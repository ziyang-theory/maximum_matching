#!/usr/bin/env python3
"""Rebuild a source-only copy, report axioms, and replay with Lean's own kernel.

Requires an installed Lean 4.34.0 toolchain. A Lake/elan shim may download a
missing toolchain; this script itself does not install dependencies.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXPECTED = "Lean (version 4.34.0,"
ACTIVE_LOGS: Path | None = None


def run(cmd: list[str], cwd: Path, log: Path) -> str:
    result = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    log.write_text("$ " + " ".join(cmd) + "\n" + result.stdout)
    if result.returncode:
        raise SystemExit(f"Failed (exit {result.returncode}); see {log}\n{result.stdout}")
    return result.stdout


def without_comments(source: str) -> str:
    """Remove nested Lean block comments and line comments for a hygiene scan."""
    out: list[str] = []
    depth = 0
    quoted = False
    i = 0
    while i < len(source):
        pair = source[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif not quoted and pair == "/-":
            depth = 1
            i += 2
        elif not quoted and pair == "--":
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        else:
            char = source[i]
            if char == '"' and (i == 0 or source[i - 1] != "\\"):
                quoted = not quoted
            out.append(char)
            i += 1
    return "".join(out)


def public_declarations(source: str) -> list[str]:
    """Only our conventional namespace layout; Lean checks every generated name."""
    stack: list[tuple[str, str]] = []
    names: list[str] = []
    for line in without_comments(source).splitlines():
        if match := re.match(r"^namespace\s+([\w.]+)\s*$", line):
            stack.append(("namespace", match[1]))
        elif match := re.match(r"^(?:noncomputable\s+)?section(?:\s+([\w.]+))?\s*$", line):
            stack.append(("section", match[1] or ""))
        elif re.match(r"^end(?:\s+[\w.]+)?\s*$", line):
            if stack:
                stack.pop()
        elif match := re.match(
            r"^(?:@\[[^]]*\]\s*)?(?:noncomputable\s+)?"
            r"(?:theorem|def|abbrev|structure|inductive)\s+([\w'.]+)", line
        ):
            namespaces = [name for kind, name in stack if kind == "namespace"]
            names.append(".".join(namespaces + [match[1]]))
    return names


def main() -> None:
    global ACTIVE_LOGS
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=shutil.which("lake"))
    args = parser.parse_args()
    logs = ROOT / "validation"
    logs.mkdir(exist_ok=True)
    ACTIVE_LOGS = logs
    (logs / "source-hashes.json").unlink(missing_ok=True)
    (logs / "summary.json").write_text(json.dumps({"status": "running"}, indent=2) + "\n")
    if not args.lake:
        parser.error("Lake not on PATH: pass --lake /absolute/path/to/Lean-4.34.0/bin/lake")
    lake = str(Path(args.lake).resolve())
    version = run([lake, "env", "lean", "--version"], ROOT, logs / "version.log")
    if EXPECTED not in version:
        raise SystemExit(f"Wrong Lean version: {version.strip()}")
    source_files = sorted([ROOT / "MaximumMatching.lean", *ROOT.glob("MaximumMatching/*.lean")])
    inputs = source_files + [ROOT / "lakefile.toml", ROOT / "lake-manifest.json", ROOT / "lean-toolchain"]
    snapshot = {path: path.read_bytes() for path in inputs}
    aggregate = snapshot[ROOT / "MaximumMatching.lean"].decode()
    for path in source_files:
        if path.parent.name == "MaximumMatching" and f"import MaximumMatching.{path.stem}\n" not in aggregate:
            raise SystemExit(f"Aggregate does not explicitly import {path.name}")
    for path in source_files:
        # Supplemental hygiene check, not a security boundary or an axiom audit.
        if re.search(r"(?m)^\s*(?:axiom|opaque)\s|\b(?:sorry|admit|native_decide)\b", without_comments(snapshot[path].decode())):
            raise SystemExit(f"Review forbidden/admitted declaration or tactic in {path}")
    names = sorted({name for path in source_files for name in public_declarations(snapshot[path].decode())})
    audit = "import MaximumMatching\n\n" + "\n".join(f"#print axioms {name}" for name in names) + "\n"
    (logs / "Axioms.lean").write_text(audit)
    key_results = [
        "AltPath.augment_cardinality",
        "Matching.twice_cardinality",
        "Matching.isMaximum_iff_noAugmentingPath",
        "AugmentingFamily.run_cardinality",
        "matched_tenacity",
        "AltPath.limited_bfs_honesty",
        "AltPath.baseOnPath_exists_of_eligible",
        "AltPath.baseOnPath_outer",
        "matched_base_values_iff",
        "rooted_shortest_even_iff_odd",
        "AltPath.minimum_unique_bridge_maxlevel",
        "AltPath.minimum_maxlevel_path_unique_bridge",
        "minimum_unique_base",
        "AltPath.parity_bases_agree_of_predecessor_ge",
        "blossom_threshold_prefix",
        "AltPath.predecessor_blossom_prefix",
        "matched_bridge_levels",
        "unmatched_bridge_tenacity",
        "blossoms_laminar",
        "minimum_blossom_relative_paths",
        "AltPath.minlevel_predecessor_honest",
        "IsBase.shortest_relative",
        "IsBase.append_relative_shortest",
        "matched_outer_minlevel",
        "DDFS.highestBottleneck_exists",
        "DDFS.highestBottleneck_unique",
        "DDFS.two_path_dichotomy",
        "DDFS.highestBottleneck_certificate",
        "DDFS.lift_path",
        "DDFS.bridge_detour",
        "DDFS.Machine.step_rank_lt",
        "DDFS.Machine.step_wellFounded",
        "DDFS.Machine.reaches_stuck",
        "DDFS.Machine.reachable_invariant",
        "DDFS.Machine.reachable_progress",
        "DDFS.Machine.exists_correct_run",
        "DDFS.Machine.maximal_trace_correct",
        "DDFS.Machine.visited_iff_on_root_to_bottleneck",
        "DDFS.BlossomWeightedMatching.realize",
        "DDFS.BlossomWeightedMatching.realize_disjoint",
        "IsBase.minimum_exit_segment",
        "IsBase.minimum_exit_reverse",
        "exists_differenceFamily",
        "AugmentingFamily.shortest_length_increases",
        "PhaseDriver.run_isMaximum",
        "BudForest.compressMany_root",
        "Search.scan_tie_adds_predecessor",
        "Search.scan_reverse_noop",
        "AltPath.minlevel_last_predecessor_honest",
        "predecessor_iff_level_guard",
        "Search.scan_assigns_semantic",
        "Search.scan_rejects_bridge",
        "Search.scanCandidates_preserves",
        "Search.initial_scanCandidates_labelsSound",
        "blossom_baseOnPath",
        "blossom_shortest_relative",
        "AltPath.disjoint_lower_boundary_reroute",
        "AltPath.base_prefix_avoids_opposite_suffix",
        "AltPath.first_lower_boundary_hit_strict",
        "AltPath.absent_lower_boundary_disjoint",
        "AltPath.high_edge_bridge_iff",
        "AltPath.high_middle_edge_tenacity",
        "AltPath.low_stretch_reverse_expansion",
        "blossom_even_top_segment",
        "DDFS.BlossomWeightedMatching.weight_add_potential",
        "DDFS.BlossomWeightedMatching.realize_disjoint_low_starts",
        "DDFS.Machine.execute_correct",
        "DDFS.Machine.reconstructTrees",
        "DDFS.Machine.executeFull",
        "DDFS.ColoredTrees.cover",
        "DDFS.ColoredTrees.overlap",
        "Search.scanLevel_complete_of_prior_levels",
        "Search.initial_scanLevel_complete",
        "Search.initial_scanLevel_classificationSound",
        "Search.assignMax_support_member",
        "Search.assignMaxList_member_correct",
        "Search.scanLevel_matched_bridge_queued",
        "Search.scanLevel_outer_bridge_queued",
        "Search.refreshIncidentAll_sound",
        "Search.refreshIncidentAll_complete",
        "Search.maxProcessVertex_correct",
        "Search.maxProcessVertex_queues_incident",
        "Search.scanLevel_current_bucket_complete",
        "Search.initial_stageInvariant",
        "Search.scanLevel_stageState",
        "Search.scanLevel_stage_bucket_complete",
        "Search.searchLevel_stageInvariant",
        "Search.maxProcessVertex_stageState",
        "Search.maxProcessVertices_member_correct",
        "Examples.DeferredBridge.max_registers_deferred_bridge",
        "Search.scanLevel_unmatchedPending",
        "Search.maxProcessVertex_unmatchedPending",
        "AltPath.low_vertex_boundary_before",
        "AltPath.blossom_member_before_high_forces_boundary",
        "DDFS.BlossomWeightedMatching.bridge_detour_of_potential",
        "ParitySegment.bridge_join",
        "general_base_and_confinement",
        "general_unique_base",
        "general_blossom_relative_confined",
        "general_unique_base_of_lower",
        "AltPath.general_parity_bases_agree",
        "AltPath.no_even_candidate_at_absent_boundary",
        "AltPath.double_reverse_boundary_bound_of_firstHit",
        "AltPath.current_blossom_suffix_mem",
        "general_blossom_relative_confined_of_current",
        "blossom_unmatched_edge_boundary_eq",
        "AltPath.first_entry_prefix_honest",
        "AltPath.exists_first_entry_confined_tail",
        "AltPath.dishonest_last_predecessor_outer",
        "AltPath.dishonest_outer_predecessor_base",
        "blossom_append_relative_shortest",
        "lower_endpoint_blossom_relative_confined",
        "blossom_low_crossing_bridge",
        "AltPath.late_low_stretch_mem",
        "general_suffix_base",
        "general_blossom_relative_base",
        "general_blossom_edge_bounds",
        "general_blossom_relative_edge_bound",
        "AltPath.general_maxlevel_path_unique_bridge",
        "AltPath.unique_bridge_maxlevel_of_lower",
        "vertex_in_bridge_support",
        "tenacity_iff_bridge_support",
        "BudForest.mergeInto_root",
        "BudForest.mergeManyInto_source",
        "DDFS.ColoredTrees.mem_vertices",
        "DDFS.Machine.executeAndContract",
        "DDFS.Machine.executeAndContract_bottleneck",
        "DDFS.Machine.FullOutput.contract_root_congr",
        "BudForest.withLabels_root",
        "BudForest.withLabels_assignedRoots",
        "BudForest.mergeManyInto_root_exact",
        "Search.initial_budGraphInvariant",
        "Search.BudGraphInvariant.edge_witness",
        "Search.BudGraphInvariant.reachBottom",
        "Search.BudGraphInvariant.root_reaches_free",
        "Search.scanLevelWithBuds_invariant",
        "Search.executeBudSearch_vertices",
        "Search.executeBudSearch_preserves",
        "Search.executeBudSearch_contracts",
        "predecessor_blossom_expansion",
        "Search.BudGraphInvariant.realize_bottom_path",
        "Search.BudGraphInvariant.bridge_top_segments",
        "Search.BudGraphInvariant.bridge_linkage_path",
        "Search.BudGraphInvariant.disjoint_bridge_paths_shortest",
        "DDFS.ColoredTrees.bottom_linkage",
        "Search.BudGraphInvariant.colored_region_support",
        "Search.BudGraphInvariant.colored_bottleneck_even",
        "Search.recordQueuedPetal_origin",
        "Search.PetalRecord.after_root",
        "Search.PetalRecord.maxEvent_correct",
        "tenacity_one_bridge_augmenting",
        "Search.uncontracted_lower_representation_one",
        "AltPath.base_eq_of_shortest_prefix",
        "AltPath.reverse_stretch_minlevel_witness",
        "DDFS.FiberWeightedMatching.realize",
        "DDFS.FiberWeightedMatching.bridge_detour_of_potential_contains",
        "Search.BudGraphInvariant.lower_blossom_fiber",
        "Search.BudGraphInvariant.fiberWeightedMatching_drop",
        "AltPath.current_bridge_prefix_honest",
        "ParitySegment.bridge_join_segment",
        "ParitySegment.bridge_join_relative",
        "DDFS.path_of_consecutive_indices",
        "DDFS.path_of_reverse_consecutive_indices",
        "DDFS.Path.map_eq_or_edge",
        "AltPath.short_shortest_no_current_bridge",
        "AltPath.maxlevel_strict_high_index_below_half",
        "Search.BudGraphInvariant.compress_early_core",
        "Search.BudGraphInvariant.compress_late_core",
        "Search.BudGraphInvariant.current_bridge_graph_arms",
        "Search.BudGraphInvariant.support_graph_arms",
        "Search.BudGraphInvariant.support_in_bottleneck_region",
        "Search.CurrentBridgeRepresentation.ofLowerBlossoms",
        "Search.PetalRecord.afterBridgeRepresentation",
        "Search.CurrentBridgeRepresentation.execute_output_sound",
        "Search.PetalRecord.maxEvent_correct_of_current",
        "Search.PetalRecord.maxEvent_representation",
        "Search.PetalRecord.transport_path",
        "Search.PetalRecord.transport_disjoint_paths",
        "Search.runCurrentBucket",
        "Search.CurrentBucketWitness.shortest_augmenting",
        "Search.runCurrentBucket_root_congr",
        "Search.runCurrentBucket_exhausted_trigger_equal",
        "Search.PetalRecord.transport_disjoint_paths_of_surviving_target",
        "Search.runCurrentBucket_exhausted_maxComplete",
        "Search.runCurrentBucket_exhausted_stageInvariant",
        "Search.runCurrentBucket_maxLabelsOffRoots",
        "Search.runCurrentBucket_exhausted_next_lower_bound",
        "Search.runCurrentBucket_exhausted_lower_representation",
        "Search.runCurrentBucket_exhausted_base_eq",
        "Search.runSearchLevel_exhausted",
        "Search.freeEdgePhase_maximalShortest",
        "Search.runLevels",
        "Search.isMaximum_iff",
        "DDFS.RootedTree.recover",
        "DDFS.FiberWeightedMatching.recoverPath",
        "Search.OperationalArms.afterMin",
        "Search.OperationalArms.afterMax",
        "Search.CurrentBucketWitness.recover",
        "Search.runRecoverableBucket_erase",
        "Search.runRecoverableBucket_history",
        "Search.findShortestAugmenting",
        "Search.ShortestAugmentingOutcome.hasPath_iff",
        "DDFS.RecursiveRemoval.mem_prune_iff",
        "DDFS.RecursiveRemoval.remove_reachBottom",
        "Search.CurrentBucketWitness.recover_coverage",
        "Search.CurrentBucketState.augmenting_bridge_arms",
        "Search.runCurrentBucket_bottom_arms",
        "Search.ActiveSearchState.initial_reach",
        "Search.ActiveSearchState.recoverLivePath",
        "Search.ActiveSearchState.LiveBridgeArms.remove_path",
        "Search.ActivePetalRecord.maxEvent_correct_of_current",
        "Search.ActivePetalRecord.afterPetal_liveBridgeArms",
        "Search.runBlockingBucket_maximalShortest",
        "Search.locateBlockingPhase",
        "Search.resumeBlockingPhase_maximalShortest",
        "Search.blockingPhase_complete",
        "Search.blockingPhase_shortestBlocking",
        "Search.runBlockingPhases_isMaximum",
        "Search.maximumMatching_isMaximum",
    ]
    statements = "import MaximumMatching\n\n" + "\n".join(
        f"#check @MaximumMatching.{name}" for name in key_results
    ) + "\n"
    (logs / "Statements.lean").write_text(statements)
    with tempfile.TemporaryDirectory(prefix="maximum-matching-check-", dir="/private/tmp") as tmp:
        fresh = Path(tmp)
        for path, content in snapshot.items():
            target = fresh / path.relative_to(ROOT)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(content)
        (fresh / "Axioms.lean").write_text(audit)
        (fresh / "Statements.lean").write_text(statements)
        run([lake, "build"], fresh, logs / "fresh-build.log")
        run([lake, "env", "lean", "Statements.lean"], fresh, logs / "statements.log")
        report = run([lake, "env", "lean", "Axioms.lean"], fresh, logs / "axioms.log")
        if "sorryAx" in report:
            raise SystemExit("An audited declaration depends on sorryAx")
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        found = set()
        for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", report, re.S):
            found.update(item.strip() for item in group.split(",") if item.strip())
        if found - allowed:
            raise SystemExit(f"Unreviewed axioms: {sorted(found - allowed)}")
        run([lake, "env", "leanchecker", "--fresh", "MaximumMatching"], fresh,
            logs / "leanchecker.log")
    if any(path.read_bytes() != content for path, content in snapshot.items()):
        raise SystemExit("Source changed during validation; rerun on the final snapshot")
    if sorted(ROOT.glob("MaximumMatching/*.lean")) != sorted(p for p in source_files if p.parent.name == "MaximumMatching"):
        raise SystemExit("Module list changed during validation; update aggregate and rerun")
    manifest = {str(path.relative_to(ROOT)): hashlib.sha256(content).hexdigest()
                for path, content in snapshot.items()}
    (logs / "source-hashes.json").write_text(json.dumps(manifest, indent=2) + "\n")
    (logs / "summary.json").write_text(json.dumps({
        "status": "passed",
        "lean_version": version.strip(),
        "public_declarations_audited": len(names),
        "axioms": sorted(found),
        "fresh_project_build": "passed",
        "bundled_kernel_replay": "passed",
        "blocking_phase_correctness": "passed",
        "maximum_matching_correctness": "passed",
        "scope": "functional_correctness_and_termination",
    }, indent=2) + "\n")
    print(f"Fresh build and kernel replay passed; audited {len(names)} declarations.")
    print("Functional correctness and termination checks passed.")


if __name__ == "__main__":
    try:
        main()
    except (Exception, KeyboardInterrupt, SystemExit) as error:
        if ACTIVE_LOGS is not None:
            (ACTIVE_LOGS / "source-hashes.json").unlink(missing_ok=True)
            (ACTIVE_LOGS / "summary.json").write_text(json.dumps({
                "status": "failed",
                "error": f"{type(error).__name__}: {error}",
            }, indent=2) + "\n")
        raise
