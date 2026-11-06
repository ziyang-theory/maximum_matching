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
    stack: list[str] = []
    names: list[str] = []
    for line in source.splitlines():
        if match := re.match(r"^namespace\s+([\w.]+)\s*$", line):
            stack.append(match[1])
        elif re.match(r"^end(?:\s+[\w.]+)?\s*$", line):
            if stack:
                stack.pop()
        elif match := re.match(
            r"^(?:@\[[^]]*\]\s*)?(?:noncomputable\s+)?"
            r"(?:theorem|def|abbrev|structure|inductive)\s+([\w'.]+)", line
        ):
            names.append(".".join(stack + [match[1]]))
    return names


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=shutil.which("lake"))
    args = parser.parse_args()
    if not args.lake:
        parser.error("Lake not on PATH: pass --lake /absolute/path/to/Lean-4.34.0/bin/lake")
    lake = str(Path(args.lake).resolve())
    logs = ROOT / "validation"
    logs.mkdir(exist_ok=True)
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
        "DDFS.highestBottleneck_exists",
        "DDFS.highestBottleneck_unique",
        "BudForest.compressMany_root",
        "Search.scan_tie_adds_predecessor",
        "Search.scan_reverse_noop",
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
        "lean_version": version.strip(),
        "public_declarations_audited": len(names),
        "axioms": sorted(found),
        "fresh_project_build": "passed",
        "bundled_kernel_replay": "passed",
        "complete_mv_verification": False,
    }, indent=2) + "\n")
    print(f"Fresh build and kernel replay passed; audited {len(names)} declarations.")
    print("This checks the supplied development, not the missing full MV algorithm.")


if __name__ == "__main__":
    main()
