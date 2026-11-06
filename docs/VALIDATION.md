# Validation and trust

The pinned environment is Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, ARM64 macOS. Lake reports `5.0.0-src+293d5d0`. The project imports Std and declares no external packages. The matching official [release](https://github.com/leanprover/lean4/releases/tag/v4.34.0) and [versioned validation documentation](https://lean-lang.org/doc/reference/4.34.0/ValidatingProofs/) were consulted when selecting the already-installed environment.

From `maximum_matching`, run:

```sh
python3 scripts/verify.py --lake /absolute/path/to/Lean-4.34.0/bin/lake
```

The script:

1. Checks the actual Lean version.
2. Takes a source/configuration snapshot, checks aggregate import coverage, and performs a supplemental lexical hygiene scan.
3. Copies the snapshot to a fresh directory under `/private/tmp`, without project build products.
4. Builds every module through the default `MaximumMatching` target.
5. Prints the main theorem types with explicit parameters, then generates `#print axioms` commands for public definitions and theorems, including all reported results. Private proof helpers are included transitively. Fails on `sorryAx` or any axiom other than `propext`, `Classical.choice`, `Quot.sound`.
6. Runs `lake env leanchecker --fresh MaximumMatching` in the source-only project.
7. Verifies that the source did not change during checking and writes exact hashes and a machine-readable result summary.

The most recent results are in [../validation/summary.json](../validation/summary.json), with the corresponding [source hashes](../validation/source-hashes.json), [fresh build log](../validation/fresh-build.log), [axiom log](../validation/axioms.log), and [kernel replay log](../validation/leanchecker.log). The empty successful kernel output is retained after its command line. Replay checks the supplied correctness and termination proof terms.

## Trust boundary

- Proof terms use ordinary Lean foundations. `propext`, `Quot.sound`, and where needed `Classical.choice` are reported explicitly. No custom mathematical axiom, admitted proof, or native-decision axiom is accepted.
- Proof examples use kernel reduction/tactics. `DDFSExecutableExamples`, `CurrentBucketCompletionExamples`, `LevelSearchExamples`, `MatchingPathRecoveryExamples`, `ShortestAugmentingExamples`, `RecursiveRemovalExamples` and `BlockingPhaseExamples` additionally use guarded compiled evaluations to exercise executable search, tree reconstruction, petal/MAX processing, actual matching-path recovery and pruning; these regression checks are separate from the universal kernel-checked correctness proofs.
- Semantic minimum levels and selected witnesses in the Berge proof use classical choice. The document distinguishes these from executable path-flip, family, bud and MIN-update functions.
- Source-only project rebuilding reuses the installed toolchain and standard-library artifacts. Bundled `leanchecker` replays with Lean's own kernel implementation. Neither step rebuilds the compiler or provides an independent second kernel.
- Lexical scanning is a hygiene check, not adversarial artifact validation. Correspondence requires reading definitions and theorem statements; the review notes record that work and their exact scopes.

## Independent checks

[INDEPENDENT_REVIEW.md](INDEPENDENT_REVIEW.md) covers paper correspondence, matching/level proofs, symmetric-difference optimality, full limited BFS honesty, structural definitions and concrete boundary cases. [SECOND_REVIEW.md](SECOND_REVIEW.md) independently checks disjoint-family execution, bud compression, MIN updates and DDFS structural facts. Each report identifies its source snapshot; later changes must be covered by the final reproducibility pass and, where substantive, a follow-up review.

[THIRD_REVIEW.md](THIRD_REVIEW.md) covers the minimum-tenacity base/bridge
proofs, source blossom recursion and laminarity, relative paths, DDFS
certificates and stack transitions, and the phase-progress proofs.

The coordinating agent additionally reviewed the final `eligible_vertex_matched`
and `matched_outer_inner` additions: the former excludes a free eligible-tenacity
vertex using the strict augmenting-length bound; the latter derives the opposite
endpoint's inner classification from the proved matched-edge level identities.
They do not assume unique bases. The final source snapshot and axiom report
include both declarations.

[ADDITIONAL_PROOFS.md](ADDITIONAL_PROOFS.md) records the independently reviewed
base-induction steps, weighted expansion, bridge classification, semantic MIN
preservation, and executable DDFS added after the third review.


The resumed search/recovery development is recorded in [CHECKPOINT.md](CHECKPOINT.md),
with its review scope in [SEARCH_RECOVERY_REVIEW.md](SEARCH_RECOVERY_REVIEW.md).
Independent reviewers checked actual bucket coverage, surviving-root MAX
exclusion, the noncircular use of exhaustion to derive the strict bound for
base restoration, and executable recovery without semantic path selection.
The subsequent blocking-family proof and its independent review scope are recorded in [BLOCKING_PHASE_PROOF.md](BLOCKING_PHASE_PROOF.md). The final reproducibility pass includes its concrete phase and solver theorems.
