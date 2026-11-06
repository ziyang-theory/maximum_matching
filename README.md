# Maximum matching in Lean 4

**Partial formalization of the Micali–Vazirani algorithm. Full MV correctness and its running-time bound are not yet proved.** The checked development contains the matching foundations and limited BFS-honesty theorem, plus local algorithm components. It does not contain a complete MV solver.

Source: Vijay V. Vazirani, *A Proof of the MV Matching Algorithm*, [arXiv:2012.03582v1](https://arxiv.org/abs/2012.03582v1), 7 December 2020; supplied as [max_matching.pdf](max_matching.pdf). The exact version and claim map are recorded in [docs/SOURCE_MAP.md](docs/SOURCE_MAP.md).

## Checked results

| Result | Main declaration |
| --- | --- |
| Executable augmentation preserves matching validity and adds exactly one edge | `AltPath.augment`, `AltPath.augment_cardinality` |
| Matching cardinality is half an even saturated-vertex count | `Matching.twice_cardinality` |
| Maximum matching iff no augmenting path (Berge criterion) | `Matching.isMaximum_iff_noAugmentingPath` |
| Execute a supplied disjoint family, gaining exactly its number of paths | `AugmentingFamily.run_cardinality` |
| Matched endpoints have equal tenacity, including infinity (Lemma 5.2) | `matched_tenacity` |
| Both conclusions of limited BFS honesty, all parity/infinity cases (Theorem 5.3) | `AltPath.limited_bfs_honesty` |
| Layered-path simplicity and highest-bottleneck existence/uniqueness | `DDFS.Path.injective`, `DDFS.highestBottleneck_exists`, `DDFS.highestBottleneck_unique` |
| Bud lookup terminates; compression preserves roots under a rank invariant | `BudForest.root`, `BudForest.compressMany_root` |
| MIN scans retain tied predecessors and never rescan an undirected edge | `Search.scan_tie_adds_predecessor`, `Search.scan_reverse_noop` |

The missing dependencies include the concrete DDFS machine and its coverage invariant; unique bases, recursive blossoms and Theorem 6.19; the complete MIN/MAX phase, support discovery, path expansion and removal; and the phase-count/cost proofs. [docs/STATUS.md](docs/STATUS.md) separates these from completed results. No unproved MV lemma is installed as an axiom or hidden behind an algorithm-correctness parameter.

## Build and check

The project pins **Lean 4.34.0**, imports **Std only**, and has no external package dependencies. With that toolchain installed:

```sh
lake build
python3 scripts/verify.py --lake "$(command -v lake)"
```

In this workspace, the existing concrete toolchain can be used directly:

```sh
python3 scripts/verify.py --lake \
  /Users/ziyang/Documents/github/formal_verification/formal_verification_skills/.cache/lean-4.34.0-darwin_aarch64/bin/lake
```

The verification script copies source/configuration into a fresh temporary directory, builds the aggregate target, reports transitive axioms for public declarations, and runs `leanchecker --fresh MaximumMatching`. Logs and exact source hashes are retained in [validation/](validation/). Kernel replay uses Lean's own kernel and the installed standard-library artifacts; it is not a second independent kernel or a rebuilt toolchain. See [docs/VALIDATION.md](docs/VALIDATION.md).

## Project structure

- `Basic`, `PathLemmas`, `Augmentation`, `Phase`, `Family`: graph/matching representation and actual path operations.
- `SymmetricDifference`, `DifferenceUniqueness`, `Optimality`: complete Berge proof.
- `Levels`, `Honesty`, `Splice`, `Structure`, `LimitedHonesty`, `Base`: semantic levels and structural path arguments.
- `Bud`, `Min`, `DDFS`: verified data-structure/local-update components and DDFS graph-theoretic specification.
- `Examples`: small kernel-checked examples, including an invalid alternating-walk shortcut on a triangle.
- `docs/`: original step plan, source correspondence, remaining obligations and independent reviews.

Semantic levels use `none` for infinity and mathematical choice to select minima; they are specifications, not the operational MIN/MAX implementation. Augmentation, disjoint-family execution, bud lookup/compression and local MIN updates are executable. General definitions allow any vertex type; cardinality and the Berge criterion use `Fin n`. Loops and parallel edges are excluded; no normalization theorem for multigraphs is claimed.
