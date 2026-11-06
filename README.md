# Maximum matching in Lean 4

An executable maximum-matching algorithm with proved correctness and termination,
using MIN/MAX search, double depth-first search (DDFS), petal expansion, and
deletion-aware maximal blocking phases.

For every finite simple graph with decidable adjacency,
`Search.maximumMatching_isMaximum` proves that `Search.maximumMatching` returns
a maximum-cardinality matching. The concrete phase satisfies both `Complete`
and `ShortestBlocking`; these are proved results, not assumptions supplied to
the solver. This repository covers correctness and termination, not running-time
or space-complexity bounds.

Source: Vijay V. Vazirani, *A Proof of the MV Matching Algorithm*,
[arXiv:2012.03582v1](https://arxiv.org/abs/2012.03582v1), 7 December 2020;
supplied as [max_matching.pdf](max_matching.pdf). The exact source, theorem
correspondence, and representation choices are in [docs/SOURCE_MAP.md](docs/SOURCE_MAP.md).

## Main results

| Result | Declaration |
| --- | --- |
| Augmentation preserves matching validity and increases cardinality by one | `AltPath.augment_cardinality` |
| Maximum matching iff no augmenting path | `Matching.isMaximum_iff_noAugmentingPath` |
| Correct, terminating DDFS with disjoint paths or a highest bottleneck | `DDFS.Machine.execute_correct`, `executeFull` |
| General base, blossom, and unique-bridge structure | `general_unique_base`, `general_blossom_relative_confined`, `AltPath.general_maxlevel_path_unique_bridge` |
| Computed shortest augmenting path or certified absence | `Search.findShortestAugmenting` |
| Safe deletion and maximal shortest-path family | `Search.resumeBlockingPhase_maximalShortest` |
| Complete concrete phase and maximum-matching solver | `Search.blockingPhase_complete`, `blockingPhase_shortestBlocking`, `maximumMatching_isMaximum` |

The live search removes whole touched bud fibers. Its safety and maximality
are proved; exact intermediate-state equivalence to literal source vertex
deletion is not claimed. See [docs/BLOCKING_PHASE_PROOF.md](docs/BLOCKING_PHASE_PROOF.md)
and [docs/STATUS.md](docs/STATUS.md) for the precise scope.

## Build and verify

The project pins **Lean 4.34.0**, imports **Std only**, and has no external
package dependencies.

```sh
lake build
python3 scripts/verify.py --lake "$(command -v lake)"
```

The verification script rebuilds a source-only copy, checks theorem statements
and transitive axioms, and replays the bundled Lean kernel. It rejects admitted
proofs and custom axioms. Results and exact source hashes are in
[validation/](validation/); the trust boundary is in [docs/VALIDATION.md](docs/VALIDATION.md).

## Project structure

- `Basic`, `PathLemmas`, `Augmentation`, `Family`, `Optimality`: matching/path foundations, actual flips, and the Berge criterion.
- `Levels`, `Minimum*`, `General*`, `Blossom*`: semantic levels, bases, blossom structure, and path geometry.
- `DDFS*`: search transitions, invariants, termination, path/bottleneck correctness, and stored search trees.
- `Min*`, `Max*`, `CurrentBucket*`, `Operational*`, `Petal*`: actual MIN/MAX search and computed path expansion.
- `Active*`, `BlockingBucket*`, `BlockingPhase*`, `PhaseDriver`: safe deletion, maximal blocking phases, and the complete solver.
- `docs/`: source correspondence, proof explanations, review notes, and the completed [checkpoint](docs/CHECKPOINT.md).

General definitions allow arbitrary vertex types; finite cardinality and solver
statements use `Fin n`. Graphs exclude loops and parallel edges. Semantic levels
use `none` for infinity and mathematical choice for specifications; runtime
search and path recovery use computed data.
