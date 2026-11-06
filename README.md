# Maximum matching in Lean 4

This project implements a maximum-cardinality matching algorithm and proves its
correctness and termination in Lean 4. Given a finite simple graph, it computes
a largest set of edges with no shared endpoints.

The development follows Vijay V. Vazirani's
[*A Proof of the MV Matching Algorithm*](https://arxiv.org/abs/2012.03582v1)
(7 December 2020). It includes alternating paths, blossom structure, double
depth-first search (DDFS), and the MIN/MAX search for augmenting paths. Each
nonempty phase finds a maximal family of vertex-disjoint shortest augmenting
paths and uses them to enlarge the matching.

## Main result

`Search.maximumMatching G` computes the matching, and
`Search.maximumMatching_isMaximum G` proves that no matching in `G` has more
edges. The solver accepts an undirected graph on `Fin n` with decidable adjacency,
without loops or parallel edges.

```lean
import MaximumMatching

open MaximumMatching

example {n : Nat} (G : Graph (Fin n)) [DecidableRel G.Adj] :
    (Search.maximumMatching G).IsMaximum :=
  Search.maximumMatching_isMaximum G
```

The proof includes Berge's criterion, correctness of augmentation, the base and
blossom theorems, and completeness of the concrete search. Callers do not need
to supply a search-completeness assumption.

The scope is correctness and termination; time and space bounds are not proved.
During a blocking phase, deletion removes whole groups of vertices with the same
bud. Safety and maximality are proved for this representation, without claiming
identical intermediate states to the paper's vertex-deletion procedure.

## Build and check

The project uses Lean **4.34.0** and its standard library (`Std`), with no external
Lean packages. With the pinned toolchain installed, run:

```sh
lake build
python3 scripts/verify.py --lake "$(command -v lake)"
lake env lean tests/IndependentChecks.lean
```

The verifier builds a fresh copy, checks theorem statements and axiom dependencies,
and replays the proofs with the bundled Lean kernel. It accepts only `propext`,
`Classical.choice`, and `Quot.sound`. Admitted proofs and custom axioms fail the
check. Reports and source hashes are generated locally in `validation/`.
Kernel replay uses Lean's own implementation, not a second independent checker.

The separate runtime test compares the solver with a brute-force matching
algorithm on all 1,100 simple graphs with up to five vertices. Examples in the
library also exercise blossoms, path recovery, and deletion.

## Where to start

[`MaximumMatching.lean`](MaximumMatching.lean) imports the whole library.
The modules in [`MaximumMatching/`](MaximumMatching/) are grouped by topic:

| Modules | Contents |
| --- | --- |
| `Foundations`, `Optimality`, `PhaseDriver` | Matchings, path augmentation, Berge's criterion, and the outer solver loop. |
| `Levels`, `Structure`, `Base*`, `BlossomStructure`, `General*` | Levels, bases, and blossom proofs. |
| `RelativePaths`, `WeightedPaths`, `WeightedRecovery` | Paths through blossoms and their expansion. |
| `DDFS*`, `BudForest` | The search machine, its invariants, and contraction. |
| `Min*`, `BridgeBuckets`, `MaxBridgeRefresh`, `SearchStage` | Level discovery, bridge queues, and MIN/MAX updates. |
| `Matching*`, `Current*`, `Petal*`, `Operational*`, `Support*` | Search through contracted graphs, support discovery, and path recovery. |
| `Active*`, `ShortestAugmentingSearch`, `BlockingPhase` | Search after deletion, blocking phases, and the complete solver. |
| `FoundationExamples`, `DDFSExamples`, `SearchExamples` | Concrete proof and runtime examples. |

Start with [`Foundations.lean`](MaximumMatching/Foundations.lean) for the
definitions, or [`BlockingPhase.lean`](MaximumMatching/BlockingPhase.lean) for
the solver and its final correctness theorem. The independent exhaustive test
is in [`tests/`](tests/), and [`scripts/verify.py`](scripts/verify.py) runs the
proof audit.

## License

Released under the [MIT License](LICENSE).
