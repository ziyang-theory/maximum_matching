# Independent component review

This is a historical component-review record. Its open obligations describe
that review's source snapshot; the completed solver and current validation
are recorded in [CHECKPOINT.md](CHECKPOINT.md) and [VALIDATION.md](VALIDATION.md).

Date: 2026-11-05. Scope: `Phase.lean`, `Family.lean`, `Bud.lean`, `Min.lean`, and `DDFS.lean`. Reviewed by the augmentation/optimality worker, independently of the authors of these five modules. The augmentation primitives used by Phase/Family were authored by this reviewer; this is an independent review of their composition, not an independent review of those primitives.

## Result

No confirmed correctness defect found in the inspected declarations. The source comments accurately limit the modules to supplied-path augmentation, local MIN/MAX updates, a ranked bud forest, and DDFS input/output structural facts. These modules do not implement or verify a complete MV phase. In particular, their compilation cannot establish Theorems 2.1, 6.19, 8.3, or 8.6 of the supplied paper.

All five files freshly elaborated with Lean 4.34.0 and exited 0 without warnings. `lake build MaximumMatching.Family MaximumMatching.Bud MaximumMatching.Min MaximumMatching.DDFS` also exited 0. This review did not run an independent kernel implementation or establish the final whole-project build; those are separately recorded by the coordinating agent.

## Checked correspondence

- **Phase:** `AltPath.rebase` keeps the second path's actual vertices and length and derives alternation/free endpoints after the first flip using vertex disjointness. `augmentPair` executes both flips. Its cardinality theorem proves an exact gain of two, and its free-vertex theorem identifies all four removed free endpoints. The disjointness premise is a property of the supplied paths, not an assumed correctness conclusion.
- **Family:** `AugmentingFamily.run` executes the first flip, transports every remaining path through `rebase`, and recursively consumes the family. `run_cardinality` proves an exact gain of `f.count`; it does not assume that cardinality equation or accept a matching-result oracle. Each supplied path must be augmenting against the initial matching and the family must be pairwise vertex-disjoint. No search procedure, shortest-path property, or maximal-family property is inferred from those inputs.
- **Bud:** `root` implements recursive parent chasing. `compress` redirects one vertex to its root; `compressMany_root` proves that every root is preserved by a finite sequence of such operations. The rank-decrease condition is explicit in `BudForest`; MV's petal creation has not been proved to establish it. The abstraction does not store petal bridge endpoints or the path-expansion information described on source pp.14–16. This is an implementation of the pointer-recursion portion of Definition 4.1, not the full petal data structure.
- **MIN/MAX local operations:** the source's Algorithm 1, p.13, uses `minlevel(v) ≥ i+1`; `admits` correctly retains equality, and `scan_tie_adds_predecessor` checks it. Edge marking is undirected, including the reverse-scan no-op theorem. `scanCandidate` guards adjacency, source parity/level, and edge parity. Candidate lists remain caller-supplied; no frontier enumeration or semantic label correctness has been established. `assignMax` performs natural subtraction and `assignMax_sum` correctly requires `lo ≤ t`. It does not prove support membership, ensure that condition globally, or enqueue all bridges newly exposed by MAX.
- **DDFS:** `LayeredGraph`, `ReachBottom`, and `Bottleneck` match the relevant graph-level definitions on source p.6. Path simplicity and length bounds follow from decreasing natural-number layers. Highest-bottleneck existence requires both a real root-to-bottom path and an existing bottleneck; uniqueness also retains real reachability, avoiding vacuity. Disjoint paths exclude a bottleneck, but the converse dichotomy and the DDFS machine are not proved. The ownership fixture demonstrates why irreversible greedy ownership is inadequate; it is not a counterexample to MV.

## Nonvacuity and boundary checks

An independent scratch fixture instantiated a family of two disjoint one-edge augmenting paths over an empty matching on four vertices. The family-cardinality theorem gives cardinality two, and executing its mate function produced `[some 1, some 0, some 3, some 2]`. An empty supplied family retains cardinality zero. These are instance checks, not substitutes for the universal family theorem.

A separate scratch instance set a minimum label to seven and applied `assignMax` with tenacity five. The result was zero, and seven plus zero is not five. This confirms why the theorem's `lo ≤ t` premise is material; the module does not hide truncated subtraction behind an unconditional arithmetic assertion. It is an invalid-state boundary test, not a reachable-state counterexample to MV.

The fixture and audit commands were run in `.cache/SecondReviewFixtures.lean` and `.cache/SecondReviewAudit.lean`. They are scratch review files; the public mathematical statements reside in the modules above.

## Assumption inspection

`#print axioms` reported only the following foundational axioms:

| Checked declaration | Reported axioms |
| --- | --- |
| `AugmentingFamily.run_cardinality` | `propext`, `Classical.choice`, `Quot.sound` |
| `AltPath.augmentPair_free_iff` | `propext`, `Quot.sound` |
| `BudForest.compressMany_root` | `propext`, `Quot.sound` |
| `Search.scan_reverse_noop` | `propext`, `Quot.sound` |
| `Search.scan_tie_adds_predecessor` | `propext`, `Quot.sound` |
| `Search.assignMax_sum` | `propext`, `Quot.sound` |
| `DDFS.highestBottleneck_exists` | `propext`, `Classical.choice`, `Quot.sound` |
| `DDFS.highestBottleneck_unique` | `propext`, `Quot.sound` |
| `DDFS.OwnershipExample.no_bottleneck` | `propext`, `Quot.sound` |

No `sorryAx`, custom axiom for an algorithmic claim, or native-decision axiom appeared in these reports. Paper correspondence remains a human review obligation; it is not certified by the axiom report.
