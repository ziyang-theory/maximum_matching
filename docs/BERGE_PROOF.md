# Augmentation and Berge's criterion

Status: checked in Lean 4.34.0, using Std only. This is a completed prerequisite for MV correctness, not a proof of the MV search procedure.

## Formal statements

For every natural `n`, simple undirected graph `G : Graph (Fin n)`, and matching `M : Matching G`:

- `Matching.matchedCount_even`: the number of saturated vertices is even.
- `Matching.twice_cardinality`: `2 * M.cardinality = M.matchedCount`.
- `Matching.cardinality_le`: `M.cardinality ≤ n / 2`.
- `AltPath.augment_free_iff`: augmenting along a simple alternating path with odd length and free endpoints removes exactly those endpoints from the free-vertex set.
- `AltPath.augment_path_edge`: augmentation matches precisely the even-indexed path edges, reversing their original matched/unmatched status.
- `AltPath.augment_off_path`: mates of vertices outside the path do not change.
- `AltPath.augment_cardinality`: an augmentation increases cardinality by exactly one.
- `Matching.isMaximum_iff_noAugmentingPath`: maximum cardinality is equivalent to absence of augmenting paths.
- `Matching.larger_has_augmentingPath`: any larger matching implies an augmenting path exists.

`IsMaximum` quantifies over all matchings of the same graph. No bipartiteness or maximality premise appears. `AltPath` is vertex-simple, starts at a free vertex, and uses unmatched edges at even edge indices and matched edges at odd indices. `Augmenting` additionally requires odd length and a free last vertex. The first and last vertices are then provably distinct.

## Proof route

The executable augmentation function scans the finite path-index list to locate a vertex and pairs indices `(0,1), (2,3), ...`. Mates outside the path remain unchanged. Matching validity follows from the index involution, graph adjacency, and the fact that every old matching edge incident to the path stays on the path. Internal path vertices were already matched; both endpoints become matched. Counting them gives the exact cardinality increment.

For the converse of Berge's criterion, compare `M` with an arbitrary matching `N`. A `DifferencePath M N` is an `M`-alternating path whose even-indexed edges belong to `N`. The construction alternates the unique `N` and `M` neighbors. Uniqueness of mates proves both extensions preserve vertex simplicity. The path has fewer than `n` edges, so the measure `n - path.length` proves termination.

Assuming there is no `M`-augmenting path, every vertex free in `M` and matched in `N` reaches an even-length terminal path whose last vertex is free in `N` and matched in `M`. Reversing the two alternating matchings proves that paths with the same even terminal vertex have the same initial vertex. Thus the construction gives an injection from the first excess-vertex set to the second. A direct count identity then proves `N.cardinality ≤ M.cardinality`.

This is an internal derivation. The existence, termination, endpoint-injection, and counting statements are proved rather than supplied as theorem hypotheses. Classical choice selects witnesses inside the counting proof; it does not implement the MV augmenting-path search.

## Source correspondence and limits

The supplied paper, *A Proof of the MV Matching Algorithm*, arXiv:2012.03582v1 (December 7, 2020), Section 4, physical PDF page 11, uses the equivalence between no augmenting path and maximum cardinality. The development proves that equivalence independently for the graph representation used here. It also supplies the path-flipping fact used by the paper's phases.

The Berge criterion alone does not show that MIN/MAX/DDFS finds a shortest augmenting path or that the phase finds a maximal vertex-disjoint family. These properties are proved separately in `ShortestAugmentingSearch` and `BlockingPhase`.

## Trust and checks

Fresh direct elaboration of `Augmentation.lean`, `SymmetricDifference.lean`, and `Optimality.lean` succeeded without warnings. The endpoint-uniqueness module was independently implemented by the coordinating agent. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for the final cardinality and Berge theorems; some helper theorems use a subset. No `sorryAx`, custom mathematical axiom, or native-decision axiom occurs in those reports. Full project rebuild and final kernel replay are recorded by the coordinating agent separately.
