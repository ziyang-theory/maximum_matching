# Structural proof status and remaining obligations

General common-base existence and arbitrary shortest relative-path confinement
are now proved at every eligible tenacity. The minimum-tenacity unique-bridge
theorem, relative shortestness/decomposition and recursive-blossom laminarity
are also proved. Full MV correctness does not follow yet.

Source: the supplied *A Proof of the MV Matching Algorithm*,
arXiv:2012.03582v1 (7 December 2020), Theorem 6.19, PDF pp.29–33; SHA-256
`05f3cfcc51c12eea0537cb9892a9bc832f8f175fc507b2b0f8228b68e922996c`.

## Completed general induction

| Conclusion | Checked declaration | Scope |
| --- | --- | --- |
| Unique common base, Theorem 6.19(1) | `general_unique_base` | Every vertex of eligible tenacity, arbitrary vertex type; no lower/current correctness premise. |
| Relative-path confinement, Theorem 6.19(4) | `general_blossom_relative_confined` | Every shortest relative path from the actual high boundary to any member, including iterated bases. |
| Simultaneous induction | `general_base_and_confinement` | Supplies both conclusions by strong tenacity induction; current bases use minlevel induction and confinement uses path-length induction. |
| Laminarity | `blossoms_laminar` | Actual source-recursive blossoms at odd thresholds with high roots. |
| Path decomposition and joining | `blossom_shortest_relative`, `blossom_append_relative_shortest` | Exact relative lengths; joining derives simplicity rather than assuming it. |
| Same-free-root parity paths | `rooted_shortest_even_iff_odd` | Globally shortest paths at eligible endpoint tenacity. |

[GENERAL_BASE_REMAINING.md](GENERAL_BASE_REMAINING.md) explains the completed
direct induction and its checked first-intersection constructions. This proof
route closes bases and confinement without constructing the source's full `H_v`.

## Remaining general structural conclusions

The general bridge target, including the additional `t = l_m` case, is:

```lean
∀ {n : Nat} (G : Graph (Fin n)) (M : Matching G) (t : Nat),
  AtMostShortestAugmenting M t →
  ∀ p : AltPath M, p.Shortest → tenacity M p.last = some t →
  maxlevel M p.last = some p.length →
  ∃ i : Fin p.length,
    Bridge M (p.vertex ⟨i.val, by omega⟩)
      (p.vertex ⟨i.val + 1, by omega⟩) ∧
    edgeTenacity M (p.vertex ⟨i.val, by omega⟩)
      (p.vertex ⟨i.val + 1, by omega⟩) = some t ∧
    ∀ j : Fin p.length,
      Bridge M (p.vertex ⟨j.val, by omega⟩)
        (p.vertex ⟨j.val + 1, by omega⟩) →
      edgeTenacity M (p.vertex ⟨j.val, by omega⟩)
        (p.vertex ⟨j.val + 1, by omega⟩) = some t →
      j = i
```

The final equality premise is essential: a higher-tenacity maxlevel path
may also contain bridges of lower tenacity inside nested blossoms.
`AltPath.UniqueTenacityBridge`, currently used for the minimum case,
asserts uniqueness among all bridges and must not be reused unchanged
as the general statement.

The displayed bridge target was type-checked with Lean 4.34.0. No axiom or
admitted theorem has been introduced for it.


The other missing parts of Theorem 6.19 are:

- Every edge of every shortest relative path inside a blossom has edge tenacity
  at most the blossom cutoff. Vertex membership alone does not imply this bound.
- For a shortest path to a vertex of eligible tenacity, the actual base of every
  vertex after its base occurs somewhere on that path's base-to-endpoint suffix
  (Statement 5). The source does not require it to occur before that vertex.

## Weighted paths and concrete matching search

The DDFS path/bottleneck certificate, executable transition system and globally
colored parent-tree output are proved. High-core weighted paths expand into
simple alternating paths with exact summed lengths; disjoint cores give
disjoint expansions. Ordinary lower-blossom stretches and artificial low-top
segments have actual witnesses. The new general base/confinement theorems can
discharge their lower eligible-threshold premises.

Selecting the complete matching-derived layered graph and identifying its DDFS
region with actual bridge support remain construction obligations. Assigned
DDFS layers and expanded segment lengths must stay distinct, especially for
artificial top vertices. Generic path certificates and weighted concatenation
do not supply the support correspondence by themselves.

## Separate algorithm obligations

Still required are mutable petal/bud correspondence (Lemma 6.20), contracted
DDFS support discovery, complete synchronized MIN/MAX refinement (Theorem 8.3),
recursive expansion/removal of a maximal shortest augmenting-path family, and
concrete operation/data-structure costs. The generic supplied-family and
supplied-phase theorems do not construct these operations. No full MV solver
or asymptotic running-time theorem is claimed.
