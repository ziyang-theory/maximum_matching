# Structural proof status and remaining obligations

All structural conclusions of Theorem 6.19 are now proved: common bases,
unique same-tenacity bridges, laminarity, relative-path decomposition and
confinement, relative edge-tenacity bounds, and the suffix-base property.
The bridge theorem also covers `t = l_m`. Full MV correctness does not follow yet.

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

## General bridge, relative edges and suffix bases

`AltPath.general_maxlevel_path_unique_bridge` proves the general bridge result
for arbitrary vertex types with premises `AtMostShortestAugmenting M t`, endpoint
tenacity `t`, and `maxlevel M p.last = some p.length`. Shortestness is derived.
Its conclusion `p.UniqueBridgeOfTenacity t` says exactly one path edge is both
a bridge and of tenacity `t`. Lower-tenacity bridges may also occur. The older
minimum-case `UniqueTenacityBridge` asserts uniqueness among all bridges and
is deliberately kept separate.

`general_blossom_relative_edge_bound` proves every edge of every shortest
relative path has tenacity at most the eligible blossom cutoff. This uses an
additional edge argument; vertex membership alone is insufficient.

`general_suffix_base` proves that the actual base of every vertex after the
path's base occurs somewhere on that original base-to-endpoint suffix.
It need not occur before the chosen vertex. `general_blossom_relative_base`
provides the companion result for arbitrary shortest relative paths.

The public theorems have no unproved structural oracle premises. Strong cutoff
induction supplies the lower-blossom statements; the bridge proof only needs
cutoffs strictly below `t`, preserving the equality case `t = l_m`.
`tenacity_iff_bridge_support` then identifies the current vertex-tenacity
stratum with the union of the corresponding semantic bridge supports.
Supports may overlap; this is not a claim about computing them by DDFS.

## Weighted paths and concrete matching search

The DDFS path/bottleneck certificate, executable transition system and globally
colored parent-tree output are proved. High-core weighted paths expand into
simple alternating paths with exact summed lengths; disjoint cores give
disjoint expansions. Ordinary lower-blossom stretches and artificial low-top
segments have actual witnesses. The new general base/confinement theorems can
discharge their lower eligible-threshold premises.

The executable `DDFSBud.executeAndContract` now merges the computed bottleneck
region under explicit fixed-root/rank representation. Selecting the complete
matching-derived layered graph and identifying its DDFS region with actual
bridge support remain construction obligations. Assigned
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
