# The checked DDFS path certificate

Source: the supplied *A Proof of the MV Matching Algorithm*, arXiv:2012.03582v1,
7 December 2020, §2 pp.6–8 and Lemma 6.13 Claim 4 p.25. The PDF hash is recorded
in SOURCE_MAP.md. The proof below supplies the graph-theoretic witnesses used
by Claim 4. It does not verify the operational two-search procedure.

## Dichotomy

`DDFS.two_path_dichotomy` works in any directed graph whose natural-number
layer strictly decreases on every edge. Given a terminal predicate `T` and
an actual path from each of `r,g` to `T`, it proves either:

- two vertex-disjoint paths, one from each root to `T`; or
- a vertex occurring on every path from either root to `T`.

The argument is internal to this project; it does not assume Menger's theorem.
It inducts on `level(r)+level(g)`. Equal roots give an immediate common
dominator. Otherwise, take `r` to have the higher layer. If `r` is terminal,
its trivial path is disjoint from a terminal path from `g` by layer descent.
For each reachable successor `x` of `r`, apply the induction hypothesis to
`x,g`. Disjoint paths extend through `r`, again using layer separation.

If every successor instead gives a common dominator, choose one of minimum
layer. All these dominators occur on one fixed terminal path from `g`.
The lower chosen dominator also dominates every terminal continuation from
each higher dominator: splice such a continuation to the fixed path's prefix.
Consequently the chosen vertex dominates every terminal path from `r` and
from `g`. Existence of a minimum natural-number layer does not require a
finite vertex type or a finite list of successors.

`DDFS.bottom_dichotomy` specializes to layer-zero terminals and selects a
highest bottleneck in the second case. Equal roots, roots at layer zero,
and zero-edge paths are included.

## Per-vertex certificate

`DDFS.highestBottleneck_certificate` assumes a highest bottleneck `b`,
root-to-bottom reachability, and a path from either root to a vertex `w`
strictly above `b`. It constructs one of the two linkages:

```text
r → w and g → b, vertex-disjoint
g → w and r → b, vertex-disjoint
```

Apply the dichotomy to the terminal set `{w,b}`. If a common dominator `c`
existed, truncating all original bottom paths at `b` would make `c` an
original bottleneck, so `level(c) ≤ level(b)`. But `c` must also occur on
the given path ending at `w`, so `level(w) ≤ level(c)`. This contradicts
`level(b) < level(w)`. The resulting disjoint terminal paths have different
endpoints, giving the required linkage.

The orientation can depend on `w`. This theorem does not assert that one
operational search computes a globally consistent coloring or two spanning
search trees.

## Actual alternating paths

`DDFS.LayeredMatching` states three compatibility facts about the directed
input graph: its edges are graph edges, lower the level by exactly one,
and have the matching parity dictated by the lower level.

`DDFS.lift_path` joins an actual level-honest alternating prefix ending at
`b` to the reversal of a directed path ending at `b`. All newly appended
vertices have higher levels than the prefix vertices. The proof derives
simplicity and alternation and records exact vertex membership.

`DDFS.bridge_detour` then combines a prefix to `b`, the reversed `g→b`
certificate path, the triggering bridge `(g,r)`, and the `r→w` certificate
path. Disjointness and level separation prove simplicity. When both bridge
endpoints have level `α`, the constructed alternating path has length
`2α+1-level(w)`. These compatibility facts must be established for the
particular matching-layer graph; they are not assumed MV correctness.

## Operational obligation

These existence theorems are separate from the operational proof now recorded
in [DDFS_OPERATIONAL_PROOF.md](DDFS_OPERATIONAL_PROOF.md). The stack transition
system has checked coverage, collision/Barrier recovery, progress, finite
termination and correct path/bottleneck outcomes. Its remaining globally
colored tree output and executable representation/cost refinement are
listed in [DDFS_OBLIGATIONS.md](DDFS_OBLIGATIONS.md). Mathematical choice in
the existence proof is not an efficient search implementation.
