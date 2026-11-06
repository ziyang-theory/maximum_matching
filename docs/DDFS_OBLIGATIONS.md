# DDFS operational obligations

Source: `max_matching.pdf`, SHA-256 `05f3cfcc51c12eea0537cb9892a9bc832f8f175fc507b2b0f8228b68e922996c`, §2, pp.6–8. This note concerns reconstructing operational details and invariants. It is not a counterexample to the MV algorithm or to Theorem 2.1.

## A literal ordinary-DFS translation gets stuck

The normal-DFS paragraph on p.7 says to skip an already visited successor. The collision paragraph then describes both activity centers meeting and transfers ownership. The collision handling must override the visited-successor skip; otherwise that event is unreachable when visiting a vertex immediately marks it visited.

The smallest example with two distinct roots and a common lower vertex has three vertices:

```text
level 1: r       g
          \     /
level 0:     b
```

Edges are `r → b` and `g → b`. All vertices reach level zero. The scheduling rule first moves red from `r` to `b`, marking `b` red. Green then scans `g → b`. If it literally skips every visited successor, it exhausts the green root without ever entering the collision branch. An ordinary “backtrack to parent” operation has no parent there. The correct result is the highest bottleneck `b`.

This is a reproducible obstruction to that naive translation, not evidence of a false graph-theoretic claim. The paper expressly announces an exception to normal DFS before giving collision handling; the implementation must make this exception precise.

## Recoloring is necessary, not just collision detection

Use vertices `r,g,s,a,b`, layers `2,2,1,0,0`, and edges:

```text
r → s       g → s
r → a       s → b
```

Starting with red's edge `r → s`, the next green step reaches the red activity center `s`. Two vertex-disjoint root-to-bottom paths nevertheless exist: `r → a` and `g → s → b`. Thus `s` must not be declared a bottleneck merely because green's only outgoing edge reaches a red vertex. Red can relinquish `s` and find the alternative edge `r → a`.

This graph is implemented in `MaximumMatching/DDFS.lean`, namespace `OwnershipExample`. Lean checks:

- `reaches_bottom`: every vertex reaches layer zero.
- `solutions_disjoint`: the two displayed solution paths share no vertex.
- `no_bottleneck`: no vertex is a bottleneck for these roots.
- `green_successors_owned`: every available green successor is already on red's collision prefix `r → s`.

These statements separate a real allowed graph from an imagined failing tactic. They do not certify an implementation of DDFS. The three-vertex stuck trace above is a direct hand execution of the explicitly described naive transition rule; the five-vertex structural facts are machine-checked.

## Operational resolution to implement

When scanning an outgoing edge to the other current activity center, process a collision before the generic visited-edge skip. Suspend ordinary moves at the collision vertex, tentatively assign it to green, and search for a red alternative at least as deep. If red exhausts its allowed prefix down to its current Barrier, transfer the collision vertex to red, move the Barrier to that vertex, and try the green alternative. The machine must record enough parent/ownership history to restore rooted paths after these transfers. Distinguish vertices visited earlier but no longer current from the other active center; treating all visited vertices as interchangeable loses precisely the information needed by these rules.

The source's English rules determine the intended behavior, but a faithful Lean transition system still needs explicit definitions for collision modes, suspended centers, parent updates, and the root/Barrier exhaustion cases. These choices must be checked against the source before a correctness theorem about the machine is meaningful.

## Exact invariant that remains to be established

A useful proof needs more than “both colors form rooted trees.” During collision recovery, a formerly owned vertex is reassigned, so naive permanently-disjoint parent maps do not remain invariant. The required invariant should express all of the following for reachable machine states:

1. Active root-to-center chains follow graph edges and are vertex-disjoint except at the currently suspended collision vertex. Every off-chain colored vertex retains valid discovery provenance in its current search forest.
2. Each explored edge belongs to exactly one recorded exploration event. When an edge is skipped, its destination is either covered by an already justified search region or handled by the collision-recovery obligation; “visited” alone is insufficient evidence of coverage.
3. Exhaustion of red's allowed search above the current Barrier proves that every remaining red escape to the collision depth intersects the region assigned to green. The analogous green exhaustion then upgrades the collision vertex to a universal root-to-bottom bottleneck. This is the completeness step; local tree validity cannot imply it.
4. When an alternative is found, ownership/parent updates preserve the two active chains and all coverage obligations. When both alternatives are exhausted, the reported bottleneck is the highest one, not merely some common reachable vertex.
5. Barrier moves only to strictly lower layers on each relevant update. Together with edge-exploration uniqueness and bounded backtracking this yields termination and the source's local linear work accounting; a fuel bound chosen without this proof would not establish the claimed complexity.

The currently checked `Path.level_drop`, path simplicity, highest-bottleneck existence/uniqueness, and disjoint-path exclusion lemmas supply structural ingredients. They do **not** establish items 1–5. The unresolved next step is a concrete collision/recovery transition relation with a coverage invariant strong enough for item 3. No theorem in this development assumes that invariant as if it had already been proved for MV.
