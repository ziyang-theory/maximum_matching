# Source map and proof obligations

This document records the requested target, not a claim that the whole target has been proved. The source is Vijay V. Vazirani, *A Proof of the MV Matching Algorithm*, arXiv:2012.03582v1, 7 December 2020. The supplied `max_matching.pdf` has 43 physical pages, whose printed page numbers agree with physical page numbers. SHA-256:

```text
05f3cfcc51c12eea0537cb9892a9bc832f8f175fc507b2b0f8228b68e922996c
```

The local paper-library index was consulted first; its targeted matching search did not identify this paper. This map uses the supplied version. It does not adopt the paper's 2020 priority or fastest-known-algorithm assertions as current claims. Text extraction covered all pages; the algorithm, definitions, and main proof passages below were read. Rendered pages 16, 29, and 37 were additionally inspected where notation or apparent typographical problems mattered.

## Intended theorem and representation

For every finite undirected graph `G`, the executable MV procedure, started with the empty matching, terminates with a matching `M` such that every matching `N` in `G` satisfies `|N| ≤ |M|`. This is the functional-correctness part of Theorem 8.6 (p.40). A formalization of a generic augmenting-path loop, or an exhaustive matching enumeration, does not by itself establish this theorem about MV.

A finite simple-graph representation is a natural formalization choice. The source says “undirected graph”; if a future development admits loops or parallel edges, either use appropriate semantics or prove a normalization theorem. Path means **simple path**, not arbitrary alternating walk (p.8). A path's length counts edges. Levels and tenacities take values in the natural numbers extended by infinity; unavailable paths must not silently receive level zero. A length-zero path at an unmatched vertex gives evenlevel zero, but is not an augmenting path.

The asymptotic part of Theorem 8.6 is a separate target: RAM time `O(m sqrt(n))`, or pointer-model time `O(m sqrt(n) alpha(m,n))`. A functional Lean definition has no such cost bound merely because it terminates. The paper imports phase-count and disjoint-set data-structure results for this claim.

## Definitions and their source locators

| Paper object | Locator | Required meaning |
| --- | --- | --- |
| Matching, alternating path, augmentation | §3, p.8 | Matching edges are graph edges with no common endpoint. Alternating paths are simple; augmentation flips membership along a nonempty path joining distinct unmatched endpoints. |
| `l_m` | Notation 3.1, p.8 | Shortest augmenting-path length; infinity if none exists. |
| evenlevel, oddlevel | Definition 3.2, pp.8–9 | Minimum length among alternating simple paths from any unmatched vertex with the stated parity, or infinity. |
| minlevel, maxlevel, outer/inner | Definitions 3.3–3.4, p.9 | Min/max of the two parity levels. Classification requires finite minlevel. |
| vertex/edge tenacity | Definition 3.6, p.10 | Vertex: sum of parity levels. Unmatched edge: sum of endpoint evenlevels plus one. Matched edge: sum of endpoint oddlevels plus one. |
| predecessor, prop, bridge | Definition 3.8, p.10 | A predecessor is the penultimate vertex of a minlevel path. Props are corresponding last edges; other graph edges are bridges. |
| bridge support | Definition 3.9, p.10 | For bridge `e` of tenacity `t ≤ l_m`, vertices of tenacity `t` with a maxlevel path containing `e`. |
| petal, bud, `bud*` | §4.2, pp.14–15 | Runtime, order-dependent objects. A new petal contains newly discovered support vertices, excluding its bud; `bud*` follows the currently installed bud links. |
| eligible tenacity | Definition 6.1, p.20 | Odd finite `t`, with `t_m ≤ t < l_m`. Strict upper bound is essential. |
| path-dependent base, unique base | Definitions 6.2–6.6, p.21 | Last vertex of tenacity greater than `t` on a minimum parity path; uniqueness is a theorem, not a field assumed in the input. |
| blossom | Definition 6.8, p.22 | Recursive union of same-base vertices of tenacity `t` and lower-tenacity blossoms; excludes the base itself. |

## Operational correspondence

The paper gives a mixture of pseudocode, English operational rules, and examples. The following components together specify MV; Algorithm 1 alone leaves its hardest subroutines abstract.

| Component | Source | State and operations that must be represented |
| --- | --- | --- |
| Outer loop | §4, p.11 | Empty initial matching; repeatedly find a maximal family of vertex-disjoint shortest augmenting paths and flip all their edges. Stop only when no augmenting path exists. |
| Phase initialization | §4.1, p.11 | Unmatched vertices get minlevel zero; other vertices initially have unknown/infinite minlevel; no maxlevels assigned. |
| MIN | Algorithm 1, p.13; explanation pp.12–14 | Search vertices with the parity level `i`; traverse unmatched edges for even `i`, matched edges for odd `i`; scan each edge once; assign minlevel/predecessors/props, otherwise classify bridges and enqueue known tenacities. Multiple predecessors must survive ties at the same search level. |
| MAX scheduling | Algorithm 1, p.13; pp.39–40 | Process exactly bridges of tenacity `2i+1` after MIN at level `i`; newly obtained evenlevels can reveal further bridge tenacities. Processing a bridge as soon as its tenacity becomes known is not equivalent. Figures 23–24 exhibit why. |
| DDFS | §2, pp.5–8 | Two DFS trees; current centers; visited colors and parent links; explored-edge flags; ownership transfer at collisions; red `Barrier` limiting repeated backtracking. Roots may have unequal levels; edges may skip layers. |
| DDFS implicit input graph | §4.3, p.16 | Start at `bud*(r)` and `bud*(g)` for the triggering bridge. From `v`, follow each predecessor `u` to `bud*(u)`. Labels are minlevels. Prove decreasing levels and reachability to level zero. The algorithm works on `G` without materializing `H`. |
| New petal | §4.2, pp.14–15 | On the bottleneck outcome, record newly found support vertices, the bud, both bridge endpoints, and search-tree information needed for later expansion. Supports can overlap; petals reflect processing order. |
| Augmenting-path extraction | §4.5.1, pp.17–18 | Join the two search-tree paths and triggering bridge; recursively expand skipped petals with the appropriate parity. Whether an internal path uses its petal's bridge depends on whether the requested parity level is the minlevel or maxlevel. |
| Recursive removal | §4.5.2, pp.18–19 | Remove vertices on the chosen path, then repeatedly remove matched vertices whose predecessor lists became empty. Unmatched vertices are removed only if isolated. Continue the remaining bridges of tenacity `l_m`. |

### DDFS contract

The abstract input `H` is finite, directed and layered; every edge strictly decreases its layer, and every vertex reaches a layer-zero vertex (p.6). A bottleneck lies on every root-to-zero path from both roots. The highest bottleneck is unique when it exists. DDFS must produce either:

1. The highest bottleneck `b`, a red/green partition of the vertices above it reachable on root-to-`b` paths, and two rooted trees which overlap only at `b`; or
2. Vertex-disjoint paths from the two roots to distinct layer-zero vertices.

The first outcome entails the DDFS certificate: each red vertex has a red-root-to-vertex path disjoint from a green-root-to-`b` path, and conversely. Theorem 2.1 (p.8) additionally requires the advertised local linear work bound. A theorem that this certificate *implies* disjoint paths does not prove that the concrete DDFS procedure constructs the certificate.

The phrase “lie on all paths” in the definition of `V_b` and `E_b` on p.6 is interpreted as the union over relevant paths, not their intersection. This reading is required by the subsequent partition and spanning-tree obligations. The same-root case in the actual MV invocation is handled by an immediate abort/empty-new-petal branch (§4.3 footnote and §4.4); do not force it into a two-distinct-roots partition.

## Mathematical dependency map

| Target | Source claim | Principal prerequisites | Completion criterion |
| --- | --- | --- | --- |
| Augmentation safety and progress | §3, p.8 | Simple alternating path, free distinct endpoints | Prove flipped set is a matching and cardinality increases by exactly one. |
| Optimality from no augmenting path | §3, p.8 | Symmetric-difference path/cycle decomposition (Berge criterion) | Prove equivalence for every finite graph and matching, without assuming the missing direction. |
| DDFS correctness | Theorem 2.1, p.8 | Operational collision/backtracking invariants and layered reachability | Prove the actual procedure terminates with the required outcome; separately count work. |
| Matched endpoint relation | Lemma 5.2, p.20 | Simple alternating-path operations | Derive parity-level relations and equal tenacities for matched endpoints. |
| Limited BFS honesty | Theorem 5.3, p.20 | Minimal parity paths, splice/intersection arguments | For a vertex on such a path with at least the endpoint's tenacity, prove the stated prefix is minimal; obtain minlevel when inequality is strict. |
| Structural core | Theorem 6.19, pp.29–33 | Lemmas 6.9–6.18; nested induction on tenacity and minlevel; DDFS-style path certificates; §7 laminarity | Simultaneously prove unique base, unique same-tenacity bridge on each maxlevel path, laminarity, path decomposition/internal confinement, and base-on-path property. Only the bridge conclusion extends to `t = l_m`. |
| Runtime/mathematical correspondence | Lemma 6.20, p.33 | Structural core and actual petal updates | At the correct end-of-search-level instant, prove `bud*(v)=base(v)` and identify blossoms as unions of petals and lower blossoms. |
| Level computation | Theorem 8.3, pp.37–39 | Structural core, bridge classification Lemma 8.1, correct DDFS implementation | Strong induction on search level proves MIN assignment/prop completeness, bridge-bucket completeness, and MAX assignment correctness. |
| Support discovery | Claim 8.4, p.39 | DDFS, bud/petal correspondence, synchronization | Prove the newly found vertices are exactly `support(e) \ alreadyFound`. |
| Phase correctness | Lemma 8.5, p.40 | Path expansion, recursive removal, structural core | Produce a maximal family of disjoint shortest augmenting paths; show removal cannot destroy a disjoint shortest path. |
| Complete functional correctness | Theorem 8.6, p.40 | Phase correctness, augmentation, no-augmenting-path optimality, termination | Instantiated theorem about the concrete MV program, with no oracle premise for these derived claims. |
| Phase count and time | §1.2, p.5; Theorem 8.6, p.40 | Shortest-path phase lemma; imported phase bound; data-structure and primitive-operation costs | Separate cost semantics and proofs for RAM or pointer model; do not conflate them. |

The difficult induction must not be replaced with a “valid blossom” input structure that simply stores all five conclusions of Theorem 6.19 and then treats such a structure as supplied by the algorithm. Such an interface can organize intermediate conditional lemmas, but construction of its fields is the central open obligation until proved.

## Source qualifications that affect translation

These are local textual issues and scope cautions, not a conclusion that the MV algorithm is incorrect.

- **Base eligibility.** Remark 6.7 (p.21) explicitly demonstrates failure of base existence at `t = l_m`. Lemma 6.20 (p.33) does not repeat eligibility in its opening sentence. Its base expression must be used only in the eligible range fixed by the preceding definitions; applying it literally to every finite tenacity would overclaim.
- **Same-root footnote.** Footnote 3 on p.16 says equal `bud*` roots arise for a bridge with “non-empty support,” but p.17 describes the same-root abort using an empty-support example. The rendered p.16 confirms this is present in the PDF rather than an extraction error. The unambiguous operational branch is equality of contracted roots; no support equivalence should be inferred from that footnote alone.
- **Case-3 endpoint labels.** The end of the proof of Lemma 8.1 (p.37) describes appending an edge to reach `u`, but the subsequent inequality has `oddlevel(v)` on its left. Remark 8.2 repeats endpoint labels that are incompatible with its stated inner-vertex case if read literally. Reconstruct the needed inequalities from the path definitions rather than importing these sentences as axioms.
- **Temporal scope.** `bud*` is mutable. Lemma 6.20 identifies it with the base at the end of level `(t-1)/2`; after later levels it may instead be an iterated base (p.33). A single timeless equality is too strong.
- **Imported complexity.** The `O(sqrt(n))` phase bound and specialized set-union implementation are cited dependencies. This development must either formalize them, use a checked library theorem with matching hypotheses, or report the final bound as conditional. The pointer-model linear-time `bud*` question is expressly left open on p.40.

## Recommended order of implementation

1. Fix finite graph, edge identity, matching cardinality, simple alternating path, and extended-natural level semantics. Prove augmentation and small parity facts.
2. Implement the layered DDFS machine and prove its collision/ownership/backtracking invariants. At the same time, develop minimal-path splice lemmas needed by limited BFS honesty.
3. Formalize the simultaneous structural induction. Prove a representative nontrivial bridge/base step before building a large API around unproved interfaces.
4. Implement MIN, bridge queues, petals and `bud*`, then prove correspondence of the implicit DDFS graph and support discovery.
5. Implement recursive path expansion and removal; prove phase correctness and instantiate the complete matching algorithm.
6. Audit transitive assumptions and theorem/source correspondence. Treat phase count and machine-model cost as distinct declarations, with explicit status.

This ordering is a work plan. Only checked declarations listed in the project's build/assumption report count as completed formal verification.


## Checked mathematical milestones in the development

The following declarations are the concrete correspondence targets now implemented; the project's final build and axiom reports provide the mechanical checking evidence.

| Source claim | Formal declaration | Scope |
| --- | --- | --- |
| Augmentation increases matching size by one, §3 p.8 | `AltPath.augment_cardinality` | Executable flip on any augmenting simple path in a graph on `Fin n`. |
| No augmenting path iff maximum matching, §3 p.8 | `Matching.isMaximum_iff_noAugmentingPath` | Both directions for finite simple undirected graphs; converse uses a proved endpoint injection between alternating components. |
| Matched endpoints have equal tenacity, Lemma 5.2 p.20 | `matched_tenacity` | Includes infinite-level cases. |
| Limited BFS honesty and strict minlevel conclusion, Theorem 5.3 p.20 | `AltPath.limited_bfs_honesty` | Both endpoint/interior parities, free endpoints, and infinity; no blossom or DDFS assumption. |
| Last high-tenacity vertex on one path, Definition 6.2 p.21 | `AltPath.baseOnPath_exists_of_eligible`, `AltPath.baseOnPath_unique` | Per-path existence/uniqueness. Path independence is proved at every eligible tenacity by `general_unique_base`. |
| Path-relative base is even/outer, Definition 6.2 p.21 | `AltPath.baseOnPath_even`, `AltPath.baseOnPath_outer` | Proved from lastness, Lemma 5.2, and Theorem 5.3; no cross-path uniqueness premise. |
| Matched endpoints have equal global base-value sets, part of Lemma 6.12 p.24 | `matched_base_values_iff`, `matched_unique_base_iff` | Proves equality/transfer only, not unconditional base uniqueness or the root-filtered portions of Lemma 6.12. |
| Highest bottleneck uniqueness, §2 p.6 | `DDFS.highestBottleneck_unique` | Structural fact from a real root-to-bottom path; does not establish the DDFS machine or Theorem 2.1. |
| Same-root parity paths, Lemma 6.9 pp.22–23 | `rooted_shortest_even_iff_odd` | Shortest paths of either parity from a specified free root exist together, at eligible tenacity. |
| Minimum-tenacity common base and unique bridge, Lemma 6.13 pp.24–27 | `minimum_unique_base`, `AltPath.minimum_maxlevel_path_unique_bridge` | Both endpoint parities and all free roots; requires globally minimum finite eligible tenacity. |
| Relative shortest paths, Proposition 6.17 p.28 | `IsBase.shortest_relative`, `IsBase.append_relative_shortest` | Actual common bases split shortest paths; arbitrary shortest relative segments concatenate simply with shortest even prefixes. General common-base existence is supplied separately by `general_unique_base`. |
| Recursive blossom laminarity, Definition 6.8 and §7 | `blossoms_laminar` | Source-recursive blossoms over the actual partial base relation, with valid high-tenacity roots. Eligible base existence and coverage now follow from `GeneralStructureInduction` and `BlossomCover`. |
| DDFS path/bottleneck outcomes, §2 pp.6–8 | `DDFS.Machine.exists_correct_run`, `maximal_trace_correct` | Finite transition system: every maximal execution terminates with the specified paths or highest bottleneck. Layered input and bottom reachability are explicit premises. |
| DDFS bottleneck region, §2 p.6 | `DDFS.Machine.visited_iff_on_root_to_bottleneck` | Final visited vertices equal the union of root-to-bottleneck path vertices. Executable globally colored parent trees are now supplied by `DDFS.Machine.executeFull`; abstract local transition bounds are separately proved in `DDFSLocalWork`. |
| Shortest-family progress and phase count, invoked in Theorem 8.6 p.40 | `AugmentingFamily.shortest_length_increases`, `PhaseDriver.run_positivePhases_le_two_sqrt` | Actual family flips strictly increase shortest augmenting-path length. The outer loop has at most `2 * Nat.sqrt n` nonempty phases under its explicit `ShortestBlocking` search contract. |

The general common-base and relative-path confinement parts of Theorem 6.19 are proved by `general_base_and_confinement`; this direct induction does not require constructing the source's `H_v`. The same-tenacity bridge (including `t = l_m`), suffix-base and relative edge-tenacity conclusions are proved in `GeneralBridge`, `GeneralSuffixBase` and `GeneralEdgeBounds`. Semantic support coverage follows in `GeneralSupport`. Concrete matching-derived DDFS support discovery, representation costs, synchronized MIN/MAX refinement, complete phase construction, and the full Theorem 8.6 remain open. Finite-tenacity Lemma 8.1, additional base steps, witnessed weighted concatenation, local MIN preservation and output-local DDFS transition bounds are recorded in ADDITIONAL_PROOFS.md. These milestones do not by themselves constitute a formal verification of the full MV algorithm. See STATUS.md for the detailed checked/open boundary.
