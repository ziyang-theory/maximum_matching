# Independent statement and assumption review

This is a historical component-review record. Its open obligations describe
that review's source snapshot; the completed solver and current validation
are recorded in [CHECKPOINT.md](CHECKPOINT.md) and [VALIDATION.md](VALIDATION.md).

**Final source-review conclusion:** the complete Berge criterion and both conclusions of the paper's Theorem 5.3 are faithfully formalized in the reviewed sources. Full MV correctness remains open. No substantive mathematical defect was found.

Review date: 5 November 2026. The reviewer read `Basic`, `PathLemmas`, `Levels`, `Augmentation`, `Phase`, `Optimality`, `Bud`, `Min`, `Examples`, and the then-current `Honesty` source against the supplied paper's definitions and relevant proof passages. These files were written by other agents. The reviewer authored `DDFS`; its build and axiom results below are checks, **not an independent review of that module's mathematical design**.

The reviewed source snapshot is identified by [SHA-256 hashes](review/source-hashes.json). Subsequent source changes are outside this snapshot until separately rechecked. The exact fresh directory is `/private/tmp/mm-independent-b6trjdx1`.

## Findings

No confirmed mathematical error was found in the checked declarations of the reviewed snapshot. This is acceptance of the stated partial results, not acceptance of a complete MV verification. In particular:

- `Matching` specifies a graph-respecting partial involution with no fixed points; `AltPath` specifies a vertex-simple alternating path from a free vertex. These are input definitions. Augmentation validity and cardinality gain are derived, not stored as assumptions in the input path.
- `augment` implements mate updates along the path. The proofs establish symmetry, edge validity, unchanged off-path mates, and exactly two newly saturated vertices. Saturated-count evenness is separately proved before using half the count as cardinality.
- `matched_last_fresh` supplies the simplicity argument needed to append a matched terminal edge. `matched_path_length_iff`, `evenlevel_matched`, and `matched_tenacity` genuinely establish the source's Lemma 5.2, including infinite-level cases.
- `level` is a noncomputable **semantic** minimum, with separately proved specifications for `some k` and `none`. It must not be identified with operational MIN/MAX output. The source comments preserve this distinction.
- The then-current `Honesty` proves an actual same-parity path splice and its simplicity, the resulting shorter-prefix intersection obligation, reverse augmentation, and the augmenting-path tenacity/honesty subcase. It does not at this snapshot prove the full Theorem 5.3.
- `BudForest.decreases` is a domain invariant needed for terminating root lookup and compression. The theorems correctly preserve roots under compression, but no runtime-MV theorem establishes that a constructed petal forest meets this invariant. The file header expressly records that limit.
- `Min` implements guarded candidate scans and local updates, including undirected already-scanned handling and retention of equal-level predecessor ties. It does not find a complete frontier, prove its labels are semantic minima, or establish DDFS support membership. `assignMax_sum` correctly requires `lo ≤ t` to justify natural subtraction.
- `Phase` establishes validity and gain for a pair of already supplied disjoint augmenting paths. It does not find a maximal shortest-path family. `Optimality` proves the necessary half of Berge's criterion; the sufficient half is still a combinatorial obligation in this snapshot.

One fixture-quality issue was reported to the implementing agent: the original `Examples.min_keeps_tied_predecessors` invokes raw `scan` on the triangle's matched edge at even search level zero, with an incorrect source-frontier label. It checks the raw local update, but it does not witness an allowed `scanCandidate` transition. A valid replacement uses two free roots adjacent to one matched vertex, scans the two unmatched edges at level zero, and retains both predecessors. This does not invalidate the universal local-update lemmas; it is a source-correspondence limitation of the original fixture.

## Fresh checking

Copied only Lean source files, `lakefile.toml`, and `lean-toolchain` into an empty permitted temporary directory. The scratch aggregate imported **every** source module, because the working aggregate at the time did not yet include the newer `Honesty` and `Optimality` modules. No project `.olean` files were copied. Existing Lean standard-library artifacts were reused.

Concrete executable:

```text
/Users/ziyang/Documents/github/formal_verification/formal_verification_skills/.cache/lean-4.34.0-darwin_aarch64/bin/lake
```

`lake build` exited 0 and built all 11 source modules plus aggregate (14 jobs), without warnings. An [audit module](review/Audit.lean) inspected 27 substantive declarations with `#print axioms`; all reports contain only subsets of `propext`, `Classical.choice`, and `Quot.sound`. None uses `sorryAx` or a custom axiom for a missing matching/DDFS claim. These reports concern logical dependencies, not proof of correspondence to the paper.

The development still lacks a concrete MV implementation with proved DDFS collision/coverage invariants, Theorem 6.19, MIN/MAX refinement, path expansion/removal and full maximum-matching correctness. That reviewed partial development did not establish Theorem 8.6's functional-correctness conclusion.

`lake env leanchecker --fresh MaximumMatching` also exited 0 on the source-only snapshot. This replays declarations using Lean's bundled kernel checker; it is not a second independently implemented kernel or a rebuilt toolchain. The [empty-graph boundary fixture](review/Boundary.lean) compiled with exit 0 and establishes zero cardinality, maximum cardinality, and absence of an augmenting path on `Fin 0`.

## Additional review: Berge criterion and first intersections

The [extended source hashes](review/extended-source-hashes.json) identify the later reviewed versions of `DifferenceUniqueness`, `SymmetricDifference`, `Optimality`, `Honesty`, `Splice`, `LimitedHonesty`, and `Examples`. This source review supersedes the earlier observation that Berge's converse was open. `lake env lean MaximumMatching/Optimality.lean` exited 0 on the reviewed version. The integration pass performs the final all-module build and axiom/kernel validation; a second full kernel replay was not duplicated for this review increment.

**Berge's criterion now has a complete mathematical proof.** `DifferencePath` specifies an M-alternating simple path whose other edges belong to N. Its extension operations prove freshness of the next vertex rather than assuming it. Under absence of an M-augmenting path, following these uniquely determined edges reaches an N-free vertex; finiteness supplies the decreasing measure `n - length`. A positive even terminal path ends at an M-matched vertex. Two such even paths with the same endpoint have the same starting vertex: reversing the final M edge and preceding N edge is deterministic, and the proof inductively removes two edges. The length-zero cases correctly distinguish an M-free vertex from a matched endpoint.

Consequently, the classical choice of one path per M-free/N-matched vertex defines an injection into N-free/M-matched vertices. The injection is independent of which witness is chosen because terminal equality forces initial equality. The source list is a duplicate-free enumeration of a subset of `Fin n`, so the image-length argument is valid. `excess_balance` has the correct orientation and yields `N.matchedCount ≤ M.matchedCount`; division by two gives the required cardinality inequality. `noAugmentingPath_isMaximum` and `isMaximum_iff_noAugmentingPath` require no algorithm-completeness hypothesis and contain no circular appeal to optimality.

**Splicing and first-intersection parity are faithful.** `spliceReverse` joins an odd replacement path to an even-indexed path vertex and traverses the old segment backward. Its parity assumptions establish the matching edge at the join; its `ReverseDisjoint` premise excludes precisely the retained segment while allowing the join itself. `FirstHit` is a separately constructed least intersection along the replacement path. On an even original path, an odd-indexed suffix consists of whole matched pairs, so a first intersection cannot occur at an even replacement index: its matched predecessor would have been an earlier intersection. Forward/reverse disjointness is then derived from minimality and path simplicity.

`LimitedHonesty.even_vertex_honest` proves the even-terminal/even-interior part of Theorem 5.3, including infinity. A shorter even replacement creates a shorter odd path by first intersection; comparison with an opposite-parity terminal path then contradicts the tenacity order. No intermediate BFS-honesty claim is assumed in this construction. This intermediate snapshot covered the even-terminal/even-interior result. The subsequent complete theorem is reviewed below.

**The MIN fixture finding is resolved.** The new `Examples.min_keeps_tied_predecessors` starts from a valid matching of the complete four-vertex graph, with free roots 0 and 1 and matched edge 2–3. It executes actual `scanCandidate` calls along unmatched edges 0–2 and 1–2 at search level zero, and checks that both predecessors are retained.


## Final review: full Theorem 5.3 and structural specifications

The [full-honesty source hashes](review/full-honesty-source-hashes.json) identify the stable declarations inspected for this final mathematical review. The implementing agent reports successful compilation; the root integration pass supplies the final fresh build, axiom inventory, and kernel replay for the assembled project. This reviewer did not duplicate that full replay.

`AltPath.limited_bfs_honesty` matches both claims of Theorem 5.3 (p.20). `p.Shortest` means that the path has minimum length among free-rooted simple alternating paths of its own parity ending at `p.last`. For every path index `i`, the premise compares endpoint tenacity with `p.vertex i` using the natural order extended by infinity. The first conclusion is precisely the parity-appropriate shortest-prefix property from Definition 5.1. A strict tenacity increase gives `minlevel M (p.vertex i) = some i.val`. There is no added eligibility, finite-tenacity, fixed-root, nonempty-matching, or DDFS-completeness premise.

The parity reductions preserve that statement:

- For an even terminal path and even interior index, the explicit first-intersection/reverse-splice construction proves honesty. The opposite-parity terminal-path comparison also proves the strict minlevel conclusion. If the endpoint's opposite level is infinite, a finite contrary tenacity contradicts the extended order; infinite interior levels are handled without substituting a finite sentinel.
- An odd interior index on an even path has its matched successor at the next even index. Lemma 5.2 transfers tenacity, and the proved matched parity-level correspondence recovers the original odd prefix length. For the strict conclusion, the successor's minlevel determines which original level is smaller.
- An odd terminal path with a matched endpoint is extended by its matched edge. `matched_last_fresh` proves that this extension remains simple, and `matched_shortest_iff` proves it remains shortest at the new even parity. The old path's vertices and indices are unchanged, and Lemma 5.2 preserves endpoint tenacity.
- An odd terminal path with a free endpoint is augmenting. Reversing it gives opposite-parity prefixes to every interior vertex, bounding that vertex's tenacity by the path length. The theorem's premise forces equality; its strict premise is impossible. This separately closes the free-endpoint case rather than assuming a nonexistent matched neighbor.

No base, blossom, support-discovery, or DDFS-correctness property is used to establish Theorem 5.3.

The `Structure` definitions also match their intended source objects:

- `levelLE`, `levelLT`, `levelMin`, and `levelMax` use `none` as infinity. `Outer` implies finite minlevel; `Inner` expressly requires finite minlevel. For unreachable vertices the min/max definitions are totalized to infinity, extending the paper's restricted definition without making such vertices inner or outer.
- `Predecessor` witnesses an actual minlevel path and its penultimate vertex; `PropEdge` forgets orientation; `Bridge` additionally requires graph adjacency. `ContainsEdge` accepts either orientation of a genuine path edge.
- `EligibleTenacity` expresses odd finite `t`, existence of a vertex with tenacity at most `t`, and strict inequality against every augmenting-path length. These are exactly `t_m ≤ t < l_m`, including `l_m = infinity` when no augmenting path exists.
- `InSupport` requires a graph bridge with finite tenacity `t ≤ l_m`, a vertex of the same tenacity, and an actual maxlevel path containing that bridge. Requiring finite `t` loses no witnessed maxlevel path: such a finite path has a finite maxlevel.
- `BaseOnPath` chooses the last path vertex with tenacity greater than `t`. Per-path existence and uniqueness are derived; neither asserts independence of the chosen shortest path. `HasUniqueBase` is only the pending path-independence predicate. Its eventual theorem must assume `EligibleTenacity M t` and `tenacity M v = some t`; the definition alone proves no part of Claim 6.4.


## Final increment: path-relative bases and matched-endpoint transfer

The [base source hashes](review/base-source-hashes.json) identify the stable `Base` module and its dependencies inspected in this increment. No substantive mathematical defect, hidden premise strengthening, or circular dependence was found. The root integration pass supplies final compilation and transitive-assumption validation.

`baseOnPath_even` needs only a path-relative base above the finite endpoint tenacity. If that base occurred at an odd index, it would have a later matched successor of the same tenacity, contradicting lastness. `baseOnPath_outer` then applies the already proved strict part of Theorem 5.3 and parity of the two levels; it never assumes cross-path base uniqueness. `prefixes_honest_at_minimum` has the explicit hypothesis that the endpoint's finite tenacity is a global minimum. This is exactly the minimum-tenacity setting used in Lemma 6.13, not an assumed shortest-prefix property.

The general initial-segment helper requires the removed suffix to contain no vertex above the threshold. Its append/truncate applications discharge that condition because the only changed endpoint has tenacity exactly equal to the threshold. `matched_shortest_path_transfer` handles even paths by removing the last matched edge and odd paths by appending the matched neighbor; simplicity and shortestness come from the previously proved path lemmas and Lemma 5.2 correspondence. Neither operation adds a new higher-tenacity vertex.

`matched_base_values_iff` therefore establishes the global `B(u) = B(v)` component of Lemma 6.12. Its hypotheses are slightly more general than the source's eligible-tenacity case, but the theorem merely equates base-value sets; it does not assert that either set is nonempty or a singleton. `matched_common_base_iff` and `matched_unique_base_iff` transfer the corresponding properties across a matched edge without asserting either property unconditionally.

These declarations do not yet establish the root-filtered `V_t(f)`, `A_f`, or `B_f` portions of Lemma 6.12: the current transfer theorem's public statement does not include preservation of the starting root. They also do not prove Lemma 6.13's global singleton assertion or unique-bridge assertion. The distinction is maintained in the source comments and final project status.
