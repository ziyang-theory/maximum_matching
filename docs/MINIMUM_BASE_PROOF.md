# Minimum-tenacity bases and blossoms

The development now proves the minimum-tenacity common-base and unique-bridge claims of Lemma 6.13 (pp.24–27), and the relative-path confinement and edge-tenacity parts of the minimum-tenacity basis of Theorem 6.19 (pp.29–30). These are checked mathematical results. The general outer induction over larger tenacities, operational MIN/MAX correspondence, and the complete MV theorem remain separate obligations.

Source: the supplied *A Proof of the MV Matching Algorithm*, arXiv:2012.03582v1, 7 December 2020. Its hash and exact definition correspondence are recorded in [SOURCE_MAP.md](SOURCE_MAP.md).

## Quantifiers and assumptions

`minimum_unique_base M t ht hmin v hvt` proves `HasUniqueBase M v t` for an arbitrary vertex type and simple undirected graph. Here `hvt` states `tenacity M v = some t`; `hmin` states every vertex has tenacity at least `t`, with `none` representing infinity; and `ht : EligibleTenacity M t` retains the strict bound `t < l_m` through the absence of augmenting paths of length at most `t`. Thus the theorem concerns the attained global minimum finite eligible tenacity. It does not assert base existence for every eligible tenacity.

`HasUniqueBase` quantifies over **all** shortest parity paths to the vertex, including paths starting at different free roots. Its conclusion is not merely uniqueness on one path or agreement for one pair of witnesses.

## The alternative minimum-level induction

The formal proof uses an induction on minimum level and a direct predecessor argument. It proves the source claim without assuming DDFS correctness or fixed-root bottleneck agreement.

For an inner vertex, let `p` be an even shortest path of length `E` and `q` an odd shortest path of length `O`, where `O < E` and `E+O=t`. Let `u` be the predecessor of their common endpoint on `q`.

1. Limited BFS honesty at global minimum tenacity makes every prefix of `p` and `q` honest. In particular, `u` has evenlevel and minlevel `O−1`. If `u` occurs on `p`, it occurs exactly at index `O−1`: an odd-index occurrence would force tenacity below `t`.
2. A first-intersection splice proves that every vertex of `p` from index `O` onward has tenacity exactly `t`. For an index strictly larger than `O`, the splice supplies an opposite-parity path of complementary length. The index `O` follows from its matched successor. This is `tenacity_suffix_minimum`; no walk simplification is assumed.
3. If `tenacity(u)=t`, the induction hypothesis gives its common base at the smaller minlevel `O−1`. If `u` occurs on `p`, restrict both paths to their honest prefixes ending at `u`. If it does not occur on `p`, append the actual unmatched edge to obtain a simple odd shortest path to `u`. Removing or adding only tenacity-`t` suffix vertices preserves the path-relative base. Both original paths therefore have the same base.
4. If `tenacity(u)>t`, freshness of `u` from `p` would permit an odd path to `u` of length `E+1`. Together with evenlevel `O−1`, this contradicts its high tenacity. Hence `u` occurs on `p` at index `O−1`, and the suffix bound makes `u` the base of both paths.

For an outer endpoint, its matched neighbor has the same tenacity and a minimum level smaller by exactly one. The already-proved matched-edge base correspondence transfers the induction result back. Eligibility excludes a free endpoint in this reduction. Finally, agreement between every even/odd path pair yields one base shared by all shortest paths; per-path base existence and uniqueness close the argument.

## Unique bridge and relative paths

At minimum tenacity, the checked geometry gives the minlevel of vertex `p[i]` on the long even path as `min(i, E+O−i)`. Every nonmiddle edge is a prop in the appropriate direction. The middle edge is the sole bridge and has tenacity `t`. Extending an odd maxlevel path by its matched edge reduces the other parity to this case; the appended edge is proved to be a prop before restricting the bridge back.

`AltSegment` models simple alternating paths from a base with an unmatched first edge; its start need not be free. `IsBase.shortest_relative` proves that every global shortest path splits at its common base into a shortest even prefix and a genuinely shortest relative segment. Its comparison ranges over all relative segments, including ones that intersect the prefix. A first-intersection argument either shortens the global path or gives a forbidden short odd path to the high-tenacity base.

The converse, `IsBase.append_relative_shortest`, proves that **any** shortest even prefix to the base joins to **any** shortest relative path to its child. Relative minimality fixes the exact suffix length. An opposite global shortest path through the same base supplies the tenacity bound. The resulting disjointness is proved before the actual concatenation is constructed.

`minimum_blossom_relative_paths` then proves, for any member of a minimum-tenacity blossom and any shortest relative path to it, that every vertex lies in the blossom or is its base, and every edge has tenacity exactly `t`. It applies the proved joining theorem and global shortest-path suffix confinement, not an assumed expansion certificate.

## Recursive blossoms and scope

`Blossom` follows Definition 6.8 (p.22), with the empty base case at index one. `IsBase` is the actual common-base relation, whose functionality is proved. The recursion is equivalent to a finite chain of these bases with every nonroot tenacity at most the threshold. Functional parent chains give boundary uniqueness and laminarity of the resulting blossoms (`blossoms_laminar`), matching the iterated-base argument of §7.

This laminarity proof does not establish that every eligible-tenacity vertex has a base. `blossom_cover_of_base_existence` exposes the precise additional premise needed for coverage: actual base existence for all vertices at or below the chosen cutoff. It is an assembly lemma for a lower-tenacity induction hypothesis, not a replacement for the general common-base theorem.

The independent helper `minlevel_predecessor_honest` proves Lemma 6.18's local conclusion in a stronger form: on a minimum-level path, the predecessor of any vertex whose tenacity is at least that of the endpoint is honest. `GeneralSuffix` also bounds suffix tenacities without the global-minimum assumption. These support the remaining general induction but do not complete it.

The central checked declarations report only `propext`, `Classical.choice`, and `Quot.sound` under `#print axioms`. No common-base, bridge, phase-progress, or laminarity claim is imported as a custom axiom.
