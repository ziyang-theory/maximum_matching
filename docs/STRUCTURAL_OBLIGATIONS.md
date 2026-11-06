# Structural proof status and remaining induction

The minimum-tenacity common-base theorem and unique-bridge theorem
(Lemma 6.13) are proved. The mathematical DDFS path certificate is proved.
The general higher-tenacity common-base/bridge induction and its weighted
path realization remain unproved; full MV correctness does not follow yet.

Source: the supplied *A Proof of the MV Matching Algorithm*,
arXiv:2012.03582v1 (7 December 2020), PDF pp.21–36; SHA-256
`05f3cfcc51c12eea0537cb9892a9bc832f8f175fc507b2b0f8228b68e922996c`.
The source PDF has not been changed.

## Checked structural results

| Source claim | Checked declaration / module | Scope |
| --- | --- | --- |
| Limited BFS honesty, Theorem 5.3 | `AltPath.limited_bfs_honesty` | Both parity cases and infinite levels; no blossom premise. |
| Same-free-root parity paths, Lemma 6.9 | `rooted_shortest_even_iff_odd`, `SameRoot.lean` | Globally shortest paths, with the same specified free root and eligible endpoint tenacity. |
| Matched-endpoint transfer, Lemma 6.12 | `matched_common_base_iff`, `matched_unique_base_iff`, `matched_isBase_iff` | Transfers actual common bases; does not assume their existence. |
| Minimum-tenacity common base, Lemma 6.13(1) | `minimum_unique_base`, `MinimumBase.lean` | Eligible `t` and `t ≤ tenacity(w)` for every vertex. |
| Minimum-tenacity unique bridge, Lemma 6.13(2) | `AltPath.minimum_unique_bridge_maxlevel`, `MinimumBridgeAll.lean` | Both endpoint parities; actual unique edge index and bridge tenacity. |
| Relative shortestness, Proposition 6.17 | `IsBase.shortest_relative`, `RelativeShortest.lean` | Extracted base-to-endpoint segment minimizes length over all simple relative alternating paths of its parity. |
| Predecessor honesty, Lemma 6.18 | `AltPath.minlevel_predecessor_honest`, `PredecessorHonesty.lean` | A minlevel path's predecessor is honest when its successor has at least endpoint tenacity; stronger than the source's local premise. |
| Blossom definition | `IsBase`, `base`, `BaseStratum`, `Blossom`, `Blossom.lean` | Actual common-base relation and source recursion. `base = none` means no common base exists, not an unresolved proof placeholder. |
| Blossom laminarity, Theorem 6.19(3) / Proposition 7.6 | `blossoms_laminar`, `BlossomLaminar.lean` | Arbitrary odd thresholds and roots above their respective thresholds. It does not assume that every finite-tenacity vertex has a base. |
| Minimum-tenacity path confinement and edge bounds | `minimum_blossom_relative_paths`, `MinimumRelative.lean` | Every vertex on any shortest relative path lies in its blossom or is its base; every edge has tenacity exactly `t`. Uses the genuine shortest-path concatenation in `RelativeJoin.lean`. |
| Lower-blossom coverage | `unique_blossom_cover_of_base_existence`, `BlossomCover.lean` | Explicitly conditional on actual common-base existence below the cutoff; terminates by decreasing minlevel. |
| Separation of lower-blossom expansions | `BlossomEdgeExpansion.disjoint_of_endpoints`, `blossom_hulls_disjoint` | Derives disjointness from actual segment containment and disjoint high-tenacity cores; does not construct the weighted realizations. |

The minimum-base proof uses a checked induction on minlevel rather than
formalizing the source's fixed-root Claims 3–9 verbatim. For an inner vertex,
the predecessor on an odd minlevel path either occurs on an even maxlevel
path at the same index, or can be appended to it. In both cases the bases
reduce to a strictly smaller minlevel. `MinimumSuffix.lean` proves the
required low-tenacity suffix and `BaseUnique.lean` proves the parity-base
agreement. The outer case reduces across its matched edge.

Laminarity is proved by identifying the source recursion with bounded
chains in the functional `IsBase` relation (`blossom_iff_base_cut`). This
establishes the claim for all blossoms that exist under the actual
relation; it does not supply the still-missing general base-existence proof.

The mathematical DDFS result includes the strong per-vertex disjoint-path
certificate; see [DDFS_CERTIFICATE.md](DDFS_CERTIFICATE.md). Separately, the
explicit two-search stack transitions now have a total-correctness proof for
their path/bottleneck outcomes; see [DDFS_OPERATIONAL_PROOF.md](DDFS_OPERATIONAL_PROOF.md).
Globally colored spanning-tree output and linear machine cost remain unproved.

## First missing general theorem

The minimum restriction must be removed from the common-base theorem:

```lean
∀ {n : Nat} (G : Graph (Fin n)) (M : Matching G) (t : Nat),
  EligibleTenacity M t →
  ∀ v : Fin n, tenacity M v = some t → HasUniqueBase M v t
```

This is a fully typed target proposition, not an exported theorem. The
minimum instance is already proved. Eligibility retains the strict
condition `t < l_m`, including `l_m = ∞`.

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

Both displayed target propositions were type-checked with Lean 4.34.0.
No axiom or `sorry` declaration was introduced for either target.

## Concrete remaining weighted-path obligation

The next missing source construction is the higher-tenacity graph `H_v`
on pp.31–32, using the already-proved lower-tenacity induction hypotheses.
It must supply the following finite data and prove these invariants:

1. Select the actual high-tenacity vertices on both shortest parities and
   the additional top vertices `S′`. Retain an explicit map to original
   graph vertices. Ordinary directed edges decrease the assigned layer;
   the triggering top bridge is separate from the DDFS edge relation.
2. Replace each maximal lower-tenacity stretch by an edge carrying an
   actual simple alternating segment. Prove its endpoints, parity,
   length, and containment in the specified lower blossom. These are
   construction obligations, not fields to be assumed without witnesses.
3. Distinguish assigned DDFS layers from segment lengths and actual
   minlevels. In particular, the source assigns additional vertices in
   `S′` to layer `(t-1)/2`; they may lie inside lower-tenacity blossoms.
   A directed path's edge count is not the length of its expanded path.
   The latter must equal the sum of the actual edge-realization lengths.
4. Construct a simple alternating realization of each relevant directed
   path by concatenating the witnessed segments. Prove simplicity and
   alternation at every join. For two disjoint DDFS certificate paths,
   construct vertex-disjoint realizations. The lower-blossom separation
   theorem is checked, but the segment selection and complete weighted
   concatenation are not yet constructed.
5. Add the triggering bridge and a shortest prefix to the bottleneck.
   Prove that the resulting actual alternating path has complementary
   parity and the exact length required for `tenacity(w)=t`. An abstract
   DDFS certificate alone does not establish this length or alternating
   path in the original graph.

The simple minimum-tenacity predecessor induction cannot simply be
reused: at a larger `t`, the predecessor can have tenacity below `t`, and
an even maxlevel-path prefix at that vertex need not be shortest. The
lower-blossom expansion is precisely the missing mechanism for that case.

After this construction, the remaining semantic induction must prove the
general bridge target, common-base existence, confinement of every
relative shortest path, and the base-on-path conclusion of Theorem 6.19(5).
Checked laminarity and relative shortestness can then be reused without
assuming those conclusions again.


## Investigated direct base-chain jump

A direct minlevel induction can avoid the weighted graph only if it can
reroute through a lower blossom's boundary while preserving the original
path's bases at threshold `t`. One further general-tenacity case is now
proved in `GeneralBaseStep.lean`: `AltPath.high_predecessor_occurs` and
`AltPath.high_predecessor_bases` show that a predecessor of tenacity
strictly greater than `t` occurs at index `oddlevel(v)-1` on every even
shortest path, and is the base on both parity paths. These results do not
assume globally minimum tenacity. They use actual fresh extension when
the predecessor is absent, and the general suffix tenacity bound.

The unresolved jump can be isolated as this type-checked target:

```lean
∀ {n : Nat} (G : Graph (Fin n)) (M : Matching G)
  (p q : AltPath M), p.Shortest → q.Shortest →
  p.length % 2 = 0 → (hqo : q.length % 2 = 1) →
  q.last = p.last → q.length < p.length →
  EligibleTenacity M (p.length + q.length) →
  let t := p.length + q.length
  let u := q.vertex ⟨q.length - 1, by omega⟩
  ∀ c : Fin n, Blossom M (t - 2) c u →
    levelLT (some (t - 2)) (tenacity M c) →
    ∃ r : AltPath M, r.last = c ∧ r.Shortest ∧
      ∀ b : Fin n, p.BaseOnPath t b ↔ r.BaseOnPath t b
```

This is not an exported theorem or an added correctness assumption.
Lower-blossom coverage supplies `c`, and its occurrence on the honest
prefix to `u` makes `minlevel(c) < minlevel(v)`. The target asks for an
actual shortest path to `c` preserving all threshold-base values of `p`;
merely producing some path to `c` is insufficient.

The present first-intersection results do not establish that preservation.
Write `E = p.length`, `O = q.length`, and `τ = tenacity(u) < t = E+O`.
Lemma 6.18 gives `evenlevel(u)=O-1`. If `u` is absent from `p`, appending
`(v,u)` produces an odd path of length `E+1`, while
`oddlevel(u)=τ-(O-1)<E+1`. Consequently the extension is not shortest,
and the proved common-base/relative-join theorems do not apply to it.
If `u` occurs on `p`, its prefix may instead be dishonest; the
minimum-case index-alignment contradiction also disappears.

Reversing the lower-blossom segment from `u` to `c` after that extension
would have the desired complementary length `t-evenlevel(c)`, but the
segment may intersect `p` internally. At such an intersection, the prefix
of `p` ending at a low-tenacity vertex is not known to be shortest.
Current splice lemmas require a proved avoidance premise and do not
preserve the last vertex above `t` after arbitrary rerouting. The checked
relative-join theorem starts with a shortest even prefix to an actual
base, so it does not fill this missing premise. No counterexample to the
jump statement has been established; this is an exact remaining proof
obligation for the direct approach.

## Separate algorithm obligations

Even completing the semantic induction would not complete the requested
MV verification. The DDFS transition, coverage and path/bottleneck correctness
proofs are now checked. Its colored-tree output, executable adjacency
refinement and linear cost accounting remain. Petal/bud correspondence
(Lemma 6.20), synchronized MIN/MAX refinement
(Theorem 8.3), exact support discovery, expansion/removal of a maximal
shortest augmenting-path family, and the concrete algorithm's work bound
must still be connected. Generic supplied-family or supplied-phase
correctness results do not construct these MV operations.
