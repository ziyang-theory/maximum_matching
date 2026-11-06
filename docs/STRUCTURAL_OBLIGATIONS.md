# Structural obligations after limited BFS-honesty

Theorem 5.3 and the matched-edge level identities are checked. Claim 6.4,
Lemma 6.13, and Theorem 6.19 remain unproved. This is a formalization gap,
not a counterexample to the paper or a claim that these statements are
mathematically open.

Source: the supplied *A Proof of the MV Matching Algorithm*,
arXiv:2012.03582v1 (7 December 2020), PDF pp.21–33; SHA-256
`05f3cfcc51c12eea0537cb9892a9bc832f8f175fc507b2b0f8228b68e922996c`.

## Checked steps toward the minimum-tenacity case

`MaximumMatching/Base.lean` proves:

- A path-relative base has even index and is an outer vertex
  (`AltPath.baseOnPath_even`, `AltPath.baseOnPath_outer`). The proof uses
  matched-edge tenacity equality and both parts of Theorem 5.3.
- At globally minimum finite tenacity, every prefix on a shortest path
  is BFS-honest (`AltPath.prefixes_honest_at_minimum`).
- Appending or deleting a terminal matched edge at the threshold
  preserves the path-relative base.
- Shortest paths transfer between matched endpoints while preserving
  all their base values (`AltPath.matched_shortest_path_transfer`).
- The base-value sets agree across a matched edge
  (`matched_base_values_iff`, the `B(u)=B(v)` part of Lemma 6.12).
- Unique-base assertions transfer across matched endpoints
  (`matched_unique_base_iff`); eligible-tenacity vertices are matched;
  an outer vertex's matched neighbor is inner (`matched_outer_inner`).
  These are the reduction steps in Lemma 6.13, Claim 1. They do not
  prove that any inner vertex has a path-independent base.

The path-relative base is already specified independently in
`Structure.lean`; its existence and uniqueness **on a single path** are
checked there. These facts must not be confused with agreement across
all shortest paths.

## First unproved target

For finite graphs, the minimum-tenacity instance of Claim 6.4 is:

```lean
∀ {n : Nat} (G : Graph (Fin n)) (M : Matching G) (t : Nat),
  EligibleTenacity M t →
  (∀ w, levelLE (some t) (tenacity M w)) →
  ∀ v, tenacity M v = some t → HasUniqueBase M v t
```

This is a target statement, not a theorem exported by the project. The
eligibility premise retains `t < l_m`, including the case `l_m = ∞`.
No theorem has been made conditional on this target and then presented
as full MV correctness.

## Investigated derivation and missing witnesses

The minimum-tenacity proof on pp.24–27 does more than compare numeric
levels. It forms a graph `H_v` from the union of shortest paths of both
parities to an inner vertex, initially with a fixed free root. Its layers
are minlevels. The formal development has not yet constructed this graph
and proved the required connection between its directed paths and simple
alternating paths in the original graph. There is also an explicit representation
step: the source permits horizontal top-layer bridges in `H_v`, whereas
`DDFS.LayeredGraph` requires strictly decreasing edges. A DDFS invocation
must use downward prop edges and treat the triggering bridge separately;
that refinement has not been proved.

The first central unproved certificate step is Claim 4 on p.25. For a
bridge `(u,u')`, let `b` be the highest common bottleneck of the relevant
minlevel paths. For every vertex `w` above `b` on those paths, the proof
needs the DDFS certificate from p.6: a directed path from one bridge
endpoint to `w` and a vertex-disjoint directed path from the other endpoint
to `b`, with the two roles exchanged according to the partition. These
must be lifted and concatenated with the bridge and a shortest path to
`b` to construct an **actual simple maxlevel path to `w` of the required
length**. Only then can one conclude `tenacity(w)=t`.

The current DDFS graph-theoretic lemmas do not supply that global
certificate. Rank decrease, successful traversal of one branch, and the
existence of one path to each sink are insufficient to infer the two
vertex-disjoint witnesses. Assuming the certificate in a theorem
parameter would merely relocate this missing proof.

Even after Claim 4, the following steps remain:

1. Prove the fixed-root bottleneck agreement and the inner induction
   (Claims 5–8, pp.26–27), including the claimed splices and their
   shortestness and disjointness conditions.
2. Prove that both parities have a shortest path from the same free root
   (Lemma 6.9, pp.22–23), then prove agreement between different free
   roots using the exclusion of an augmenting path of length `t`
   (Claim 9, p.27).
3. Establish the unique bridge on every maxlevel path; equality of
   base-value sets does not establish this claim.
4. For larger tenacities, define blossoms by well-founded induction and
   prove the five mutually dependent statements in Theorem 6.19,
   including laminarity and confinement of relative shortest paths.
5. Connect these semantic results to the changing petal/bud state,
   MAX's bridge supports, path expansion and recursive deletion.

The first-intersection machinery from `Splice.lean` is available for
these steps, but it only creates a splice after its exact disjointness
premise is proved. It does not justify the missing global bottleneck
or blossom invariants.
