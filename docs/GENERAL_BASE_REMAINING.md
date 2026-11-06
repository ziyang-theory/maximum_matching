# Remaining higher-tenacity common-base step

The general common-base theorem is still unproved. The new predecessor,
base-chain, and weighted-expansion lemmas remove several local obligations,
but they do not establish the intersection/rerouting step below. No version
of that step has been installed as an axiom or theorem with an admitted proof.

The source is the supplied [Vazirani manuscript](../max_matching.pdf),
arXiv:2012.03582v1 (7 December 2020), pp.29–32, with SHA-256
`05f3cfcc51c12eea0537cb9892a9bc832f8f175fc507b2b0f8228b68e922996c`.
The hash was rechecked during this investigation. This note concerns that
version, not a claim about subsequent literature.

## Exact targets

The first missing general theorem remains:

```lean
∀ {n : Nat} (G : Graph (Fin n)) (M : Matching G) (t : Nat),
  EligibleTenacity M t →
  ∀ v : Fin n, tenacity M v = some t → HasUniqueBase M v t
```

The direct-induction route isolates the following unresolved proposition,
unchanged from `STRUCTURAL_OBLIGATIONS.md`:

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

The general bridge target in `STRUCTURAL_OBLIGATIONS.md` is also unchanged:
uniqueness is among bridges of the endpoint's tenacity, and its range includes
`t = l_m`. Neither ordinary bridge uniqueness nor a strict-eligibility-only
statement replaces it.

## What is now proved

Write `E = p.length`, `O = q.length`, `t = E + O`, and let `u` be `q`'s
penultimate vertex. Here `E` is even, `O` is odd, and `O < E`.

- `AltPath.minlevel_last_predecessor_honest` (`MinCorrectness.lean`) proves that `q`'s prefix
  to `u` is shortest. Thus `evenlevel(u) = O - 1`, even when `u` has lower
  tenacity. This fact no longer needs the source's finite-tenacity restriction.
- `GeneralBaseEqual` discharges the equal-tenacity predecessor case without
  a global minimum hypothesis. Together with `GeneralBaseStep`, all cases
  `tenacity(u) ≥ t` are handled by the minlevel induction.
- `AltPath.predecessor_blossom_prefix` (`GeneralBaseChain.lean`) constructs a shortest even
  prefix `r_q` of `q` to the lower-blossom boundary `c`, with length
  `C = evenlevel(c) < O` and exactly the same threshold-`t` base values as
  `q`. It does not establish the corresponding statement for `p`.
- `WeightedExpansion` concatenates supplied actual edge segments and derives
  simplicity and disjointness from disjoint high-tenacity cores and local
  target-blossom containment. It neither selects the source's `H_v` nor
  supplies the required segment witnesses for that graph. The later `WeightedTopExpansion` results add low top vertices using actual
  confined initial segments and prove that the remaining core realization
  avoids the initial blossom. Full `H_v` selection remains separate.

## Two investigated direct routes

### Reverse the lower-blossom suffix

Suppose `tenacity(u) = τ < t`. Since `evenlevel(u) = O - 1`,

```text
oddlevel(u) = τ - (O - 1) < E + 1.
```

Consequently, even if the edge extension `p • (v,u)` is simple, it is not a
shortest odd path to `u`. Common-base theorems for shortest paths cannot be
applied to that extension.

A more promising walk is

```text
p • (v,u) • reverse(q[c to u]).
```

Its length is `E + 1 + (O - 1 - C) = t - C`, and its parity is odd.
The phase at both joins is correct: `q[c to u]` has even length, so its
reverse begins with the matched edge required after `(v,u)`.

If this walk is simple, `AltPath.disjoint_lower_boundary_reroute` in
`GeneralBaseReroute.lean` now gives a complete Lean proof of this subcase. The boundary has tenacity at least `t` (finite tenacities are odd,
and the boundary is above `t - 2`), while the even prefix of length `C` and
the constructed odd path bound its tenacity by `t`. Hence
`tenacity(c) = t`, the odd path is shortest, and appending vertices of
tenacity at most `t` preserves every threshold-`t` base of `p`.
The needed low-tenacity suffix bound follows from the established base chain:
`c` is the last vertex above `t - 2` on the shortest prefix to `u`.

What is not proved is simplicity, or a replacement with the same length and
base-preservation properties, when `p` intersects that lower suffix. A first
intersection can have the wrong parity for reversing the suffix. Switching
to a forward splice can yield a path to `u` longer than its evenlevel.
A subsequent first-intersection splice can meet the earlier lower-blossom
segment again. The checked weighted concatenation theorem does not supply
avoidance for this situation: `p` is not yet represented as a disjoint
high-core path with witnessed edge realizations.

### Checked intersection reductions

`higher_base_absent` and `base_prefix_avoids_opposite_suffix` compare distinct
actual threshold bases `b` and `c` at honest even indices `B ≥ C`. They prove
that `b` is absent from the opposite path and that the opposite prefix through
`C` avoids the original suffix starting at `B`. First-intersection splices and
shortestness derive these exclusions; they are not supplied avoidance premises.

`first_lower_boundary_hit_strict` assumes that the lower boundary `c` is absent
from the even maxlevel path. Its first hit on the other path's boundary-to-
predecessor suffix must occur at odd indices on both paths, and the even
maxlevel path's index is strictly larger. Equal indices would construct a
shortest predecessor path omitting its established boundary. Together with original-path low-blossom localization,
`absent_lower_boundary_disjoint` now eliminates all intersections when `c` is
absent from `p` and its boundary index `C` is at most an even high index `B`
on `p` whose vertex is absent from `q`. This theorem uses base existence and
confinement only at `t−2`; it derives the early-intersection exclusion. The
case `C>B` and the cases where `c` occurs on `p` remain open.

### Search in the parity-state graph and erase loops

The graph on states `(vertex, parity)` makes alternating walks easy to
construct, but a simple state path need not project to a simple graph path.
For the triangle with free vertex `0`, matched edge `{1,2}`, and unmatched
edges `{0,1}` and `{0,2}`, the state path

```text
(0,0), (1,1), (2,0), (0,1)
```

has no repeated state. Its projection repeats vertex `0`; it is not an
`AltPath`. It would incorrectly suggest a finite oddlevel for the only free
vertex. Deleting the odd cycle changes parity. Thus parity-state shortest
paths plus ordinary loop erasure cannot replace the required simple-path
construction.

## Concrete low-predecessor obstruction

This finite example shows exactly where the minimum-tenacity predecessor
argument stops working. It is a counterexample to that simplification,
not to the common-base theorem.

Take vertices `0,…,4`, matching `{1,2}, {3,4}`, and graph edges

```text
{0,3}, {0,4}, {1,2}, {1,3}, {2,3}, {2,4}, {3,4}.
```

Enumerating all simple alternating paths from the sole free vertex `0`
gives:

| Vertex | evenlevel | oddlevel | Tenacity |
| --- | ---: | ---: | ---: |
| 0 | 0 | ∞ | ∞ |
| 1 | 4 | 3 | 7 |
| 2 | 4 | 3 | 7 |
| 3 | 2 | 1 | 3 |
| 4 | 2 | 1 | 3 |

Choose `v = 1`, `p = (0,3,4,2,1)`, and `q = (0,4,3,1)`.
Then `u = 3`, `t = 7`, and `tenacity(u) = 3 < t`. The predecessor occurs
on `p` at odd index `1`, not at the even index `O - 1 = 2`.
The extension `p • (v,u)` already repeats `u`.
The full proposed complementary walk is

```text
0, 3, 4, 2, 1, 3, 4, 0.
```

Removing its even loop leaves the odd closed triangle `(0,3,4,0)`.
Removing that cycle changes the parity. The actual lower-blossom boundary
is `c = 0`, and the required base-preserving shortest path to it is simply
`(0)`. Thus the target holds in this example while the proposed fixed-length
walk/loop-erasure argument fails.

These calculations were independently reproduced by the following exhaustive
Python enumeration; they are not reported as new Lean-checked examples:

```python
V = range(5)
E = {frozenset(e) for e in
     [(0,3), (0,4), (1,2), (1,3), (2,3), (2,4), (3,4)]}
mate = {1: 2, 2: 1, 3: 4, 4: 3}
paths = []
def visit(p):
    paths.append(p)
    for w in V:
        if (w not in p and frozenset((p[-1], w)) in E
                and ((mate.get(p[-1]) == w) == ((len(p)-1) % 2 == 1))):
            visit(p + (w,))
visit((0,))
for v in V:
    print(v, [min((len(p)-1 for p in paths
                   if p[-1] == v and (len(p)-1) % 2 == a),
                  default=None) for a in (0, 1)])
```

## Sufficient next lemma and source route

A concrete sufficient rerouting lemma would supply one of these two outcomes,
without assuming common-base agreement at tenacity `t`:

1. `c` occurs on `p` at its honest evenlevel index `C`, and every later
   vertex of `p` has tenacity at most `t`; or
2. an actual simple odd alternating path to `c` of length `t - C`, obtained
   by retaining a prefix of `p`, deleting only vertices of tenacity at most
   `t`, and adjoining only vertices of tenacity at most `t`.

The first outcome gives the required shortest prefix. The second forces
`tenacity(c) = t` and gives a shortest odd path. In both cases the
threshold-base equivalence follows from the low-tenacity edits. This is a
sufficient structural formulation, not an exported or proved lemma.

Alternatively, follow the source's outer induction: pp.30–31 first establish
the unique bridge at the current tenacity using lower-tenacity confinement
and suffix-base facts; pp.31–32 then construct `H_v`, including the artificial
vertices `S′`, witnessed weighted segments, and exact length identities.
Only after that construction can the DDFS certificates and the new weighted
concatenation lemmas complete the path correspondence. Lower-tenacity base
existence alone is insufficient to instantiate those source steps; the
confinement and suffix-base parts of the simultaneous induction must also be
carried. Neither route has been completed in the present development.
