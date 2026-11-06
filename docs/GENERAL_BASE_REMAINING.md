# General common bases and confinement: completed proof

The original higher-tenacity common-base target is now proved, together with
confinement of arbitrary shortest relative paths, in
`GeneralStructureInduction.lean`. This file retains its original name for
existing links. The remaining structural obligations are listed in
[STRUCTURAL_OBLIGATIONS.md](STRUCTURAL_OBLIGATIONS.md).

The source is the supplied [Vazirani manuscript](../max_matching.pdf),
arXiv:2012.03582v1 (7 December 2020), Theorem 6.19, pp.29–33; SHA-256
`05f3cfcc51c12eea0537cb9892a9bc832f8f175fc507b2b0f8228b68e922996c`.

## Checked conclusions

`general_unique_base M t ht v hvt` proves `HasUniqueBase M v t` for every
vertex with `tenacity M v = some t` and `EligibleTenacity M t`. It applies to
arbitrary vertex types, so includes the original finite-graph target.
There is no lower-tenacity correctness or base-existence premise.

`general_blossom_relative_confined M t ht b v hv hb q hq hqb hqv` proves
that every vertex of an arbitrary shortest relative path from the actual
high boundary `b` to a member `v` lies in `Blossom M t b` or equals `b`.
It covers iterated-base members, both path parities, and all eligible cutoffs.
It does not yet prove the source's edge-tenacity bound or suffix-base property.

## Proof route

The joint theorem `general_base_and_confinement` uses strong induction on
eligible tenacity. The base step at the current cutoff uses an inner induction
on minlevel. For shortest even/odd paths of lengths `E` and `O`, with `O<E`,
the equal/higher-tenacity predecessor cases use the earlier checked reduction.
For a lower predecessor, its established lower blossom promotes into the odd
path's current blossom using bases at smaller current minlevels.

When the odd path's base has no larger minlevel, minimize over short shortest
paths ending in that blossom and meeting the even path's high suffix. The
first-hit inequalities force a shortest prefix with the wrong boundary.
For the other order, minimize over **even** shortest paths whose endpoints
lie on the even path. Matching closure excludes every earlier interior hit.
A final matched pair either gives a shortest prefix containing the boundary
or forces two reverse splices that give the supposedly high boundary tenacity
at most `E+O`. Both splices are actual simple alternating paths.
`general_unique_base_of_lower` then discharges the entire inner induction.

Confinement uses induction on actual shortest-path length. Honest prefixes
recurse at a shorter length or use the lower-tenacity endpoint lemma. A
dishonest last predecessor forces an odd maxlevel path to an outer endpoint;
the predecessor belongs to that endpoint's lower blossom. Select its first
entry on the path. Replacing the reversed tail by a shortest relative path
proves the original reversed tail shortest, then lower confinement applies.
The prefix just before entry is honest: otherwise the entering edge would
have tenacity at most `t−2` while crossing distinct lower blossoms. The
small-edge boundary-equality theorem rules this out by two opposite first-hit
arguments and a genuine append/reverse construction.

Finally, arbitrary shortest relative paths are joined to shortest even
boundary prefixes. Their exact lengths and disjointness follow from the
actual common-base chain. Joint tenacity induction supplies every lower
hypothesis; no current confinement assumption is used to establish itself.

The original walk/loop-erasure shortcut was not used. The following retained
example explains why that shortcut was insufficient; it is not a counterexample
to the now-proved theorem.

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
