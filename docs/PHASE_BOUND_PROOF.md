# Shortest-path phase progress and phase count

The mathematical phase-progress and square-root phase-count arguments are now checked. They apply to the executable family flips and outer loop in this project. They do not establish that the currently incomplete MV MIN/MAX implementation returns the required family, or bound its machine cost.

The source invokes the square-root phase bound in Theorem 8.6, p.40, after describing maximal families of vertex-disjoint shortest augmenting paths in §4, p.11, and Lemma 8.5, p.40. The proof below reconstructs that dependency from the project's proved Berge criterion instead of assuming an external phase-count theorem. Source version and hash are recorded in [SOURCE_MAP.md](SOURCE_MAP.md).

| Declaration | Checked statement | Assumptions beyond a finite simple graph |
| --- | --- | --- |
| `exists_differenceFamily` | There are `N.cardinality - M.cardinality` vertex-disjoint `M`-augmenting paths, with even-index edges from `N`. | Two legal matchings `M`, `N`. |
| `deficit_of_long_paths` | `(N.cardinality - M.cardinality) * (l+1) ≤ n`. | Every `M`-augmenting path has at least `l` edges. |
| `AugmentingFamily.shortest_length_increases` | Every augmenting path after `f.run` has length greater than `l`. | `f` is a maximal vertex-disjoint family of shortest augmenting paths of length `l`. |
| `PhaseDriver.run_phases_cutoff` | The remaining positive phase count is at most `k + n/(l+k+1)`. | Every current augmenting path has length at least `l`; each nonempty search result is a maximal shortest family. |
| `PhaseDriver.run_positivePhases_le_two_sqrt` | Positive phase count is at most `2 * Nat.sqrt n`. | Each nonempty search result is a maximal shortest family. |

`Nat.sqrt` is the integer floor square root; all divisions in this table are natural-number divisions. The last bound concerns positive phases. The outer loop can perform one final search returning the empty family. Its separate `Complete` predicate requires such an empty result to imply absence of augmenting paths. The phase-count theorem does not need this predicate, since stopping prematurely can only reduce the count.

## Difference packing

Apply the proved Berge criterion to the graph consisting of the edges of `M` and `N`. If `|N| > |M|`, this produces an augmenting path `p` whose unmatched edges belong to `N`. Delete all vertices of `p` from both matchings and from the graph. Matched edges cannot leave this component. The checked endpoint count gives

```text
|N_without_p| + |M| + 1 = |M_without_p| + |N|.
```

The comparison matching strictly decreases in size, so recursion terminates. Lift the residual paths back into the original graph and prepend `p`. They remain disjoint. This constructs the asserted number of paths. Their distinct vertex lists establish the deficit bound: each path of at least `l` edges uses at least `l+1` vertices.

## Strict progress

Let `f` contain `k` disjoint shortest augmenting paths of length `l`. Suppose the actual flipped matching `f.run` admits an augmenting path `q` of length at most `l`. Flipping `q` gives a matching `N` with

```text
|N| = |M| + k + 1.
```

Difference packing supplies `k+1` disjoint `M`-augmenting paths. Shortestness forces their vertex lists to contain at least `(k+1)(l+1)` vertices. Every one of those vertices has different mates in `M` and `N`, so it lies in the union of the vertices of `f` and `q`: all actual flips leave mates outside this union unchanged.

If `q` meets a path of `f`, this union contains fewer than `k(l+1)+(l+1)` vertices. The formal proof removes one repeated vertex from a list and applies the proved distinct-list cardinality bound, yielding a contradiction. Thus `q` is disjoint from `f`. Transport it through the unchanged mates back to an `M`-augmenting path. It must have length exactly `l`, contradicting maximality of `f`.

This proof uses only the actual flip operation, path simplicity, the family conditions, and the proved difference decomposition. Phase progress is not an input field.

## Phase count

Induct on a cutoff `k`. At cutoff zero, each positive phase gains at least one matching edge. The final matching's cardinality deficit is at most `n/(l+1)` by difference packing. For a positive first phase, strict progress raises the lower bound on augmenting-path length by at least one, so the induction applies with parameters `k` and `l+1`. An empty phase terminates immediately. This proves

```text
positivePhases ≤ k + n/(l+k+1).
```

Set `l=0` and `k=Nat.sqrt n`. The checked core-library inequality `n < (k+1)*(k+1)` gives `n/(k+1) ≤ k`, hence at most `2*k` positive phases. The argument includes `n=0` and empty search results.

## Trust and remaining connection

The four central declarations (`exists_differenceFamily`, `deficit_of_long_paths`, `shortest_length_increases`, and `run_positivePhases_le_two_sqrt`) report only `propext`, `Classical.choice`, and `Quot.sound` under `#print axioms`. None depends on `sorryAx` or a custom axiom.

`PhaseDriver.ShortestBlocking` is a transparent search specification, not a proof that concrete MV satisfies it. To instantiate Theorem 8.6, the remaining implementation must establish this specification and `PhaseDriver.Complete` from MIN/MAX, path expansion, and recursive removal. RAM/pointer-model costs and set-union complexity remain separate obligations.
