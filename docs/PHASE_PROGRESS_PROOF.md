# Shortest-path phase progress

`AugmentingFamily.shortest_length_increases` proves that executing a maximal
vertex-disjoint family of shortest augmenting paths strictly increases the
length of every remaining augmenting path. The proof concerns actual matching
flips and derives the required symmetric-difference decomposition internally.

## Difference packing

Apply the proved Berge criterion to the graph consisting of the edges of `M` and `N`. If `|N| > |M|`, this produces an augmenting path `p` whose unmatched edges belong to `N`. Delete all vertices of `p` from both matchings and from the graph. Matched edges cannot leave this component. The checked endpoint count gives

```text
|N_without_p| + |M| + 1 = |M_without_p| + |N|.
```

The comparison matching strictly decreases in size, so recursion terminates. Lift the residual paths back into the original graph and prepend `p`. They remain disjoint. This constructs `N.cardinality - M.cardinality` disjoint augmenting paths.

## Strict progress

Let `f` contain `k` disjoint shortest augmenting paths of length `l`. Suppose the actual flipped matching `f.run` admits an augmenting path `q` of length at most `l`. Flipping `q` gives a matching `N` with

```text
|N| = |M| + k + 1.
```

Difference packing supplies `k+1` disjoint `M`-augmenting paths. Shortestness forces their vertex lists to contain at least `(k+1)(l+1)` vertices. Every one of those vertices has different mates in `M` and `N`, so it lies in the union of the vertices of `f` and `q`: all actual flips leave mates outside this union unchanged.

If `q` meets a path of `f`, this union contains fewer than `k(l+1)+(l+1)` vertices. The formal proof removes one repeated vertex from a list and applies the proved distinct-list cardinality bound, yielding a contradiction. Thus `q` is disjoint from `f`. Transport it through the unchanged mates back to an `M`-augmenting path. It must have length exactly `l`, contradicting maximality of `f`.

This proof uses only the actual flip operation, path simplicity, the family conditions, and the proved difference decomposition. Phase progress is not an input field.

## Solver connection

`PhaseDriver.ShortestBlocking` specifies maximal shortest-family output.
`Search.blockingPhase_shortestBlocking` proves this property for the concrete
MIN/MAX/DDFS phase. Separately, `Search.blockingPhase_complete` proves that an
empty phase means there is no augmenting path. The latter property and the
Berge criterion establish `Search.maximumMatching_isMaximum` for the actual
terminating solver.

The axiom audit and source-only kernel replay are recorded in `validation/`.
