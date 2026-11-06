# Checked limited BFS-honesty

Theorem 5.3 of the supplied paper is proved by
`MaximumMatching.AltPath.limited_bfs_honesty` in
`MaximumMatching/LimitedHonesty.lean`. This is a structural theorem about
shortest alternating paths. It does not verify the MIN/MAX implementation.

Source: Vijay V. Vazirani, *A Proof of the MV Matching Algorithm*,
arXiv:2012.03582v1, 7 December 2020, PDF p.20. The local PDF SHA-256 is
`05f3cfcc51c12eea0537cb9892a9bc832f8f175fc507b2b0f8228b68e922996c`.

## Statement correspondence

- `AltPath M` is a finite vertex-simple path starting at a free vertex; its
  edge with index zero is unmatched, and edge membership alternates.
- `p.Shortest` means that its length is minimum over **all** free-rooted
  alternating paths to its endpoint of the same parity. The start vertex
  is not held fixed in this minimization.
- `p.BFSHonest i` says that the prefix ending at position `i` is shortest
  among all free-rooted paths of that parity to `p.vertex i`.
- `levelLE a b` and `levelLT a b` compare natural lengths with `none` as
  infinity. `tenacity` is the sum of even and odd levels; `minlevel` is their
  minimum.
- The theorem proves both conclusions: if the interior vertex's tenacity
  is at least the terminal vertex's tenacity, its prefix is shortest; if
  strictly greater, that prefix length equals its minlevel.
- Both endpoint parities, both interior parities, free endpoints, and
  infinite levels are included. The proof does not require a finite vertex
  type, because its path arguments are finite.

## Reconstructed argument

The core case has an even terminal path and an even interior index `k`.
Suppose a shorter even path reaches that interior vertex. A direct splice
would contradict shortestness unless the shorter path hits the strict
suffix. At its first hit, the shorter path has odd index: an even index
would have a matched predecessor that hit the suffix earlier. An odd
index on the original path permits a shorter forward splice, so the hit
must have even index there. Reversing the original segment from this hit
back to `k` produces an odd path shorter than the original terminal path.
All splice constructions prove vertex simplicity and alternation.

A second first-intersection argument compares with a shortest odd path
to the terminal vertex. It either bounds the odd level at `k` by the odd
terminal level plus the retained suffix length, or lower-bounds the odd
terminal level by `k-1`. Together with the first splice, either case
contradicts the tenacity premise. The same comparison proves the strict
minlevel conclusion.

Matched edges transfer the result between interior parities and between
terminal parities, using the fully proved Lemma 5.2. A free odd terminal
vertex cannot use this transfer. That case is proved separately: reversal
of an augmenting path supplies both parity-level upper bounds at every
interior vertex; their sum is at most the path length. The tenacity
premise forces equality, and a strictly larger tenacity is impossible.

## Main declarations

| Declaration | Role |
| --- | --- |
| `AltPath.matched_last_fresh` | Appending a matched edge to an odd path preserves simplicity |
| `evenlevel_matched`, `matched_tenacity` | Full Lemma 5.2, including infinity |
| `AltPath.splice`, `AltPath.spliceReverse` | Actual forward and reverse simple-path constructions |
| `AltPath.FirstHit.odd` | First-hit parity on a suffix consisting of matched pairs |
| `AltPath.shorter_even_prefix_opposite` | First central splice contradiction |
| `AltPath.odd_terminal_comparison` | Second central splice comparison |
| `AltPath.augmenting_tenacity_bound` | Free-terminal boundary case |
| `AltPath.limited_bfs_honesty` | Full Theorem 5.3 |

The checked main theorem depends only on Lean's `propext`,
`Classical.choice`, and `Quot.sound`. Semantic levels use mathematical
choice; they are not an executable replacement for MIN/MAX. No new
mathematical axiom, `sorry`, or native-computation theorem was used.
