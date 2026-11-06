# Search and recovery review

This historical review covers the single-path search and recovery development.
The subsequent full blocking-phase review is recorded in BLOCKING_PHASE_PROOF.md.
Exact current source hashes and machine results are in `validation/`.

## Independent statement and implementation checks

- **Bucket coverage:** an independent pass checked that initial lower-blossom
  representation and a complete queued bridge list suffice. The proof does
  not assume the desired MAX discovery. Actual contractions either label the
  target or preserve disjoint arms; final trigger equality excludes surviving
  arms. The permitted threshold includes equality with shortest augmentation
  length.
- **Base restoration:** an independent pass checked the dependency order.
  Complete MAX discovery and the unlabeled-root invariant first exclude a
  current-length augmentation. That strict bound then supplies eligible base
  existence for the fixed matching throughout the recorded loop. No
  intermediate high-tenacity bottleneck or circular base premise is assumed.
- **MIN and weighted predecessor routes:** an independent pass checked that
  the selected predecessor comes from the actual list, its honest prefix label
  is available from prior MIN/MAX completeness, and fiber separation proves
  simplicity. Semantic shortest-path witnesses supply only proofs, not runtime
  vertices. Newly assigned MIN vertices receive computed singleton arms.
- **Executable recovery:** independent inspection checked stored-parent
  traversal, predecessor-list selection, parity bridge joining, old-route
  extension and new MAX routes. Runtime definitions contain no choice-based
  path selection, unsafe implementation substitution or native-decision proof
  shortcut. The ordinary foundational axiom footprint is audited separately.
- **Whole single-path search:** independent inspection checked equality of
  recoverable and original bucket outcomes/history, threshold advancement,
  initialization and the finite stopping test. A simple path has fewer than
  `n` edges, so the stop test cannot discard an augmenting path at its proved
  lower bound.

## Executed examples

Guarded evaluations cover an empty graph, perfect matchings, free edges,
augmenting lengths three and five, two successive same-level petals, stored
tree recovery after an abandoned DDFS branch, and recursive deletion cascades.
The triangle-with-tail example recovers a real length-five matching path after
one earlier petal and executes its augmentation to cardinality three.

## Boundary at the time of review

`PetalRecord` certifies full-predecessor-graph DDFS. It cannot certify a
restricted-graph bottleneck after deletion without new active-graph invariants.
Generic pruning preserves live bottom paths, but matching-fiber avoidance and
maximal-family exhaustion are additional obligations. In particular, the
current weighted recovery API supplies expanded-vertex-to-core containment;
the converse core-in-recovered-path fact needed for a root-closure deletion
argument had not yet been added at this review snapshot. These obligations
are now discharged by `RecoveryContainment`, `ActivePetalState`,
`BlockingBucketRemoval` and `BlockingPhase`, as recorded in BLOCKING_PHASE_PROOF.md.
