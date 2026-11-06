# Follow-up proof review

This is a historical component-review record. Its open obligations describe
that review's source snapshot; the completed solver and current validation
are recorded in [CHECKPOINT.md](CHECKPOINT.md) and [VALIDATION.md](VALIDATION.md).

This review covers the new mathematical and operational developments added
after the initial project snapshot. The final reproducibility manifest in
`validation/source-hashes.json` records the delivered source versions.
Successful checks below do not establish the remaining full MV theorem.

## Independent statement checks

- The phase-proof agent reviewed `DDFSCertificate`, `DDFSAltPath`, and
  `BridgePath` against source pp.6–8 and p.25. Actual root reachability is
  required. The per-vertex linkage permits its orientation to depend on
  the vertex. It does not assert a globally colored spanning-tree output.
  The detour derives simplicity and its exact alternating-path length.
- The DDFS agent reviewed `PhaseProgress` and `PhaseDriver`.
  The strict-progress proof uses actual flips and a proved decomposition.
  Empty families and `n=0` are covered. `Complete` is needed for maximum
  output. At that snapshot the concrete phase had not yet discharged the
  search contracts; `BlockingPhase` now supplies that connection.
- The coordinating agent checked the minimum-tenacity common-base proof's
  induction and read `BaseUnique` and `MinimumBase`. The smaller-minlevel
  premise is discharged by strong induction. The final theorem has no
  common-base oracle premise. The proof treats all roots simultaneously.
- The phase-proof agent checked `MinimumBridgeAll` and `MatchedLevels`.
  The appended terminal matched edge in the odd-maxlevel case is proved
  to be a prop. Uniqueness among **all** bridges is appropriate only for
  this globally minimum-tenacity theorem; the general source target asks
  for uniqueness among bridges **of the endpoint's tenacity**.
- The phase-proof agent reviewed `IsBase`, `Blossom`, and the source-recursion
  integration in `BlossomLaminar` against Definition 6.8 and §7. The
  laminarity theorem retains the valid-root tenacity restrictions. A
  functional partial base relation does not prove general base existence.
- The phase-proof agent reviewed `SegmentSplice` and `RelativeShortest`.
  Competing relative paths may intersect the prefix. The first-intersection
  argument handles these cases explicitly. `segment_avoids_prefix` uses
  semantic shortestness of the proposed total length; it does not assume
  that the proposed concatenation is already a valid path.
- The phase-proof agent reviewed `DDFSMachine` and `DDFSTermination`.
  Restoration after failed red recovery is paid for by the mode-credit
  decrease. Every scan consumes an unexplored ordered pair; every pop
  requires a nonempty stack. Well-foundedness applies to the actual
  transition relation and excludes infinite executions.
- The coordinating agent read the mode invariant, double-exhaustion cut
  argument, progress case split and `DDFSCorrectness` assembly. Output
  correctness is derived from initialization and preservation of every
  allowed step. `exists_correct_run` assumes only the source layered graph
  and bottom reachability, with a finite vertex type. It does not take an
  invariant, coverage or progress oracle as a caller premise.
- The phase-proof agent independently reviewed the final DDFS correctness
  assembly against source pp.6–8, including red-failure Barrier restoration,
  green-failure closure and highestness. Two kernel-checked transition traces
  exercise collision/backtracking/escape and double failure with restoration.
  The latter leaves the region below the candidate bottleneck unvisited.
- The base/blossom agent independently reviewed `RelativeJoin` and
  `MinimumRelative`. The concatenation theorem derives simplicity without
  assuming prefix disjointness, and the minimum-tenacity confinement theorem
  applies to every shortest relative path with the specified endpoints/parity.
- The base/blossom agent independently reviewed `DDFSVisited`. Discovery
  provenance, closure away from the bottleneck, and depth all follow from
  machine reachability. The region theorem matches the union of all
  root-to-bottleneck path vertices, including the bottleneck; it does not
  assert a global coloring or the MV support correspondence.

No proof defect was found within these stated scopes. Reviews did identify
two documentation/refinement boundaries: the partial semantic base function
tests existence, not whether a proof has been written; and the DDFS equal-root
bottleneck branch must become immediate abort/no-new-petal in the MV wrapper.
The corresponding definition comments were corrected or clarified.

## Source and trust boundary

The source remains the supplied arXiv:2012.03582v1 PDF, dated 7 December 2020.
The proof files expose all input graph properties and search contracts.
Central theorem audits reported only `propext`, `Classical.choice`, and
`Quot.sound`. The final source-only build and kernel replay cover all public
declarations, including dependencies of private helper proofs.

The subsequent structural induction is recorded in `STRUCTURAL_OBLIGATIONS.md`.
The concrete phase and solver correctness are covered separately in
`BLOCKING_PHASE_PROOF.md`.
