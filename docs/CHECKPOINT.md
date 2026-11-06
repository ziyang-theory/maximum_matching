# Paused proof checkpoint

Work is paused at the user's request. The full goal remains unfinished: prove
the concrete Micali–Vazirani phase, its search contracts, and its implementation
costs. This checkpoint saves completed proofs and the next integration steps.
No admitted proof or new correctness axiom is used.

## Completed in this checkpoint

- `PetalRootExpansion` and `CurrentBridgeRepresentation` preserve actual
  fiber segments and every current bridge's endpoint arms through a petal
  merge. The invariant contains path witnesses and exact phase/length budgets,
  rather than support membership or an assumed MAX postcondition.
- `CurrentBridgePath`, `CurrentBridgeSupport` and `PetalCurrentMax` derive
  support soundness, shortest augmentation, and actual MAX/refresh correctness
  throughout one fixed search level. MIN labels and predecessor lists stay
  unchanged during MAX, permitting representation transport.
- `CurrentBucket` executes a supplied list of queued current bridges. It skips
  equal buds, calls DDFS on distinct buds, performs actual MAX and contraction,
  and records each actual petal. Representation witnesses are erased proofs;
  returned paths are raw computed DDFS paths. The triangle example forms one
  petal, with roots `[0,0,0]` and maxlabels `[none, some 2, some 2]`.
- `CurrentBucketProgress` proves trigger roots merge at each petal and that
  existing bud classes never split during the whole loop, including early
  stopping. It does not yet prove the exhaustion postcondition.
- `SupportBridgeGeometry`, `SupportPathEdges`, `SupportPathCompression` and
  `SupportBridgeRoots` construct two disjoint actual predecessor-graph arms
  from a semantic maxlevel support witness. `MatchingSupportComplete` derives
  strict bottleneck-region membership under lower-blossom representation,
  including the threshold equal to the shortest augmenting-path length.
- `DDFSPathMap`, `PetalPathTransport` and `PetalDisjointTransport` transport
  actual old paths across a petal, with exact vertex-image sets. Disjointness
  is preserved when one arm ends outside the selected region and the other
  reaches bottom.
- `ParityBridgeJoin` supplies simple parity/relative bridge joins without a
  free-boundary assumption; the existing free-boundary join uses this result.

## Next proof steps

1. Prove that an exhausted `runCurrentBucket` result has equal final roots for
   both endpoints of every supplied trigger. Induct over the supplied list:
   use `PetalRecord.after_trigger_equal` for a petal and
   `runCurrentBucket_root_congr` to preserve that equality through the tail.
   The early disjoint branch contradicts an exhausted-result hypothesis.
2. Extend `PetalRecord.transport_disjoint_paths` to the surviving-target case
   `p.last = R.bottleneck`. Its current hypothesis is strictly
   `¬ R.selected p.last`. The helper `selected_path_contains_bottleneck`
   already handles either equality to the bottleneck or an outside target.
3. Combine the initial support arms from
   `BudGraphInvariant.support_graph_arms` with repeated actual contraction
   transport, and transport across unchanged MIN fields after MAX. Derive
   complete current-tenacity MAX discovery from bucket exhaustion, rather
   than supplying the desired vertex list as a premise.
4. Identify final roots with mathematical bases and restore the lower-blossom
   representation for the next level. Intermediate buds may have current
   tenacity; imposing higher tenacity on every intermediate bottleneck is
   invalid. Current fixed-tenacity bridge arms alone do not prove the
   next-cutoff representation.
5. Implement matching-path recovery from the stored computed certificates
   and petal history, safe removal, and maximal shortest-family discovery.
   `CurrentBucketWitness.shortest_augmenting` is an existence/soundness theorem,
   not executable matching-path recovery.
6. Instantiate `PhaseDriver.Complete` and `ShortestBlocking`, then establish
   concrete representation costs. The existing local DDFS transition bound
   does not charge finite adjacency enumeration, reconstruction or storage.

## Review and validation

Independent reviews covered same-stage expansion, support compression,
actual contraction transport, MAX invariants, executable proof erasure,
computed-result provenance and loop monotonicity. The stated transport and
exhaustion gaps are retained explicitly above. Completed modules are all
imported by `MaximumMatching.lean` and checked by `scripts/verify.py`.
The final source-only build, all-public-declaration axiom audit and bundled
Lean kernel replay are recorded in `validation/summary.json`, with exact
source/configuration hashes in `validation/source-hashes.json`.
This snapshot passed 173 build jobs, audited 1,439 public declarations using
only `propext`, `Classical.choice` and `Quot.sound`, and passed kernel replay.

A discarded, incomplete duplicate path-contraction draft was retained locally
in ignored `.cache/proof-work/PetalPathContraction-paused.lean`; the completed
transport modules supersede it. It is not part of the committed Lean source
or a dependency needed to resume.
