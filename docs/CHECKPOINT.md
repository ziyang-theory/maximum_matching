# Proof checkpoint

The development now constructs a shortest augmenting path with actual
MIN/MAX/DDFS search and computed petal expansion, or certifies that no
augmenting path exists. Full MV blocking-phase construction and its concrete
running-time bound remain unfinished. No admission or new correctness axiom
is used.

## Completed since the previous checkpoint

- `CurrentBucketProgress` proves exhausted-trigger equality and preservation
  of MIN fields and known MAX labels throughout the actual loop.
- `PetalDisjointTransport` handles both surviving targets: outside the selected
  region and equal to its bottleneck.
- `CurrentBucketCoverage` transports initial semantic support arms through
  every actual contraction. Exhaustion discovers all current MAX labels and
  establishes the next `StageInvariant`; no desired support list is assumed.
- `CurrentBucketRootLabels`, `CurrentBucketAugmenting` and
  `CurrentBucketEndRoots` show that roots remain MAX-unlabeled, exhaustion
  excludes a current-length augmentation, and final roots have greater
  tenacity. The exclusion proof uses the free endpoint of a hypothetical
  shortest augmentation, whose current tenacity would force a forbidden MAX
  label at a fixed root.
- `PetalBasePaths`, `PetalBase`, `PetalBaseClasses` and
  `CurrentBucketBlossoms` restore the next-cutoff blossom representation and
  identify final current-tenacity roots with canonical bases. Intermediate
  bottlenecks may still have current tenacity. The strict augmentation bound
  needed for base existence is derived from exhaustion.
- `CurrentBucketStage` executes MIN followed by its complete actual bucket.
  `LevelSearch` iterates these stages with a finite stopping test and proves
  that its maximum-matching decision is exact.
- `OperationalArms`, `OperationalMinArms`, `OperationalPredecessorArms`,
  `OperationalBridgeArms` and `OperationalMaxRoutes` carry actual parity
  segments through MIN, MAX and contraction. `MatchingPathRecovery*`,
  `ParityBridgeRecovery` and `FiberWeightedRecovery` compute paths from stored
  parents/predecessors and concatenate those segments. Semantic choice is
  used only in erased correctness proofs, not to select runtime paths.
- `RecoverableBucket` erases to the same existing bucket execution and petal
  history. `findShortestAugmenting` in `ShortestAugmentingSearch` uses these data
  to return an actual globally shortest augmenting path or certified absence.
  Runtime arm closures retain prior states; compact storage and extraction
  costs are not proved.
- `FreeEdgePhase` constructs a maximal family for the length-one case.
  `RecursiveRemoval` implements repeated removal of live positive-layer
  sinks and proves exact surviving-bottom-path characterization.
  `RecursiveRemovalTransport` preserves avoidance under petal contractions.
- `Search.allCandidates_length` in `EnumerationCost` proves that the present
  MIN candidate enumeration has exactly `n * n` entries, including nonedges
  and loops.

## Remaining integration

1. Continue the shortest-level bucket after recovering a path, with actual
   deletion and recursive removal. Current `PetalRecord.computed`, `highest`
   and `region` refer to the full predecessor graph. A bottleneck in a graph
   restricted to surviving vertices is not automatically a bottleneck in the
   full graph. Introduce an active-graph event and prove its relation to the
   full predecessor edges; do not reuse the stronger full-graph premise.
2. Prove that deleting the recovered path and its affected fibers preserves
   every disjoint shortest augmentation. The generic pruning theorem preserves
   an already-live bottom path; this does not establish the missing matching
   path/fiber compatibility by itself. Keep the two surviving graph arms,
   their original-path vertex containment and the computed expansion's
   avoidance properties in the blocking-bucket invariant.
3. Produce a maximal vertex-disjoint family of shortest paths from that
   continued search, and instantiate `PhaseDriver.Complete` and
   `ShortestBlocking` for the concrete MV phase. A single shortest path, or
   rerunning searches on residual graphs, does not prove the source's
   same-phase removal/continuation procedure or its linear phase cost.
4. Replace all-pairs enumeration, repeated list scans and recomputed path
   closures with an explicit efficient representation and cost model.
   Abstract DDFS transition bounds and the conditional phase count do not
   account for these operations. The present implementation does not have the
   source's `O(m sqrt(n))` RAM bound merely because its proofs compile.

## Verification

All delivered modules are explicitly imported by `MaximumMatching.lean`.
Runtime regressions include multiple successive petals, shortest lengths
one/three/five, a length-five path through an earlier triangle petal, perfect
matchings and the empty graph. Independent reviews checked support coverage,
the noncircular base-restoration argument, stage iteration and the distinction
between executable path data and erased semantic witnesses.

The final source-only build, public-declaration axiom audit and bundled Lean
kernel replay are recorded in `validation/summary.json`, with exact source
hashes in `validation/source-hashes.json`. These checks certify the delivered
development, not the remaining blocking-phase and implementation-cost claims.
