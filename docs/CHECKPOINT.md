# Proof checkpoint

Deletion-aware maximal blocking-phase correctness and the concrete maximum
matching solver are now proved. The implementation uses actual MIN/MAX/DDFS
search, computed petal expansion, path-fiber deletion and recursive predecessor
pruning. No admission or new correctness axiom is used. This repository covers
correctness and termination.

## Completed integration

- `RecoveryContainment` proves that each recovered path contains both compressed
  cores and is closed under current bud lookup. This strengthens the computed
  recovery routines while retaining their previous APIs.
- `AugmentingPathArms` and `CurrentBucketBottomArms` retain original shortest-path
  vertex containment through initial compression and the full search prefix.
- `ActiveSearchGraph` and `ActiveSearchInitial` initialize live fixed roots and
  the restricted predecessor graph with proved bottom reachability.
- `ActivePetalRecord`, `ActivePetalPaths`, `ActivePetalMax`, `ActivePetalArms`,
  `ActivePetalTransport` and `ActivePetalState` handle actual restricted-graph
  events. MAX soundness uses lifted colored-tree linkages; it never assumes a
  full-graph bottleneck from a restricted-graph output.
- `ActivePathRecovery` computes augmentations in live fibers, with root closure
  and both trigger roots on the recovered path.
- `BlockingBucketRemoval` proves deletion and recursive pruning preserve the
  contained bottom arms of every disjoint shortest augmentation.
- `BlockingBucketAccounting`, `BlockingBucketResult` and `BlockingBucket` prove
  actual continued-search termination, pairwise disjointness, shortest lengths,
  persistent inactivity, trigger accounting and maximality.
- `BlockingPhaseStart` retains the first actual witness and current state.
  `resumeBlockingPhase` expands it once, deletes its fibers and continues the
  same bucket without restarting MIN or searching residual matchings.
- `blockingPhase_complete` and `blockingPhase_shortestBlocking` discharge both
  concrete outer-loop contracts. `maximumMatching_isMaximum` proves solver
  optimality. The recursive search and outer augmentation loop both terminate.

See [BLOCKING_PHASE_PROOF.md](BLOCKING_PHASE_PROOF.md) for the proof invariant,
independent review scope, and the exact relation of fiber deletion to source
§4.5.2 and Lemma 8.5.

## Representation scope

The live graph deletes whole touched root fibers, and may retain isolated
level-zero roots. Safety and maximality are proved for this representation;
exact intermediate-state equivalence to literal source vertex deletion is not
claimed. The algorithm's correctness and termination require no further
implementation changes.

## Verification

All delivered modules are explicitly imported by `MaximumMatching.lean`.
`BlockingPhaseExamples` includes two successive augmentations in one phase,
a subsequent active petal contraction, recursive removal of an unused matched
branch, recovery through an earlier petal, and full-solver boundary cases.

The source-only build, public-declaration axiom audit and bundled Lean kernel
replay are recorded in `validation/summary.json`, with exact source hashes in
`validation/source-hashes.json`. These checks cover phase and solver correctness
and termination.
