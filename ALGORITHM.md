# Where MV's algorithm appears in the code

The phase driver, MIN update, MAX bucket loop, and DDFS transitions are defined
in separate modules. Many other modules prove the graph-theoretic facts used
by the search. The call path below shows how the executable definitions fit
together, and the table maps them to the paper.

The code follows MV's MIN/MAX/DDFS search, with the implementation choices
described below. Its correctness and termination are proved in Lean.
The correspondence with the paper still requires source review: there is no
whole-program equivalence proof to a separate formalization of the pseudocode,
and the paper's running-time bound is not proved here.

The reference is Vijay V. Vazirani,
[*A Proof of the MV Matching Algorithm*, arXiv:2012.03582v1](https://arxiv.org/abs/2012.03582v1),
7 December 2020. All paper links use this
[PDF version](https://arxiv.org/pdf/2012.03582v1); printed and PDF page numbers
coincide.

## 1. The executable call path

[`Search.maximumMatching`](MaximumMatching/BlockingPhase.lean#L762) starts from
the empty matching and calls
[`PhaseDriver.run`](MaximumMatching/PhaseDriver.lean#L622) with
[`Search.blockingPhase`](MaximumMatching/BlockingPhase.lean#L745).
The driver augments along each returned family and repeats until it receives
an empty family. Each phase runs the following search:

```text
blockingPhaseResult                         BlockingPhase.lean
  freeEdgePhase                             ShortestAugmentingSearch.lean
    if nonempty: return the length-one family
    otherwise:
      firstHigherState + firstHigherArms
      locateBlockingPhase                   ShortestAugmentingSearch.lean
        prepareCurrentBucket                CurrentBucketStage.lean
          scanLevelWithBuds → scanLevel      MatchingSearchGraph / MinComplete
            scanCandidates → scanCandidate → scan       MinScan.lean
        runRecoverableBucket                RecoverableBucket.lean
          DDFS.Machine.executeFull          DDFSTrees.lean
            execute → executeFrom → next    DDFSCorrectness.lean
          bottleneck: update MAX labels, contract petal, retain routes
          disjoint paths: retain the witness and current search state
        exhausted bucket: advance to the next MIN/MAX level
      resumeBlockingPhase                   BlockingPhase.lean
        recover first path; remove its bud classes
        runBlockingBucket                   BlockingPhase.lean
          continue DDFS on the surviving graph in the same bucket
          recover more paths and remove their bud classes
```

`maximumMatching` calls `locateBlockingPhase`; `findShortestAugmenting` is a
separate interface. Keeping the search state lets the solver collect more
disjoint paths in the same phase. The matching and MIN labels stay fixed during
collection. Once collection finishes, `AugmentingFamily.run` flips the
matching edges along its paths.

## 2. Paper-to-code map

Names in this table are in `MaximumMatching.Search` unless qualified otherwise.
The links lead to the definitions that perform each operation.

| Paper location / operation | Lean definitions to inspect |
| --- | --- |
| §4, p.11: initialize a phase | [`State`, `initial`](MaximumMatching/MinScan.lean#L14): labels, predecessor lists, scanned edges, props, bridges, and tenacity buckets. `none` represents an unknown/infinite label; free vertices start at `some 0`. |
| Algorithm 1, p.13, MIN: choose eligible edges | [`scanCandidate`](MaximumMatching/MinScan.lean#L75) checks adjacency, the current parity label, and matched/unmatched parity. [`scanLevel`](MaximumMatching/MinComplete.lean#L418) supplies all ordered vertex pairs. |
| Algorithm 1, MIN: prop or bridge | [`scan`](MaximumMatching/MinScan.lean#L62) tests whether the edge was scanned; [`admits`](MaximumMatching/MinScan.lean#L48) implements the non-strict level comparison. The prop branch sets the label and records a predecessor; the bridge branch calls `enqueue` with `edgeTenacity`. |
| Algorithm 1, MAX: process `Br(2i+1)` | [`locateBlockingPhase`](MaximumMatching/ShortestAugmentingSearch.lean#L706) selects `B.state.bucket (2 * i + 1)` after MIN. [`runRecoverableBucket`](MaximumMatching/RecoverableBucket.lean#L376) skips equal bud roots and runs DDFS on the others. |
| §2, pp.5-8: DDFS | [`DDFS.Machine.next`](MaximumMatching/DDFSCorrectness.lean#L621) selects a transition; [`executeFrom`, `execute`](MaximumMatching/DDFSCorrectness.lean#L724) run successive transitions. [`executeFull`](MaximumMatching/DDFSTrees.lean#L659) returns disjoint bottom paths or a highest bottleneck with colored trees. |
| §4.3, p.16: predecessor edges and current buds | [`budEdge`](MaximumMatching/MatchingSearchGraph.lean#L28) and [`predecessorGraph`](MaximumMatching/MatchingSearchGraph.lean#L114) define the layered graph used by DDFS from stored predecessors and current forest roots. |
| §4.2, pp.14-15: form a petal and update buds | [`PetalRecord.after`](MaximumMatching/PetalRecord.lean#L96) merges selected roots into the bottleneck through `BudForest.mergeManyInto`. The record keeps the trigger bridge and DDFS output. |
| Algorithm 1, MAX: assign maxlevels and queue newly known bridges | [`PetalRecord.maxEvent`](MaximumMatching/CurrentBridgeRepresentation.lean#L403) processes the new support vertices. [`maxProcessVertex`](MaximumMatching/MaxBridgeRefresh.lean#L570) calls `assignMax`, then refreshes incident edges for an inner vertex. |
| §4.5.1, pp.17-18: recover an augmenting path | [`CurrentBucketWitness.recover`](MaximumMatching/OperationalArms.lean#L526) expands the DDFS witness using stored `OperationalArms`. Later paths use [`ActiveSearchState.recoverLivePath`](MaximumMatching/ActiveSearch.lean#L139). |
| §4.5.2, pp.18-19: removal and continuation | [`resumeBlockingPhase`](MaximumMatching/BlockingPhase.lean#L691), [`ActiveSearchState.remove`](MaximumMatching/ActiveSearch.lean#L270), and [`runBlockingBucket`](MaximumMatching/BlockingPhase.lean#L608) delete whole bud classes and continue the search, as described below. [`DDFS.RecursiveRemoval.remove`](MaximumMatching/RecursiveRemoval.lean#L192) performs predecessor pruning. |
| §4, p.11: repeat phases and augment | [`blockingPhaseResult`](MaximumMatching/BlockingPhase.lean#L731) returns the family; [`PhaseDriver.run`](MaximumMatching/PhaseDriver.lean#L622) applies it and repeats. |

For a short example, compare
[Algorithm 1's MIN branch (p.13)](https://arxiv.org/pdf/2012.03582v1#page=13)
with `scan`. At search level `i = 0`, suppose an eligible edge from a free vertex
has not been scanned. If the neighbor's level is unknown, the scan assigns it
level `1` and records the source as a predecessor. If the neighbor already has
level `1`, `admits (some 1) 1` is true, so the scan records another predecessor.
If the neighbor has level `0`, the scan takes the bridge branch. The theorem
[`scan_tie_adds_predecessor`](MaximumMatching/MinScan.lean#L127)
proves the tie case.

For MAX, `maxProcessVertex` assigns `t - lo` when the stored minlevel is `lo`.
The bucket loop supplies `t = 2 * i + 1`. Refreshing incident edges uses the known
labels and prop status, without searching for alternating paths to decide the
semantic `Bridge` predicate.

## 3. Runtime data and proofs

`DDFSMachine.lean` defines the transition relation
[`DDFS.Machine.Step`](MaximumMatching/DDFSMachine.lean#L593).
The executable functions are in `DDFSCorrectness.lean`: `next` selects a
transition and `execute` runs the search. Each selected transition carries a
proof that it is a `Step`.
[`Execution.trace`](MaximumMatching/DDFSCorrectness.lean#L716) certifies the
resulting sequence of transitions.

Search records contain both data and proofs. The solver computes labels,
buckets, forest pointers, DDFS paths, and `OperationalArms`. Proofs of soundness,
completeness, and termination are erased for execution. The solver recovers
paths from stored routes, without an augmenting-path oracle or enumeration of
all augmenting paths. Noncomputable definitions support the structural and
termination proofs; they do not choose the runtime search steps.

There are two versions of the current-bucket loop:

- [`runCurrentBucket`](MaximumMatching/CurrentBucket.lean#L124) exposes the search
  decisions and raw witness.
- [`runRecoverableBucket`](MaximumMatching/RecoverableBucket.lean#L376) carries
  the extra route data needed to construct the original-graph path.

[`runRecoverableBucket_erase`](MaximumMatching/RecoverableBucket.lean#L422)
proves that erasing the extra route data gives the same result as the raw loop.
This equality relates the two Lean implementations. The comparison with the
paper remains the source review described above.

## 4. Implementation choices and limits

- MIN enumerates all ordered vertex pairs and filters by adjacency. MAX's
  incident refresh also uses finite enumeration.
  DDFS chooses the first available neighbor in increasing `Fin n` order.
  The forest and path representations were chosen to support the correctness
  proofs. No time or space bound is proved for this implementation, so these
  choices provide no evidence for MV's asymptotic running time.
- After the DDFS machine reaches a bottleneck,
  `executeFull` calls [`reconstructTrees`](MaximumMatching/DDFSTrees.lean#L584).
  This separate finite pass builds colored trees from the terminal search data.
  The paper maintains these trees incrementally during DDFS.
- [`freeEdgePhase`](MaximumMatching/ShortestAugmentingSearch.lean#L156) handles
  length-one paths with a greedy free-edge scan. Higher search levels use
  MIN/MAX/DDFS.
- For a recovered path `p`,
  [`pathRoots`](MaximumMatching/ActiveSearch.lean#L323) collects the current roots
  of its vertices. `remove` deactivates whole classes of vertices with those
  roots, then prunes nonbottom roots without surviving predecessors. Safety and
  maximality are proved for this representation. Equality with the intermediate
  states of the paper's vertex-by-vertex `RECURSIVE REMOVE` is not claimed.
- DDFS terminates by well-founded recursion with an erased rank. Bucket loops
  consume finite lists, and the level search uses the simple-path length bound.
  The outer loop decreases the matching-cardinality deficit. The solver needs
  no user-supplied fuel limit and has no fallback augmenting-path search.

## 5. What the theorems establish

| Declaration | Guarantee |
| --- | --- |
| [`blockingPhase_complete`](MaximumMatching/BlockingPhase.lean#L747) | An empty returned family implies that no augmenting path exists. |
| [`blockingPhase_shortestBlocking`](MaximumMatching/BlockingPhase.lean#L750) | A nonempty family is a maximal family of vertex-disjoint shortest augmenting paths. |
| [`maximumMatching_isMaximum`](MaximumMatching/BlockingPhase.lean#L765) | The returned matching has maximum cardinality for every finite simple input graph. |

The generic theorem `PhaseDriver.run_isMaximum` also applies to other complete
searches, so final optimality alone does not identify MV. That comparison rests
on the search definitions in Sections 1 and 2, the DDFS transitions and
bucket-erasure theorem in Section 3, and the implementation choices in Section 4.
The kernel checks the Lean statements; it does not check this mapping to the paper.

The [README](README.md#build-and-check) gives the build, axiom audit, kernel replay,
and independent runtime-check commands. The exhaustive small-graph tests verify
the returned answers. They do not compare execution traces with MV.
