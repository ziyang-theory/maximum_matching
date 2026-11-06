# Matching-state search: checked connection and remaining boundary

The predecessor/bud graph of source §4.3 is now constructed from actual MIN
state, and executable DDFS and MIN updates preserve its operational invariant.
A lower-blossom input representation initializes path witnesses that actual
petal events preserve throughout one search level. The executable current-bucket
loop retains these invariants, and a disjoint output certifies a shortest
augmenting path. Converse support coverage now composes through the loop,
restoring the next blossom representation. Successive levels and computed
petal expansion form a complete single shortest-path search. The full blocking
phase is proved separately in BLOCKING_PHASE_PROOF.md.

The source is the supplied arXiv:2012.03582v1 (7 December 2020), pp.13–19,
33 and 37–40. Exact source hash and locators are in SOURCE_MAP.md.

## Actual graph and state operations

`MatchingSearchGraph.predecessorGraph` uses stored minimum labels as layers.
An edge from an assigned vertex follows a recorded predecessor to its current
bud root. `BudGraphInvariant` consists of the existing MIN correctness/range
invariants, agreement of ranks with labels, and assignment of roots of assigned
vertices. It includes no support or path-expansion conclusion.

MIN completeness supplies every actual predecessor and its smaller minimum
level. Root ranks cannot increase, so graph edges strictly descend; every
positive layer has an outgoing edge, proving bottom reachability. Unassigned
vertices are retained as isolated layer-zero vertices. The free-bottom theorem
requires an assigned starting vertex, and proves that assignment persists
along the path; it does not mistake isolated unknown vertices for free ones.

`MatchingBudStage.scanLevelWithBuds` executes MIN and changes forest ranks to
the new labels while retaining pointers. Old assigned labels do not change;
unknown vertices are fixed, so increasing their ranks preserves every parent
inequality. Actual roots and assignment of represented roots are preserved.

`MatchingDDFSBud.executeBudSearch` executes DDFS on the current graph and merges
exactly its computed bottleneck region. All searched vertices are fixed old
roots. Strict paths to the bottleneck supply the rank guards. The resulting
forest preserves the operational graph invariant.

## Actual paths and support soundness

`LowerBlossomRepresentation` is an explicit mathematical input condition:
every assigned vertex is its own high-tenacity root or lies in the lower
blossom of that root. It is not asserted for forests after arbitrary same-level
petal contractions.

`PredecessorExpansion` extracts actual matching segments from defining
minimum-level predecessor witnesses. `BridgeTopSegments` constructs actual
endpoint-to-bud segments, separating matched and unmatched triggering bridges.
The constructed lengths telescope against stored minimum levels, and phases
are checked for the matching edges rather than inferred from DDFS edge counts.

`MatchingBridgePath` expands disjoint graph paths across the actual trigger.
The result is simple, contains the trigger edge, and has the exact bridge
budget. When both graph paths reach bottom, this is an augmenting path of
trigger tenacity, shortest under `AtMostShortestAugmenting`.

`DDFSColoredLinkage` derives disjoint paths from the actual two color trees for
each selected root other than the bottleneck, extending the opposite arm below
the bottleneck. `MatchingSupportSound` expands this linkage to an actual
maxlevel path through the trigger. A complementary-length argument pins down
the root's current tenacity and proves its semantic support membership.

`MatchingBottleneckParity` proves the bottleneck's minimum level is even. It
allows the bottleneck itself to have current tenacity. An odd root would have
no nontrivial lower-blossom fiber, and every incoming graph edge would come
from its unique matched neighbor. The two color trees then meet above the
bottleneck. Root/bottleneck equality is separately excluded using bridge
classification and equal layers for matched bridge endpoints.

`FirstBridge` handles tenacity one directly: its endpoints are free, and the
actual edge forms a shortest augmenting path. If no length-one augmenting path
exists, a singleton forest satisfies the first lower-cutoff representation.

## Petal records and actual MAX updates

`PetalRecord.recordQueuedPetal` skips equal current buds and otherwise executes
DDFS on a queued, currently known bridge. A bottleneck record retains the exact
prior state, forest, trigger and computed trees. The old fiber map is immutable.
The proved exact root formula changes precisely selected old classes; all
other classes remain unchanged. Stored tree edges retain original predecessor
witnesses for later expansion.

`PetalMax.maxEvent` processes the computed non-bottleneck root list using
`maxProcessVertices`, including incident-edge refresh. Under lower-blossom input
representation, support soundness supplies each processed root's true tenacity.
The actual operation preserves local stage and bud invariants, assigns the
correct maxlevels, and retains prior maxlabels. Lower-tenacity descendants are
not erroneously assigned the current tenacity.

`FiberWeightedExpansion` proves concatenation and disjointness using actual
bud fibers, which are disjoint by root equality. It does not identify petals
with entire mathematical blossoms. `MatchingFiberExpansion` derives this
interface from the lower-blossom representation once MIN covers all lower
members. `PetalRootExpansion` now constructs each new segment by extending an
old edge or bridge-endpoint arm along the recorded old path to the bottleneck.
Its lengths telescope, phases agree, and interior vertices remain in the new
fiber. `CurrentBridgeRepresentation` packages these witnesses for all bridges
at one fixed tenacity, without assuming support membership or MAX correctness.
`afterBridgeRepresentation` preserves it, including arms for unprocessed bridges.
`CurrentBridgeSupport` derives support soundness and shortest augmentation from
this preserved representation. `PetalCurrentMax` verifies the actual MAX event
and transports the representation across its unchanged MIN fields.

## Executable bucket and converse support

`CurrentBucket.runCurrentBucket` processes a supplied finite list of queued
bridges. It skips equal buds, calls DDFS once for each distinct-root trigger,
executes MAX and contraction on a bottleneck result, and retains the actual
petal records. The representation is stored as `Nonempty` in `Prop`; it is
erased rather than used as a runtime oracle. A found result contains the raw
DDFS paths and equality to the exact call that produced them.
`CurrentBucketWitness.shortest_augmenting` proves a corresponding real shortest
augmentation exists; `ShortestAugmentingSearch` now computes that path from the retained operational arms.
`CurrentBucketProgress` proves old bud classes never split during the loop.
The triangle regression executes one actual petal, with final roots `[0,0,0]`
and maxlabels `[none, some 2, some 2]`.

`SupportBridgeGeometry`, `SupportPathEdges`, `SupportPathCompression` and
`SupportBridgeRoots` compress an actual maxlevel support witness into two
actual predecessor/bud graph arms. High-index geometry and lower-blossom
membership derive every graph edge and identify both triggering buds; disjoint
original index intervals establish disjointness. `MatchingSupportComplete`
therefore proves support membership implies strict bottleneck-region membership
under the initial lower-blossom representation, including `t = l_m`.
Its converse combines with the earlier support-soundness theorem under that
theorem's stage-bound hypotheses; no unconditional exact-output wrapper is claimed.

`PetalPathTransport` proves that old fixed-root paths map to actual paths after
contraction, preserving the exact vertex-image set. `PetalDisjointTransport`
preserves two disjoint arms when the first ends outside the selected region
and the second reaches bottom. The surviving-target theorem now also permits the first target to equal the
bottleneck. `CurrentBucketCoverage` composes these transports through the loop.

## Complete single-path search

`CurrentBucketCoverage` proves that every current-tenacity vertex receives its
MAX label after exhaustion. An unlabeled fixed-root invariant then rules out
a current-length augmentation: its free endpoint would be a current-tenacity
root requiring a MAX label. This establishes the next odd lower bound.

`PetalBasePaths` constructs a shortest path with an honest bottleneck prefix.
`PetalBase` identifies either a selected vertex's base with the bottleneck,
or their common base when the bottleneck has current tenacity.
`PetalBaseClasses` transports canonical blossom classes. Together with final
high roots, `CurrentBucketBlossoms` restores the next lower representation and
identifies current-tenacity vertices' final roots with their semantic bases.
`CurrentBucketStage` and `LevelSearch` therefore execute successive actual
MIN/MAX stages without an assumed support-discovery oracle.

The executable refinement retains `OperationalArms`: actual parity segments
from every known label to its current root, with exact lengths and fiber
containment. MIN reuses existing arms or creates new singleton arms. MAX
extends old arms along recovered predecessor tails and computes new maximum
arms from stored colored-tree parents and the trigger bridge. The runtime
choices are list/parent operations; semantic existentials occur only in erased
proofs. `RecoverableBucket` has exactly the original loop's outcome and petal
history after erasure. `findShortestAugmenting` returns the computed shortest
matching path, or certifies no augmentation.

## Blocking-phase integration

`ActivePetalRecord` records actual restricted-graph DDFS events; its highest
bottleneck and region claims are explicitly restricted to the live graph.
`ActivePetalState` preserves computed parity routes and live bottom reachability.
`RecoveryContainment` proves closure of a recovered path under current bud lookup,
and `BlockingBucketRemoval` uses it to preserve contained disjoint shortest-path
arms through actual deletion and recursive pruning. Trigger accounting at
exhaustion establishes maximality. `BlockingPhase` discharges `Complete` and
`ShortestBlocking` for the concrete phase and proves solver optimality.

Independent statement/proof reviews and runtime regressions cover the new
search and recovery modules. The complete source-only build, public axiom
audit and bundled kernel replay are recorded with exact hashes in `validation/`.
