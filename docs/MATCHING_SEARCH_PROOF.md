# Matching-state search: checked connection and remaining boundary

The predecessor/bud graph of source §4.3 is now constructed from actual MIN
state, and executable DDFS and MIN updates preserve its operational invariant.
Under a lower-blossom input representation, actual DDFS linkages give support
members and shortest augmenting paths. This is a local connection; a complete
MV phase and its running-time theorem remain unproved.

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
members. Constructing and preserving its segments through new same-level
petals remains necessary.

## Remaining proof obligations

- Preserve the path/fiber representation through a sequence of same-level petal
  events; an intermediate bud may have the current tenacity.
- Prove converse support coverage and complete current-tenacity discovery.
  `SupportBridgePrefix` proves honesty at the trigger endpoint even when it is
  low; `SupportPathReverse` constructs real reverse predecessor witnesses for
  descending stretches. These are inputs to the unfinished compression proof.
- Identify final bud roots with canonical bases at the end of the search level.
  `GeneralBasePathTransfer` proves the relevant canonical-base transfer from
  actual shortest-path geometry, not from a supplied support assertion.
- Complete recursive path extraction/removal and maximal shortest-family
  discovery, then instantiate `PhaseDriver.Complete` and `ShortestBlocking`.
- Implement and account for the efficient representation. Current finite
  enumeration and reconstruction do not have the full MV running-time bound.

Target builds and independent statement/proof reviews cover these modules.
The complete source-only build, all-public-declaration axiom audit and bundled
kernel replay are recorded with final source hashes in `validation/`.
