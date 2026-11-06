# Deletion-aware blocking phases

The concrete `Search.blockingPhase` now satisfies `PhaseDriver.Complete` and
`PhaseDriver.ShortestBlocking`. `Search.maximumMatching_isMaximum` therefore
proves maximum cardinality for the executable solver, with only a finite simple
graph and decidable adjacency as inputs. `runBlockingPhases_positivePhases_le_two_sqrt`
proves at most `2 * Nat.sqrt n` positive phases. Concrete running time remains open.

## Live state and actual events

`ActiveSearchState` retains the current matching's MIN/MAX labels, predecessor
lists, bud forest and computed parity arms. Its live list contains fixed bud
roots. DDFS uses the predecessor graph restricted to those roots. Inactive
vertices are represented as isolated layer-zero vertices, so every invocation
explicitly requires both trigger roots to be live. `LiveBridgeArms` includes
these membership conditions as well as disjoint bottom paths.

`ActivePetalRecord` records the actual restricted DDFS output. Its highest
bottleneck and selected-region statements concern that restricted graph only.
Stored colored-tree paths lift to the original predecessor graph; their
linkages establish genuine support membership and sound MAX assignments.
`ActivePetalArms` computes the new parity segments from those stored paths.
`ActivePetalState` rebuilds the semantic representation from those computed
arms and preserves stage invariants, reachability and root bounds. No full-graph
bottleneck conclusion is inferred from a restricted bottleneck.

## Recovery and deletion

The strengthened recovery routines retain two directions of containment:

- The root of every expanded vertex lies on one of the compressed cores.
- Every compressed core vertex occurs on the expanded matching path.

Consequently the recovered path is closed under its current bud map. Its
vertices have live roots, and it contains both trigger roots. `pathRoots`
collects the roots of its vertices. `remove` deletes these root classes and
then repeatedly prunes positive-layer roots with no live predecessor.

This representation can remove more original vertices than literal deletion
of the recovered path alone, because whole current fibers become inactive.
Its safety theorem retains the information needed for maximality: every
shortest augmentation disjoint from the selected family still has two live
bottom arms whose vertices occur on that augmentation. We do not claim equality
of intermediate vertex sets with a literal execution of source §4.5.2.
Isolated layer-zero roots may remain; live-trigger guards prevent false paths.

## Coverage and maximality

`AugmentingPathArms` compresses any original shortest augmentation around its
unique current-tenacity bridge. Both cores reach free endpoints and occupy
disjoint original index intervals. Their vertices are on the original path.
`CurrentBucketBottomArms` transports this containment through the initial
ordinary search prefix. `BlockingPhaseStart` retains the actual first DDFS
witness, current runtime arms, and original complete bridge list.

`resumeBlockingPhase` expands that witness once, removes its root classes,
and continues on the same matching and labels. Scanning the retained list
again only revisits earlier triggers to skip their equal roots; the found
trigger is inactive after deletion. No MIN level or residual-graph matching
search is restarted.

`BlockingBucketResult` proves the following for the actual continuation:

1. Its family consists of pairwise vertex-disjoint augmentations of the
   original shortest length.
2. Every returned vertex has an inactive final root. Previously inactive
   classes stay inactive, and contractions never split old root classes.
3. Every supplied trigger is accounted for: its final roots are equal or
   one is inactive.
4. A shortest path disjoint from the returned family retains its original
   vertex-contained live bottom arms.

For contraction, each new arm is a subset of its old arm: if it enters a
selected region, its original bottom path already contains the bottleneck.
For deletion, root closure makes every forbidden root a vertex of the recovered
path. Disjoint original arms therefore avoid these roots, and the proved
recursive-pruning theorem preserves them.

At exhaustion, a hypothetical shortest augmentation disjoint from the family
would retain two disjoint live arms at one of its queued bridges. Such a bridge
cannot be accounted for. This contradiction proves maximality. The length-one
case uses the existing greedy free-edge phase. Empty higher-level search proves
absence of all augmentations, while a found first witness prevents the resulting
maximal family from being empty. These establish both concrete search contracts.

## Review and validation

Independent subagent reviews checked recovery containment, the live-trigger
requirements, active MAX soundness, initial coverage, contraction/deletion
transport, maximality, and the final contract instantiation. They found no
remaining correctness gap. The review distinguished computed runtime paths
from erased semantic witnesses and checked that the final solver theorem has
no supplied completeness or shortest-blocking premise.

`BlockingPhaseExamples` executes two disjoint length-three augmentations in one
phase, a later active triangle contraction, recursive removal of an unused
matched branch, length-five recovery through an earlier petal, empty and perfect
cases, and the complete outer solver. These runtime checks supplement the
universal proofs. Exact checked source hashes, the source-only build, transitive
axiom report and bundled kernel replay are recorded in `validation/`.
