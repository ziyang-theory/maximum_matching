# Operational DDFS path and bottleneck outcomes

The finite stack transition system now has a checked total-correctness proof for its two path/bottleneck outcomes. It follows the collision and Barrier control rules in §2, pp.6–8 of the supplied paper. Output-local linear abstract transition bounds are also proved. Globally colored spanning-tree output and a concrete executable adjacency/data-structure refinement with running-time costs remain open.

## Interface and outcome

`DDFSMachine.lean` defines a `SearchFrame` containing the active red and green path stacks, visited vertices, explored edges, and red Barrier. Its `Mode` distinguishes normal search, red recovery with saved collision paths, green recovery with those saved paths, and the two terminal outcomes. Each scan explicitly requires a graph edge that has not already been explored. Edge order remains nondeterministic.

The independent `CorrectOutcome` in `DDFSCorrectness.lean` requires:

- In the disjoint case, the actual active stacks are vertex-disjoint paths from the specified roots to layer zero.
- In the bottleneck case, the reported vertex is the highest bottleneck, and the returned saved paths start at the specified roots, end at that vertex, and intersect only there.

`exists_correct_run` constructs a finite transition trace from initialization to a terminal correct outcome for every `LayeredGraph (Fin n)` satisfying the DDFS Requirement. `maximal_trace_correct` proves that every finite maximal execution is correct, independently of its edge choices. `no_infinite_run` excludes infinite executions. The caller supplies neither a coverage invariant nor a search-completeness theorem.

Equal roots produce their common vertex as a mathematical highest bottleneck without an edge scan. The corresponding MV wrapper case in §4.3 must translate this into the same-bud abort with no new petal. This wrapper connection is separate from the layered-graph theorem.

## Normal mode

`NormalSafe` proves that both active stacks are visited, their only possible shared vertex is their common activity center, explored sources are visited, and both centers are unexpanded. Its depth condition states that every other visited vertex has level at least the maximum of the two center levels.

The scheduling rule moves the higher center, using red on a tie. Strict edge descent and the depth invariant imply that an already visited destination can only be the other activity center. Thus collision recognition precedes the visited skip. A normal-mode skip or backtrack is unreachable under this invariant: the selected positive-level center has an outgoing edge by bottom reachability, and none of its outgoing edges has yet been explored.

`advanceRed_safe` and `advanceGreen_safe` prove preservation for the actual stack, visited-set, and explored-edge updates. `normal_move_exists` proves that an enabled move exists before a terminal event. When a move reaches the other center at `b`, every other visited vertex is strictly above `b`.

## Recovery and coverage

Recovery retains the original collision paths while changing the active stacks. Its depth invariant states that every visited vertex except `b` is strictly above `b`. The waiting center stays at `b`, with its outgoing edges unexpanded. A fresh escape at or below `b` restores the normal-mode invariant; a fresh vertex above `b` continues recovery. Skipped edges have visited destinations.

The coverage invariant is

```text
visited(u) ⇒ exhausted(u) or u lies on an active stack,
```

where `exhausted(u)` means that every actual outgoing edge of `u` has been recorded as explored. A separate invariant records that all explored destinations are visited. The Barrier invariant requires that Barrier lies on the red stack and every red-stack vertex strictly above Barrier is exhausted.

A regular pop requires exhaustion. The initial pop of a collision does not: the waiting stack still contains that vertex, so coverage is preserved. Red recovery stops at Barrier. At red failure, the current red prefix is exhausted except possibly `b`, which the green stack retains. Restore the saved red collision path and set Barrier to `b`. `restoreRed_barrier_safe` derives exhaustion of its restored prefix from the old coverage invariant and separation of the saved paths. It does not assume that restored-prefix exhaustion was already proved.

Green recovery then follows the symmetric scan/pop rules, with no red-style Barrier. If it exhausts the green root, every visited vertex other than `b` is exhausted: red's restored prefix is covered by the Barrier invariant, and the remaining green stack is its exhausted root, or `b` itself.

## Terminal bottleneck proof

`closure_at_double_exhaustion` derives a successor-closed visited region away from `b`. Recovery depth shows that `b` is its only possible layer-zero vertex. Since both roots remain visited, any root-to-bottom path must pass through `b`; otherwise closure would keep its endpoint inside this region, contradicting the absence of an alternative bottom vertex.

The saved collision paths establish highestness. Extend each with any bottom-reaching continuation from `b`. A higher common bottleneck would have to lie on both saved prefixes, whose only common vertex is `b`. This proves `green_failure_highest`.

`step_invariant` checks all fifteen transition constructors. `reachable_invariant` derives the invariant from initialization and actual steps. `invariant_progress` checks that every invariant state is terminal or has an enabled transition, including the root, Barrier, zero-length-stack, and equal-root cases.

## Exact visited region

`DDFS.Machine.visited_iff_on_root_to_bottleneck` in `DDFSVisited.lean` proves that a vertex is visited at a reachable bottleneck outcome exactly when it lies on some path from either root to the reported bottleneck. This is the union of the root-to-bottleneck path vertices, including the bottleneck itself.

The proof derives discovery provenance from every actual transition: a newly visited vertex is reached by extending an active rooted stack. It also derives closure and recovery depth at the actual terminating transition. For a visited vertex `u` above `b`, extend its root-to-`u` discovery path by any bottom-reaching path. The proved bottleneck property forces this extension through `b`; depth excludes `b` from the discovery prefix, so truncation supplies a root-to-`b` path containing `u`. Conversely, closure propagates membership along any root-to-`b` path, because every vertex before the endpoint differs from `b`.

No discovery-provenance, visited-region, or coverage hypothesis is supplied by the caller. This exact searched region is a prerequisite for later MAX support integration; it does not itself identify the corresponding contracted matching graph or construct its coloring.

## Termination and cost boundary

`DDFSTermination.lean` assigns a natural rank to every finite state. It counts unexplored ordered vertex pairs, multiplied by `4*n+6`, then adds stack lengths and mode credit. Normal, red-recovery, and green-recovery credits are `2*n+3`, `n+2`, and `1`. Terminal credit is zero. Each scan consumes a previously unexplored pair; each pop shortens a stack; and the red-failure credit decrease pays for restoring its saved prefix. `step_rank_lt` proves a strict decrease for every transition, even from states not known reachable.

The original potential is retained as a coarse termination proof. `DDFSWork.lean` proves a sharper invariant-based bound with potential `4 * unscannedEdges + red.tailDepth barrier + green.length + modeCredit`. The credits are 3, 2, 1 and 0 for normal, red recovery, green recovery and terminal states. Scans consume one actual edge and add at most three local credits. Every other transition decreases local credit; restoring the saved red path places Barrier at its endpoint, so its charged suffix has length zero. Thus every initialized trace has at most `4 * scannedEdges + 3` transitions.

`DDFSLocalWork.lean` proves the source's output-local edge inclusion. Scanned sources have root-discovery paths. Scanned targets have continuations to the bottleneck using the exact visited-region theorem. In the disjoint case, a new invariant keeps every visited bottom at an activity center; coverage and layer descent then supply a continuation to a reported bottom from every visited vertex. Concatenation gives an actual path containing each scanned edge. The resulting bounds are `4 * |E_b| + 3` and `4 * |E_p| + 3`, with edge sets interpreted as unions of root-to-output paths. `DDFSWorkExamples` checks both outcomes on an edgeless graph, where a control transition is still needed.

These count abstract transitions. The development still needs a costed finite adjacency implementation and costs for exhaustion tests, stack/path updates and restoration. It also needs construction and verification of a globally consistent red/green partition and spanning trees if that full §2 output representation is required. The previously checked per-vertex semantic certificate does not by itself provide those data structures.

## Trust

The central correctness theorems are ordinary kernel-checked proofs. Their axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`; no custom axiom or `sorryAx` is used. Mathematical choice appears in abstract witness, termination and potential definitions and does not certify an executable or efficient edge-selection implementation.
