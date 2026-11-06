# Operational DDFS path and bottleneck outcomes

The finite stack transition system now has a checked total-correctness proof for its two path/bottleneck outcomes. It follows the collision and Barrier control rules in §2, pp.6–8 of the supplied paper. Deterministic edge enumeration and globally colored spanning-tree output are also executable and proved.

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

No discovery-provenance, visited-region, or coverage hypothesis is supplied by the caller. This exact searched region is a prerequisite for later MAX support integration; it does not itself identify the corresponding contracted matching graph. The coloring is now constructed from this region as described below.

## Termination

`DDFSTermination.lean` assigns a natural rank to every finite state. It counts unexplored ordered vertex pairs, multiplied by `4*n+6`, then adds stack lengths and mode credit. Normal, red-recovery, and green-recovery credits are `2*n+3`, `n+2`, and `1`. Terminal credit is zero. Each scan consumes a previously unexplored pair; each pop shortens a stack; and the red-failure credit decrease pays for restoring its saved prefix. `step_rank_lt` proves a strict decrease for every transition, even from states not known reachable.

`step_wellFounded` and `no_infinite_run` derive termination from this strict
rank decrease. The executable search uses the same well-founded recursion.

## Executable search and colored trees

`DDFSExecutable.lean` carries decidable visited/explored predicates with each
state and selects the first unscanned outgoing neighbor in increasing `Fin n`
order. `next` returns an actual transition or terminal proof. `execute` recurses
on the proved decreasing rank; reachability and rank are used only in erased
proofs. Its result includes the counted trace and correct final outcome.

`DDFSTrees.lean` seeds one parent/color forest from the two saved collision
paths, excluding their shared bottleneck. It then repeatedly attaches an
uncolored visited vertex through an edge from a colored vertex. Every attachment
preserves the existing colors and parents and decreases the uncolored count.
At saturation, the exact visited-region theorem supplies a root-to-vertex
prefix avoiding the bottleneck; closure colors that whole prefix, proving
coverage. Each tree then adds its own saved final edge into the bottleneck.
The parent functions are globally consistent, not independently selected paths.
`ColoredTrees.cover` and `overlap` prove union and exact intersection.

`executeFull` returns either actual disjoint bottom paths or the highest
bottleneck with these stored trees. Equal roots and either root equal to the
bottleneck are supported. Permanent examples exercise an abandoned visited
branch absent from both final saved paths, as well as zero-length root trees.
The selector enumerates vertices and reconstruction searches vertex pairs.

## Trust

The central correctness theorems are ordinary kernel-checked proofs. Their axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`; no custom axiom or `sorryAx` is used. Mathematical choice appears in erased abstract witness and termination proofs. Executability of the new definitions is separately checked through compiled fixtures.
