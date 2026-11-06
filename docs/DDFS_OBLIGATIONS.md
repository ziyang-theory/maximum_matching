# DDFS operational obligations

Source: `max_matching.pdf`, SHA-256 `05f3cfcc51c12eea0537cb9892a9bc832f8f175fc507b2b0f8228b68e922996c`, §2, pp.6–8. This note concerns reconstructing operational details and invariants. It is not a counterexample to the MV algorithm or to Theorem 2.1.

## A literal ordinary-DFS translation gets stuck

The normal-DFS paragraph on p.7 says to skip an already visited successor. The collision paragraph then describes both activity centers meeting and transfers ownership. The collision handling must override the visited-successor skip; otherwise that event is unreachable when visiting a vertex immediately marks it visited.

The smallest example with two distinct roots and a common lower vertex has three vertices:

```text
level 1: r       g
          \     /
level 0:     b
```

Edges are `r → b` and `g → b`. All vertices reach level zero. The scheduling rule first moves red from `r` to `b`, marking `b` red. Green then scans `g → b`. If it literally skips every visited successor, it exhausts the green root without ever entering the collision branch. An ordinary “backtrack to parent” operation has no parent there. The correct result is the highest bottleneck `b`.

This is a reproducible obstruction to that naive translation, not evidence of a false graph-theoretic claim. The paper expressly announces an exception to normal DFS before giving collision handling; the implementation must make this exception precise.

## Recoloring is necessary, not just collision detection

Use vertices `r,g,s,a,b`, layers `2,2,1,0,0`, and edges:

```text
r → s       g → s
r → a       s → b
```

Starting with red's edge `r → s`, the next green step reaches the red activity center `s`. Two vertex-disjoint root-to-bottom paths nevertheless exist: `r → a` and `g → s → b`. Thus `s` must not be declared a bottleneck merely because green's only outgoing edge reaches a red vertex. Red can relinquish `s` and find the alternative edge `r → a`.

This graph is implemented in `MaximumMatching/DDFS.lean`, namespace `OwnershipExample`. Lean checks:

- `reaches_bottom`: every vertex reaches layer zero.
- `solutions_disjoint`: the two displayed solution paths share no vertex.
- `no_bottleneck`: no vertex is a bottleneck for these roots.
- `green_successors_owned`: every available green successor is already on red's collision prefix `r → s`.

These statements separate a real allowed graph from an imagined failing tactic. They do not certify an implementation of DDFS. The three-vertex stuck trace above is a direct hand execution of the explicitly described naive transition rule; the five-vertex structural facts are machine-checked.

## Checked operational resolution

`DDFSMachine.lean` now makes collision handling precede a visited skip, saves both collision paths, backtracks red only down to its Barrier, restores the saved red path when red fails, moves Barrier to the collision, and then attempts the green escape. It includes immediate equal-root termination and distinguishes normal search, both recovery modes, and terminal outcomes.

`DDFSInvariant.lean` proves the actual visited/frontier coverage invariant through every transition. In particular, restoration of the red prefix derives its exhaustion from prior coverage and saved-path separation; it does not introduce an assumed closure certificate. `DDFSCut.lean` turns the resulting closed search region into a bottleneck proof, and the saved paths establish highestness. The normal scheduling invariant proves that a visited normal-mode successor can only be the other activity center.

`DDFSCorrectness.exists_correct_run` proves a finite actual transition trace to a correct terminal outcome. `maximal_trace_correct` covers every finite maximal execution, and `DDFSTermination.no_infinite_run` excludes infinite executions. These theorems require the source's bottom-reachability condition and derive coverage, progress, and output correctness internally. `DDFSVisited.lean` additionally proves that the final visited region is exactly the union of all root-to-bottleneck path vertices, deriving discovery provenance from the run. See [DDFS_OPERATIONAL_PROOF.md](DDFS_OPERATIONAL_PROOF.md) for the proof and its exact interfaces.

## Remaining refinement and cost obligations

The checked machine returns actual disjoint bottom paths, or the highest bottleneck with two saved root-to-bottleneck paths meeting only there. It does not yet construct the globally consistent coloring and two spanning trees in the full §2 output representation. The individual-vertex path certificate is proved independently, but its witnesses are not a stored global pair of trees.

Edge selection is represented by a nondeterministic transition relation with an explicit unexplored-edge guard. A concrete executable adjacency representation and a verified selection loop remain to be instantiated. Its finite-state rank proves termination using a coarse ordered-pair budget, not the claimed local linear runtime. Once-per-color backtracking accounting, the Barrier history argument, and costs of the chosen data structures remain separate obligations.

For MV integration, equal roots in the layered graph give a mathematical bottleneck immediately. When both bridge endpoints have the same current bud, the matching algorithm must map this case to the §4.3 abort with no new petal. The wrapper, graph construction after blossom contraction, and its support/expansion invariants are additional MV obligations.
