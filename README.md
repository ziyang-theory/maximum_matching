# Maximum matching in Lean 4

**Executable maximum matching with proved deletion-aware blocking phases.** The development proves correctness of actual MIN/MAX/DDFS search, computed petal expansion, maximal shortest-path families, and the resulting maximum-matching solver. It also proves at most `2 * Nat.sqrt n` positive phases. The concrete MV running-time bound remains unproved.

Source: Vijay V. Vazirani, *A Proof of the MV Matching Algorithm*, [arXiv:2012.03582v1](https://arxiv.org/abs/2012.03582v1), 7 December 2020; supplied as [max_matching.pdf](max_matching.pdf). The exact version and claim map are recorded in [docs/SOURCE_MAP.md](docs/SOURCE_MAP.md).

## Checked results

| Result | Main declaration |
| --- | --- |
| Executable augmentation preserves matching validity and adds exactly one edge | `AltPath.augment`, `AltPath.augment_cardinality` |
| Matching cardinality is half an even saturated-vertex count | `Matching.twice_cardinality` |
| Maximum matching iff no augmenting path (Berge criterion) | `Matching.isMaximum_iff_noAugmentingPath` |
| Execute a supplied disjoint family, gaining exactly its number of paths | `AugmentingFamily.run_cardinality` |
| Matched endpoints have equal tenacity, including infinity (Lemma 5.2) | `matched_tenacity` |
| Both conclusions of limited BFS honesty, all parity/infinity cases (Theorem 5.3) | `AltPath.limited_bfs_honesty` |
| Same-free-root shortest paths of both parities (Lemma 6.9) | `rooted_shortest_even_iff_odd` |
| Common base and unique bridge at minimum eligible tenacity (Lemma 6.13) | `minimum_unique_base`, `AltPath.minimum_maxlevel_path_unique_bridge` |
| Common bases exist at every eligible tenacity (Theorem 6.19(1)) | `general_unique_base` |
| Every shortest relative path stays in its blossom and boundary (Theorem 6.19(4), confinement) | `general_blossom_relative_confined` |
| Each maxlevel path has exactly one bridge of its endpoint tenacity, including `t = l_m` (Theorem 6.19(2)) | `AltPath.general_maxlevel_path_unique_bridge` |
| Relative blossom edges have tenacity at most the cutoff (Theorem 6.19(4)) | `general_blossom_relative_edge_bound` |
| Bases of suffix vertices occur on the original suffix (Theorem 6.19(5)) | `general_suffix_base` |
| Current-tenacity vertices are exactly the union of corresponding bridge supports | `tenacity_iff_bridge_support` |
| Recursive blossoms form a laminar family | `blossoms_laminar` |
| Actual common bases split shortest paths into shortest relative segments | `IsBase.shortest_relative`, `IsBase.append_relative_shortest` |
| DDFS disjoint-path/bottleneck dichotomy and per-vertex linkage certificate | `DDFS.bottom_dichotomy`, `DDFS.highestBottleneck_certificate` |
| Finite DDFS transition system terminates and reports correct paths/bottleneck | `DDFS.Machine.exists_correct_run`, `maximal_trace_correct` |
| Deterministic DDFS constructs either disjoint bottom paths or colored parent trees | `DDFS.Machine.executeFull` |
| Final DDFS visited region equals the root-to-bottleneck path region | `DDFS.Machine.visited_iff_on_root_to_bottleneck` |
| DDFS uses at most `4 * m + 3` abstract transitions, counting edges in its output region | `DDFS.Machine.trace_bottleneck_local_bound`, `trace_disjoint_local_bound` |
| Actual MIN predecessor lists and bud roots define a descending graph reaching free vertices | `Search.BudGraphInvariant.root_reaches_free` |
| Matching-state DDFS and subsequent MIN preserve the operational bud representation | `Search.executeBudSearch_preserves`, `scanLevelWithBuds_invariant` |
| Under lower-blossom representation, DDFS regions give true support members and disjoint paths give shortest augmentations | `Search.BudGraphInvariant.colored_region_support`, `disjoint_bridge_paths_shortest` |
| Actual petal merges preserve path expansion and support soundness throughout one fixed search level | `Search.PetalRecord.afterBridgeRepresentation`, `CurrentBridgeRepresentation.execute_output_sound` |
| Recorded petal events execute MAX assignments and incident refresh correctly throughout that level | `Search.PetalRecord.maxEvent_correct_of_current` |
| Before same-level petals, semantic support witnesses give actual disjoint graph arms and bottleneck-region membership | `Search.BudGraphInvariant.support_graph_arms`, `support_in_bottleneck_region` |
| Executable current-bucket processing preserves stage/path invariants and returns certified raw DDFS output | `Search.runCurrentBucket`, `CurrentBucketWitness.shortest_augmenting` |
| Finite-tenacity bridge endpoint classification (Lemma 8.1) | `matched_bridge_levels`, `unmatched_bridge_tenacity` |
| Weighted high-core paths expand simply and disjointly from witnessed blossom segments | `DDFS.BlossomWeightedMatching.realize`, `realize_disjoint` |
| Maximal shortest families strictly increase augmenting-path length | `AugmentingFamily.shortest_length_increases` |
| At most `2 * Nat.sqrt n` nonempty phases, given the shortest-family search contract | `PhaseDriver.run_positivePhases_le_two_sqrt` |
| Actual DDFS bottleneck regions contract into the reported bud, preserving old classes | `DDFS.Machine.executeAndContract_bottleneck` |
| Bud lookup terminates; compression preserves roots under a rank invariant | `BudForest.root`, `BudForest.compressMany_root` |
| MIN scans retain tied predecessors and never rescan an undirected edge | `Search.scan_tie_adds_predecessor`, `Search.scan_reverse_noop` |
| Finite MIN enumerates every next-level predecessor; initial invariants are proved | `Search.scanLevel_complete`, `initial_scanLevel_complete` |
| MAX updates compute support-member maxlevels and register newly known incident bridges | `Search.maxProcessVertex_correct` |
| Actual MIN queues every current-tenacity bridge under preserved prior-stage invariants | `Search.scanLevel_current_bucket_complete` |
| Exhausting a complete actual bucket discovers every current MAX label and restores the next stage | `Search.runCurrentBucket_exhausted_stageInvariant` |
| Final current-tenacity buds equal canonical bases; the next blossom representation is restored | `Search.runCurrentBucket_exhausted_base_eq`, `runCurrentBucket_exhausted_lower_representation` |
| Consecutive actual MIN/MAX levels decide whether the supplied matching is maximum | `Search.findAugmenting`, `Search.isMaximum_iff` |
| Computed shortest augmenting path, including recursive petal expansion, or certified absence | `Search.findShortestAugmenting` |
| Executable maximal shortest-family construction for length one | `Search.freeEdgePhase_maximalShortest` |
| Recursive predecessor pruning preserves exactly the live paths to bottom | `DDFS.RecursiveRemoval.mem_prune_iff` |
| Restricted-graph MAX events preserve computed routes and surviving disjoint arms | `Search.ActivePetalRecord.afterPetal_liveBridgeArms` |
| Deletion-aware continuation constructs a maximal shortest family | `Search.resumeBlockingPhase_maximalShortest` |
| Concrete phase satisfies both outer-loop search contracts | `Search.blockingPhase_complete`, `blockingPhase_shortestBlocking` |
| Executable maximum matching and unconditional square-root phase bound | `Search.maximumMatching_isMaximum`, `runBlockingPhases_positivePhases_le_two_sqrt` |
| Exact size of the current MIN enumeration, including nonedges | `Search.allCandidates_length` |

The remaining work concerns concrete time and memory costs. The current MIN enumeration has exactly `n * n` candidates, and runtime arm closures and list scans have no linear phase-cost bound. The source's `O(m sqrt(n))` RAM bound is therefore not claimed. [docs/CHECKPOINT.md](docs/CHECKPOINT.md) records that boundary; [docs/BLOCKING_PHASE_PROOF.md](docs/BLOCKING_PHASE_PROOF.md) explains safe fiber deletion and same-phase continuation. No missing result is installed as an axiom.

## Build and check

The project pins **Lean 4.34.0**, imports **Std only**, and has no external package dependencies. With that toolchain installed:

```sh
lake build
python3 scripts/verify.py --lake "$(command -v lake)"
```

In this workspace, the existing concrete toolchain can be used directly:

```sh
python3 scripts/verify.py --lake \
  /Users/ziyang/Documents/github/formal_verification/formal_verification_skills/.cache/lean-4.34.0-darwin_aarch64/bin/lake
```

The verification script copies source/configuration into a fresh temporary directory, builds the aggregate target, reports transitive axioms for public declarations, and runs `leanchecker --fresh MaximumMatching`. Logs and exact source hashes are retained in [validation/](validation/). Kernel replay uses Lean's own kernel and the installed standard-library artifacts; it is not a second independent kernel or a rebuilt toolchain. See [docs/VALIDATION.md](docs/VALIDATION.md).

## Project structure

- `Basic`, `PathLemmas`, `Augmentation`, `Phase`, `Family`: graph/matching representation and actual path operations.
- `SymmetricDifference`, `DifferenceUniqueness`, `Optimality`: complete Berge proof.
- `DifferencePacking`, `PhaseProgress`, `PhaseDriver`, `PhaseBound`: proved packing, phase progress and outer-loop accounting.
- `Levels`, `LimitedHonesty`, `MinimumBase`, `MinimumBridgeAll`: semantic levels and the minimum-tenacity bridge theorem; `GeneralStructureInduction`, `GeneralConfinement`, `GeneralSuffixBase`, `GeneralEdgeBounds`, `GeneralBridge`, `GeneralSupport`: completed general structure and semantic support coverage.
- `Blossom*`, `BaseTree`, `BasePaths`, `Segment*`, `Relative*`: recursive blossoms, laminarity and relative alternating paths.
- `DDFS*`, `BridgePath`: path certificates, lifting, total correctness and local transition counts; `WeightedExpansion`, `WeightedTopExpansion`, `GeneralWeighted*`: weighted segment construction and expansion.
- `Bud*`, `Min*`, `MaxCorrectness`, `Bridge*`: finite MIN enumeration, local MAX updates and bridge scheduling.
- `MatchingSearchGraph`, `MatchingBudStage`, `MatchingDDFSBud`, `PetalRecord`, `PetalMax`: actual matching-state search events and local invariants.
- `MatchingGraphExpansion`, `MatchingBridgePath`, `MatchingSupportSound`, `MatchingBottleneckParity`: lower-blossom path lifting, support soundness and even bottleneck levels; `FiberWeightedExpansion` supplies general fiber-based concatenation.
- `CurrentBridge*`, `PetalRootExpansion`, `PetalCurrentMax`, `CurrentBucket*`: preserved same-stage paths, sound MAX events and executable bucket processing.
- `SupportPath*`, `SupportBridge*`, `MatchingSupportComplete`, `Petal*Transport`: actual support-path compression and contraction transport, with explicit hypotheses.
- `CurrentBucketCoverage`, `PetalBase*`, `CurrentBucketBlossoms`, `CurrentBucketStage`: complete bucket discovery, canonical bases and consecutive-level induction.
- `Operational*Arms`, `OperationalMaxRoutes`, `MatchingPathRecovery*`, `FiberWeightedRecovery`, `RecoverableBucket`, `ShortestAugmentingSearch`: computed parity routes and complete single-path search; `RecursiveRemoval*` supplies the pruning used by the blocking phase.
- `ActiveSearch*`, `ActivePetal*`, `ActivePathRecovery`, `BlockingBucket*`, `BlockingPhase*`: live-graph contraction, safe path deletion, maximal shortest-family search and the concrete solver.
- `Examples`, `DDFSExamples`: kernel-checked boundary cases and actual collision, backtracking and Barrier-restoration traces.
- `docs/`: original step plan, source correspondence, remaining obligations and independent reviews.

Semantic levels use `none` for infinity and mathematical choice to select minima; they are specifications, not the operational MIN/MAX implementation. Augmentation, disjoint-family execution, bud lookup/compression/contraction, finite MIN scans, MAX label updates and full layered DDFS are executable. The current finite enumerations do not have the MV linear-time cost bound. General definitions allow any vertex type; cardinality and the Berge criterion use `Fin n`. Loops and parallel edges are excluded; no normalization theorem for multigraphs is claimed.
