import MaximumMatching.BlockingPhase
import MaximumMatching.BlockingPhaseGraphs
import MaximumMatching.ShortestAugmentingExamples

/-! Runtime regressions for complete blocking phases. These examples execute
MIN, live DDFS, computed expansion, recursive removal, and matching flips.
They supply no augmentation or bottleneck certificate to the solver. -/
namespace MaximumMatching.Examples.BlockingPhase
open Search
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private def vertices {n : Nat} {G : Graph (Fin n)} {M : Matching G}
    (p : AltPath M) : List Nat :=
  (List.finRange (p.length + 1)).map (fun i => (p.vertex i).val)

/- Both shortest paths are collected during one phase and their actual
flips increase cardinality by two. The vertex sequences fix the scan order. -/
/-- info: (2, [[10, 9, 8, 7], [6, 5, 4, 3]], 4, 6) -/
#guard_msgs in
#eval
  let f := blockingPhase matching
  (f.count, (List.finRange f.count).map (fun j => vertices (f.path j)),
    matching.cardinality, f.run.cardinality)

/- The triangle is still uncontracted at the first augmentation. Continued
live DDFS contracts it afterwards. The matched branch 11--12 is initially
live and is recursively pruned after its only predecessor boundary is erased. -/
/-- info: [1, 2, 0, 0, 1, 1, 0, 0] -/
#guard_msgs in
#eval
  let M := matching
  if hz : (freeEdgePhase M).count = 0 then
    let hn := freeEdgePhase_empty_no_short M hz
    match locateBlockingPhase (firstHigherState M hn) (firstHigherArms M hn) with
    | .maximum _ => ([] : List Nat)
    | .found _ _ hc ht hstageTen B A W es hqueued _ =>
      let result := resumeBlockingPhase hc ht hstageTen B A W es hqueued
      [B.forest.root 1, B.forest.root 2,
        result.state.B.forest.root 1, result.state.B.forest.root 2,
        if 11 ∈ ActiveSearchState.initialLive B then 1 else 0,
        if 12 ∈ ActiveSearchState.initialLive B then 1 else 0,
        if 11 ∈ result.state.live then 1 else 0,
        if 12 ∈ result.state.live then 1 else 0]
  else []

/- This phase expands an earlier length-three petal while recovering the
length-five augmentation. It then executes the recovered matching flip. -/
/-- info: true -/
#guard_msgs in
#eval
  let f := blockingPhase LevelSearch.triangleTailMatching
  f.count == 1 &&
    (List.finRange f.count).all (fun j => (f.path j).length == 5 &&
      (vertices (f.path j) == [0, 1, 2, 3, 4, 5] ||
        vertices (f.path j) == [5, 4, 3, 2, 1, 0])) &&
    f.run.cardinality == 3

/- Empty, perfect, and blossom-only inputs must return no false augmentation. -/
/-- info: true -/
#guard_msgs in
#eval
  (blockingPhase (Matching.empty LevelSearch.emptyGraph)).count == 0 &&
    (blockingPhase lineAugmented).count == 0 &&
    (blockingPhase triangleMatching).count == 0 &&
    (blockingPhase CurrentBucketCompletion.twoTrianglesMatching).count == 0

/- The concrete outer driver stops after this single positive phase, with
the exact number of performed augmentations and matching-cardinality gain. -/
/-- info: (6, 1, 2) -/
#guard_msgs in
#eval
  let result := runBlockingPhases matching
  (result.matching.cardinality, result.positivePhases, result.augmentations)

/- The total solver starts from the empty matching, including zero vertices. -/
/-- info: true -/
#guard_msgs in
#eval
  (maximumMatching graph).cardinality == 6 &&
    (maximumMatching lineFour).cardinality == 2 &&
    (maximumMatching LevelSearch.triangleTail).cardinality == 3 &&
    (maximumMatching LevelSearch.emptyGraph).cardinality == 0

end MaximumMatching.Examples.BlockingPhase
