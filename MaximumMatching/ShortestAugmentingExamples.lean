import MaximumMatching.ShortestAugmentingSearch
import MaximumMatching.LevelSearchExamples

/-! Runtime regression tests for computed matching-path recovery, including a
path that traverses an earlier petal. Successful results execute a real flip;
no alternating path is supplied as a recovery witness by these examples. -/
namespace MaximumMatching.Examples.ShortestAugmenting
open Search
set_option maxRecDepth 4096

private def vertices {n : Nat} {G : Graph (Fin n)} {M : Matching G}
    (p : AltPath M) : List Nat :=
  (List.finRange (p.length + 1)).map (fun i => (p.vertex i).val)

/- The recovered five-edge path passes through the triangle contracted at
length three. Augmentation executes the recovered data and gains one edge. -/
/-- info: true -/
#guard_msgs in
#eval
  let result := findShortestAugmenting LevelSearch.triangleTailMatching
  match result.1 with
  | .maximum _ => false
  | .found p hp _ =>
    result.2.length == 1 && p.length == 5 &&
      (vertices p == [0, 1, 2, 3, 4, 5] || vertices p == [5, 4, 3, 2, 1, 0]) &&
      (p.augment hp).cardinality == 3

/- This path is found after an empty length-three bucket advances the actual
MIN/MAX state to length five. -/
/-- info: true -/
#guard_msgs in
#eval
  let result := findShortestAugmenting LevelSearch.lineSixMatching
  match result.1 with
  | .maximum _ => false
  | .found p hp _ =>
    result.2.length == 0 && p.length == 5 &&
      (vertices p == [0, 1, 2, 3, 4, 5] || vertices p == [5, 4, 3, 2, 1, 0]) &&
      (p.augment hp).cardinality == 3

/-- info: true -/
#guard_msgs in
#eval
  match (findShortestAugmenting middleMatching).1 with
  | .maximum _ => false
  | .found p hp _ =>
    p.length == 3 && (vertices p == [0, 1, 2, 3] || vertices p == [3, 2, 1, 0]) &&
      (p.augment hp).cardinality == 2

/-- info: true -/
#guard_msgs in
#eval
  match (findShortestAugmenting (Matching.empty lineFour)).1 with
  | .maximum _ => false
  | .found p hp _ => p.length == 1 && (p.augment hp).cardinality == 1

/- Two actual same-level petals are processed without manufacturing a path
between copies of their shared free boundary. -/
/-- info: true -/
#guard_msgs in
#eval
  let result := findShortestAugmenting CurrentBucketCompletion.twoTrianglesMatching
  match result.1 with
  | .maximum _ => result.2.length == 2
  | .found _ _ _ => false

/-- info: false -/
#guard_msgs in
#eval (findShortestAugmenting lineAugmented).1.hasPath

/-- info: false -/
#guard_msgs in
#eval (findShortestAugmenting (Matching.empty LevelSearch.emptyGraph)).1.hasPath

end MaximumMatching.Examples.ShortestAugmenting
