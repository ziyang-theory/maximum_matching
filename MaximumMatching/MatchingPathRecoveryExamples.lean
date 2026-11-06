import MaximumMatching.MatchingPathRecoveryPredecessors
import MaximumMatching.DDFSExecutableExamples
import MaximumMatching.CurrentBucketExamples

/-! Computational checks for recovery from actual DDFS outputs and petal
records, including an abandoned search branch and a selected bottleneck. -/
namespace MaximumMatching.DDFS.RecoveryExamples

def vertices {n : Nat} {H : LayeredGraph (Fin n)} (p : Path H) : List Nat :=
  (List.finRange (p.length + 1)).map (fun j => (p.vertex j).val)

def linkages {n : Nat} {H : LayeredGraph (Fin n)} {r g : Fin n}
    (out : Machine.FullOutput H r g) : List (Nat × List Nat × List Nat) :=
  match out with
  | .disjoint .. => []
  | .bottleneck _b _ trees _ region =>
    (List.finRange n).filterMap fun v =>
      match hc : trees.color v with
      | none => none
      | some _ =>
        have hs := (trees.domain v).1 ⟨_, hc⟩
        let pq := trees.recoverLinkage v hs.1
          (onRootTo_level_gt ((region v).1 hs.1) hs.2)
        some (v.val, vertices pq.val.1, vertices pq.val.2)

/-- info: true -/
#guard_msgs in
#eval linkages (Machine.executeFull ExecutableExamples.fixture_reaches 0 1) ==
  [(0, [0], [1, 2, 5]), (1, [1], [0, 4, 5]), (2, [1, 2], [0, 4, 5]),
    (3, [0, 3], [1, 2, 5]), (4, [0, 4], [1, 2, 5])]

end MaximumMatching.DDFS.RecoveryExamples

namespace MaximumMatching.Examples.CurrentBucket
open Search DDFS.RecoveryExamples

def recoveredTails : List (List (Nat × List Nat)) :=
  result.2.map fun R => R.trees.vertices.attach.map fun v =>
    (v.val.val, vertices (R.recoverTail v.val ((R.trees.mem_vertices v.val).1 v.property)).val)

/-- info: true -/
#guard_msgs in
#eval recoveredTails == [[(0, [0]), (1, [1, 0]), (2, [2, 0])]]

end MaximumMatching.Examples.CurrentBucket
