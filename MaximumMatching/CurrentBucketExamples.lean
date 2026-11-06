import MaximumMatching.CurrentBucket
import MaximumMatching.FirstBridge
import MaximumMatching.Examples

/-! Execute the complete tenacity-three bucket of a triangle. The call must
form a petal, update both current roots, and leave the free boundary unchanged. -/
namespace MaximumMatching.Examples.CurrentBucket
open Search

instance : DecidableRel triangle.Adj := fun u v => inferInstanceAs (Decidable (u ≠ v))

private theorem no_short : ∀ p : AltPath triangleMatching, p.Augmenting → 1 < p.length := by
  intro p hp
  exact False.elim (triangle_no_augmenting ⟨p, hp⟩)

private theorem permitted : AtMostShortestAugmenting triangleMatching 3 := by
  intro p hp
  exact False.elim (triangle_no_augmenting ⟨p, hp⟩)

def firstState : State (Fin 3) := scanLevel triangleMatching 0 (initial triangleMatching)
def secondState : State (Fin 3) := scanLevel triangleMatching 1 firstState

theorem firstStage : StageInvariant triangleMatching 1 firstState := by
  apply searchLevel_stageInvariant triangleMatching 0 [] (initial triangleMatching)
    (initial_stageInvariant triangleMatching)
  · intro v hv
    exact False.elim (List.not_mem_nil hv)
  · intro v hv
    have hh := tenacity_above_one_of_no_short_augmenting no_short v
    rw [hv] at hh
    change 1 < 1 at hh
    omega

theorem secondStage : StageState triangleMatching 2 3 secondState :=
  scanLevel_stageState triangleMatching 1 firstState firstStage

def node : CurrentBucketState triangleMatching 1 1 where
  state := secondState
  forest := uncontractedForest secondState
  stage := secondStage
  bud := uncontractedForest_invariant secondState 2 secondStage.min secondStage.minBound
  represented := ⟨CurrentBridgeRepresentation.ofLowerBlossoms _ rfl no_short (by omega) (by omega)
    (uncontracted_lower_representation_one secondState no_short)⟩

def result : CurrentBucketOutcome triangleMatching 1 1 × List (PetalRecord triangleMatching) :=
  runCurrentBucket rfl permitted rfl node (node.state.bucket 3) (fun _ h => h)

/-- info: true -/
#guard_msgs in
#eval match result.1 with
  | .found _ _ => false
  | .exhausted B =>
    result.2.length == 1 &&
      (List.finRange 3).map B.forest.root == [0, 0, 0] &&
      (List.finRange 3).map B.state.maxLabel == [none, some 2, some 2]

end MaximumMatching.Examples.CurrentBucket
