import MaximumMatching.CurrentBucketExamples
import MaximumMatching.CurrentBucketBlossoms
import MaximumMatching.CurrentBucketStage

/-! Regression examples for the completed bucket contracts. The triangle
checks the semantic postconditions of an actual petal; the five-vertex graph
checks repeated same-level contractions through one shared free boundary. -/
namespace MaximumMatching.Examples.CurrentBucketCompletion
open Search
set_option maxRecDepth 4096

private theorem triangle_permitted : AtMostShortestAugmenting triangleMatching 3 := by
  intro p hp
  exact False.elim (triangle_no_augmenting ⟨p, hp⟩)

private theorem triangle_lower : LowerBlossomRepresentation triangleMatching 1
    CurrentBucket.node.state CurrentBucket.node.forest := by
  apply uncontracted_lower_representation_one
  intro p hp
  exact False.elim (triangle_no_augmenting ⟨p, hp⟩)

private theorem triangle_off : MaxLabelsOffRoots CurrentBucket.node.state CurrentBucket.node.forest := by
  intro v _
  exact (scanCandidates_maxLabel _ _ _ v).trans (scanCandidates_maxLabel _ _ _ v)

private theorem triangle_complete (u v : Fin 3) (hb : Bridge triangleMatching u v)
    (ht : MaximumMatching.edgeTenacity triangleMatching u v = some 3) :
    (u, v) ∈ CurrentBucket.node.state.bucket 3 ∨ (v, u) ∈ CurrentBucket.node.state.bucket 3 :=
  scanLevel_stage_bucket_complete triangleMatching 1 CurrentBucket.firstState CurrentBucket.firstStage u v hb ht

/-- The actual executable result is exhausted, not a spurious augmentation. -/
theorem triangle_exhausted :
    CurrentBucket.result.1 = .exhausted CurrentBucket.result.1.state := by
  cases he : CurrentBucket.result.1 with
  | exhausted B => rfl
  | found B W =>
    obtain ⟨p, hp, _⟩ := W.shortest_augmenting rfl triangle_permitted rfl
    exact False.elim (triangle_no_augmenting ⟨p, hp⟩)

/-- MAX coverage is obtained from the complete bucket theorem. -/
example : ∀ v, tenacity triangleMatching v = some 3 →
    CurrentBucket.result.1.state.state.maxLabel v = maxlevel triangleMatching v :=
  runCurrentBucket_exhausted_maxComplete rfl triangle_permitted rfl CurrentBucket.node
    triangle_lower (CurrentBucket.node.state.bucket 3) (fun _ h => h) triangle_complete
    _ triangle_exhausted

/-- Exhaustion raises the augmentation lower bound to five. -/
example : AtMostShortestAugmenting triangleMatching 5 :=
  runCurrentBucket_exhausted_next_lower_bound rfl triangle_permitted rfl CurrentBucket.node
    triangle_lower triangle_off (CurrentBucket.node.state.bucket 3) (fun _ h => h) triangle_complete
    _ triangle_exhausted

/-- The returned forest represents the actual tenacity-three blossoms. -/
example : LowerBlossomRepresentation triangleMatching 3
    CurrentBucket.result.1.state.state CurrentBucket.result.1.state.forest :=
  runCurrentBucket_exhausted_lower_representation rfl triangle_permitted rfl CurrentBucket.node
    triangle_lower triangle_off (CurrentBucket.node.state.bucket 3) (fun _ h => h) triangle_complete
    _ triangle_exhausted

/-- Two triangles, 0--1--2--0 and 0--3--4--0, share their free boundary. -/
def twoTriangles : Graph (Fin 5) where
  Adj u v := u ≠ v ∧ (u = 0 ∨ v = 0 ∨ (u.val ≤ 2 ↔ v.val ≤ 2))
  symm := by
    intro u v h
    exact ⟨h.1.symm, h.2.elim (fun hu => Or.inr (Or.inl hu))
      (fun hv => hv.elim Or.inl (fun hh => Or.inr (Or.inr hh.symm)))⟩
  loopless := fun _ h => h.1 rfl

instance : DecidableRel twoTriangles.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ≠ _ ∧ (_ = 0 ∨ _ = 0 ∨ (_ ≤ 2 ↔ _ ≤ 2))))

def twoTrianglesMatching : Matching twoTriangles where
  mate v := if v = 0 then none else if v = 1 then some 2 else if v = 2 then some 1
    else if v = 3 then some 4 else some 3
  symm := by decide
  edge := by dsimp [twoTriangles]; decide

private theorem twoTriangles_free (v : Fin 5) : twoTrianglesMatching.Free v ↔ v = 0 := by
  unfold Matching.Free
  revert v
  decide

private theorem twoTriangles_no_augmenting :
    ∀ p : AltPath twoTrianglesMatching, p.Augmenting → False := by
  intro p hp
  have hf := (twoTriangles_free p.first).1 p.start_free
  have hl := (twoTriangles_free p.last).1 hp.2
  exact p.augmenting_distinct hp (hf.trans hl.symm)

private theorem twoTriangles_no_short :
    ∀ p : AltPath twoTrianglesMatching, p.Augmenting → 1 < p.length :=
  fun p hp => False.elim (twoTriangles_no_augmenting p hp)

private theorem twoTriangles_permitted : AtMostShortestAugmenting twoTrianglesMatching 3 :=
  fun p hp => False.elim (twoTriangles_no_augmenting p hp)

def twoFirst : State (Fin 5) := scanLevel twoTrianglesMatching 0 (initial twoTrianglesMatching)
def twoSecond : State (Fin 5) := scanLevel twoTrianglesMatching 1 twoFirst

private theorem twoFirstStage : StageInvariant twoTrianglesMatching 1 twoFirst :=
  first_scan_stageInvariant twoTriangles_no_short

private theorem twoSecondStage : StageState twoTrianglesMatching 2 3 twoSecond :=
  scanLevel_stageState twoTrianglesMatching 1 twoFirst twoFirstStage

def twoNode : CurrentBucketState twoTrianglesMatching 1 1 where
  state := twoSecond
  forest := uncontractedForest twoSecond
  stage := twoSecondStage
  bud := uncontractedForest_invariant twoSecond 2 twoSecondStage.min twoSecondStage.minBound
  represented := ⟨CurrentBridgeRepresentation.ofLowerBlossoms _ rfl twoTriangles_no_short
    (by omega) (by omega) (uncontracted_lower_representation_one twoSecond twoTriangles_no_short)⟩

def twoResult : CurrentBucketOutcome twoTrianglesMatching 1 1 × List (PetalRecord twoTrianglesMatching) :=
  runCurrentBucket rfl twoTriangles_permitted rfl twoNode (twoNode.state.bucket 3) (fun _ h => h)

/-- info: true -/
#guard_msgs in
#eval match twoResult.1 with
  | .found _ _ => false
  | .exhausted B =>
    twoResult.2.length == 2 &&
      (List.finRange 5).map B.forest.root == [0, 0, 0, 0, 0] &&
      (List.finRange 5).map B.state.maxLabel == [none, some 2, some 2, some 2, some 2]

private theorem twoResult_exhausted : twoResult.1 = .exhausted twoResult.1.state := by
  cases he : twoResult.1 with
  | exhausted B => rfl
  | found B W =>
    obtain ⟨p, hp, _⟩ := W.shortest_augmenting rfl twoTriangles_permitted rfl
    exact False.elim (twoTriangles_no_augmenting p hp)

/-- Both actual contractions preserve the canonical class representation. -/
example : LowerBlossomRepresentation twoTrianglesMatching 3 twoResult.1.state.state twoResult.1.state.forest := by
  apply runCurrentBucket_exhausted_lower_representation rfl twoTriangles_permitted rfl twoNode
    (uncontracted_lower_representation_one twoSecond twoTriangles_no_short) ?_
    (twoNode.state.bucket 3) (fun _ h => h) ?_ _ twoResult_exhausted
  · intro v _
    exact (scanCandidates_maxLabel _ _ _ v).trans (scanCandidates_maxLabel _ _ _ v)
  · intro u v hb ht
    exact scanLevel_stage_bucket_complete twoTrianglesMatching 1 twoFirst twoFirstStage u v hb ht

end MaximumMatching.Examples.CurrentBucketCompletion
