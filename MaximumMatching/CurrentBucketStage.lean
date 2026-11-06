import MaximumMatching.CurrentBucket
import MaximumMatching.MatchingBudStage
import MaximumMatching.FirstBridge
import MaximumMatching.CurrentBucketBlossoms

/-! Assemble actual MIN and fixed-bucket processing from a preceding stage.
Newly assigned vertices were fixed roots and lie above the lower cutoff;
consequently MIN preserves the established lower-blossom representation. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

namespace BudGraphInvariant

/-- MIN cannot discover an unassigned vertex below this cutoff: its finite
minimum level would already have been covered at the preceding stage. -/
theorem unknown_tenacity_high {i cut : Nat} {s : State (Fin n)}
    {F : BudForest (Fin n)} (h : BudGraphInvariant M i s F)
    (hcut : cut ≤ 2 * i + 1) (v : Fin n) (hv : s.minLabel v = none) :
    levelLT (some cut) (tenacity M v) := by
  cases ht : tenacity M v with
  | none => trivial
  | some t =>
    by_cases hhigh : cut < t
    · exact hhigh
    · obtain ⟨e, o, he, ho, hep, hop, _hsum⟩ := finite_levels_of_tenacity v t ht
      have hm : minlevel M v = some (min e o) := by
        simp only [minlevel, he, ho, levelMin]
      have hk : min e o ≤ i := by omega
      have hh := h.minInvariant.2.1 v (min e o) hm hk
      rw [hv] at hh
      contradiction

end BudGraphInvariant

section
variable [DecidableRel G.Adj]

/-- Rank relabeling retains all roots. Existing represented vertices keep
their fibers, and new MIN vertices enter as high singleton fibers. -/
theorem scanLevelWithBuds_lower_representation (i cut : Nat)
    (s : State (Fin n)) (F : BudForest (Fin n))
    (h : BudGraphInvariant M i s F) (hcut : cut ≤ 2 * i + 1)
    (hrep : LowerBlossomRepresentation M cut s F) :
    LowerBlossomRepresentation M cut (scanLevelWithBuds M i s F h).1
      (scanLevelWithBuds M i s F h).2 := by
  intro v k _hv
  rw [scanLevelWithBuds_root]
  cases hold : s.minLabel v with
  | none =>
    rw [F.root_of_fixed v (h.unknown_fixed v hold)]
    exact ⟨h.unknown_tenacity_high hcut v hold, Or.inl rfl⟩
  | some j => exact hrep v j hold

/-- Construct the actual post-MIN bucket node. All path representation
witnesses follow from the preceding lower-blossom invariant and are erased. -/
def prepareCurrentBucket (i cut : Nat) (s : State (Fin n))
    (F : BudForest (Fin n)) (hs : StageInvariant M i s)
    (hb : BudGraphInvariant M i s F)
    (hrep : LowerBlossomRepresentation M cut s F)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) : CurrentBucketState M i cut where
  state := (scanLevelWithBuds M i s F hb).1
  forest := (scanLevelWithBuds M i s F hb).2
  stage := scanLevel_stageState M i s hs
  bud := scanLevelWithBuds_invariant M i s F hb hs.maxComplete
  represented := ⟨CurrentBridgeRepresentation.ofLowerBlossoms _ hc
    (fun p hp => Nat.lt_of_lt_of_le (by omega) (htop p hp))
    (by omega) (by omega)
    (scanLevelWithBuds_lower_representation i cut s F hb (by omega) hrep)⟩

/-- Every semantic current bridge appears in the prepared actual bucket,
with either orientation permitted by the undirected edge representation. -/
theorem prepareCurrentBucket_complete (i cut : Nat) (s : State (Fin n))
    (F : BudForest (Fin n)) (hs : StageInvariant M i s)
    (hb : BudGraphInvariant M i s F)
    (hrep : LowerBlossomRepresentation M cut s F)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)
    (u v : Fin n) (hbridge : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (2 * i + 1)) :
    EdgeInBucket (prepareCurrentBucket i cut s F hs hb hrep hc htop hstageTen).state
      (2 * i + 1) u v :=
  scanLevel_stage_bucket_complete M i s hs u v hbridge ht

/-- Execute MIN followed by the entire bucket it produces. No bridge list
or same-stage path representation is supplied by the caller. -/
def runSearchLevel (i cut : Nat) (s : State (Fin n))
    (F : BudForest (Fin n)) (hs : StageInvariant M i s)
    (hb : BudGraphInvariant M i s F)
    (hrep : LowerBlossomRepresentation M cut s F)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) :
    CurrentBucketOutcome M i cut × List (PetalRecord M) :=
  let B := prepareCurrentBucket i cut s F hs hb hrep hc htop hstageTen
  runCurrentBucket hc htop hstageTen B (B.state.bucket (2 * i + 1)) (fun _ he => he)

/-- The entire actual MIN/MAX level restores all invariants needed by the
next level, including its semantic cutoff and absence of shorter augmentations. -/
theorem runSearchLevel_exhausted (i cut : Nat) (s : State (Fin n))
    (F : BudForest (Fin n)) (hs : StageInvariant M i s)
    (hb : BudGraphInvariant M i s F)
    (hrep : LowerBlossomRepresentation M cut s F)
    (hoff : MaxLabelsOffRoots s F)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)
    (B' : CurrentBucketState M i cut)
    (hex : (runSearchLevel i cut s F hs hb hrep hc htop hstageTen).1 = .exhausted B') :
    StageInvariant M (i + 1) B'.state ∧
      LowerBlossomRepresentation M (cut + 2) B'.state B'.forest ∧
      MaxLabelsOffRoots B'.state B'.forest ∧
      AtMostShortestAugmenting M (cut + 4) := by
  let B := prepareCurrentBucket i cut s F hs hb hrep hc htop hstageTen
  have hr : LowerBlossomRepresentation M cut B.state B.forest :=
    scanLevelWithBuds_lower_representation i cut s F hb (by omega) hrep
  have ho : MaxLabelsOffRoots B.state B.forest :=
    scanLevelWithBuds_maxLabelsOffRoots M i s F hb hoff
  have hcomplete : ∀ u v, Bridge M u v →
      MaximumMatching.edgeTenacity M u v = some (2 * i + 1) →
      (u, v) ∈ B.state.bucket (2 * i + 1) ∨ (v, u) ∈ B.state.bucket (2 * i + 1) :=
    prepareCurrentBucket_complete i cut s F hs hb hrep hc htop hstageTen
  have hsi := runCurrentBucket_exhausted_stageInvariant hc htop hstageTen B hr
    _ (fun _ he => he) hcomplete B' hex
  have hbr := runCurrentBucket_exhausted_lower_representation hc htop hstageTen B hr ho
    _ (fun _ he => he) hcomplete B' hex
  have hbound := runCurrentBucket_exhausted_next_lower_bound hc htop hstageTen B hr ho
    _ (fun _ he => he) hcomplete B' hex
  have hroot := runCurrentBucket_maxLabelsOffRoots hc htop hstageTen B
    _ (fun _ he => he) ho
  change (runCurrentBucket hc htop hstageTen B _ (fun _ he => he)).1 = .exhausted B' at hex
  rw [hex] at hroot
  refine ⟨hsi, ?_, hroot, ?_⟩
  · simpa only [hstageTen] using hbr
  · simpa only [show cut + 4 = 2 * (i + 1) + 1 by omega] using hbound

/-- When there is no free-free edge, the actual first MIN scan establishes
the next stage without any tenacity-one MAX vertices. -/
theorem first_scan_stageInvariant
    (hnoaug : ∀ p : AltPath M, p.Augmenting → 1 < p.length) :
    StageInvariant M 1 (scanLevel M 0 (initial M)) := by
  apply searchLevel_stageInvariant M 0 [] (initial M) (initial_stageInvariant M)
  · intro v hv
    exact False.elim (List.not_mem_nil hv)
  · intro v hv
    have hh := tenacity_above_one_of_no_short_augmenting hnoaug v
    rw [hv] at hh
    change 1 < 1 at hh
    omega

end
end MaximumMatching.Search
