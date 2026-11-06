import MaximumMatching.ShortestAugmentingSearch
import MaximumMatching.CurrentBucketBottomArms

/-! Locate the first augmenting level while retaining its actual search state
and the complete original bucket. Already processed triggers have equal roots
and are skipped by the continued blocking search. No MIN stage is restarted. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

inductive BlockingPhaseStart (M : Matching G) where
  | maximum (noAugmenting : M.NoAugmentingPath)
  | found (i cut : Nat) (odd : cut % 2 = 1)
      (bound : AtMostShortestAugmenting M (cut + 2)) (threshold : cut + 2 = 2 * i + 1)
      (B : CurrentBucketState M i cut) (A : OperationalArms M B.state B.forest)
      (witness : CurrentBucketWitness B)
      (es : List (Fin n × Fin n))
      (queued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
      (coverage : ∀ p : AltPath M, p.Augmenting → p.length = 2 * i + 1 →
        ∃ u v, (u, v) ∈ es ∧
          BottomBridgeArms (predecessorGraph B.state B.forest B.bud) B.forest u v
            (fun w => ∃ j, p.vertex j = w))

section
variable [DecidableRel G.Adj]

/-- The same level search as shortest augmentation, retaining the found
state and runtime arms for same-phase continuation after deletion. -/
def locateBlockingPhase {i cut : Nat} (S : LevelSearchState M i cut)
    (A : OperationalArms M S.state S.forest) : BlockingPhaseStart M :=
  if hdone : n ≤ 2 * i + 1 then
    .maximum (by
      intro p hp
      have hb := S.bound p hp
      have ht := S.threshold
      have hn := p.length_lt_vertices
      omega)
  else
    let B := prepareCurrentBucket i cut S.state S.forest S.stage S.bud S.lower
      S.odd S.bound S.threshold
    let nextArms : OperationalArms M B.state B.forest := A.afterMin S.bud S.stage.maxHasMin
    let es := B.state.bucket (2 * i + 1)
    let result := runRecoverableBucket S.odd S.bound S.threshold B nextArms es (fun _ he => he)
    match hout : result.1 with
    | .found B' A' W =>
      have herase : (runCurrentBucket S.odd S.bound S.threshold B es (fun _ he => he)).1 =
          .found B' W := by
        have hh := runRecoverableBucket_erase S.odd S.bound S.threshold B nextArms es (fun _ he => he)
        exact hh.symm.trans (congrArg RecoverableBucketOutcome.erase hout)
      .found i cut S.odd S.bound S.threshold B' A' W es
        (by
          intro e he
          have hh := runCurrentBucket_bucket_mono S.odd S.bound S.threshold B es (fun _ he => he)
            e.1 e.2 (2 * i + 1) he
          rw [herase] at hh
          exact hh)
        (by
          intro p hp hlen
          have hrep : LowerBlossomRepresentation M cut B.state B.forest :=
            scanLevelWithBuds_lower_representation i cut S.state S.forest S.bud
              (by have := S.threshold; omega) S.lower
          obtain ⟨u, v, hbridge, ht, ha⟩ := B.augmenting_bridge_arms S.odd S.bound S.threshold
            hrep p hp hlen
          have hstay := runCurrentBucket_bottom_arms S.odd S.bound S.threshold B es
            (fun _ he => he) u v _ ha
          dsimp only at hstay
          rw [herase] at hstay
          rcases prepareCurrentBucket_complete i cut S.state S.forest S.stage S.bud S.lower
              S.odd S.bound S.threshold u v hbridge ht with hm | hm
          · exact ⟨u, v, hm, hstay⟩
          · exact ⟨v, u, hm, hstay.symm⟩)
    | .exhausted B' A' =>
      have he : (runSearchLevel i cut S.state S.forest S.stage S.bud S.lower
          S.odd S.bound S.threshold).1 = .exhausted B' := by
        have hh := runRecoverableBucket_erase S.odd S.bound S.threshold B nextArms es (fun _ he => he)
        exact hh.symm.trans (congrArg RecoverableBucketOutcome.erase hout)
      have hnext := runSearchLevel_exhausted i cut S.state S.forest S.stage S.bud
        S.lower S.offRoots S.odd S.bound S.threshold B' he
      let next : LevelSearchState M (i + 1) (cut + 2) := {
        state := B'.state, forest := B'.forest,
        stage := hnext.1, bud := B'.bud, lower := hnext.2.1,
        offRoots := hnext.2.2.1, odd := by have := S.odd; omega,
        threshold := by have := S.threshold; omega,
        bound := by simpa only [Nat.add_assoc] using hnext.2.2.2 }
      locateBlockingPhase next A'
termination_by n - i
decreasing_by omega

end
end MaximumMatching.Search
