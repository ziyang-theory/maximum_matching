import MaximumMatching.CurrentBucketEndRoots
import MaximumMatching.CurrentBucketAugmenting
import MaximumMatching.PetalBaseClasses

/-! Actual current-bucket exhaustion restores the lower-blossom
representation at the next cutoff. Canonical classes are preserved through
all temporary petals; complete MAX discovery makes their final roots high. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G} [DecidableRel G.Adj]
    {i cut : Nat}
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)

/-- Every recorded contraction preserves canonical classes and the tenacity
bound on absorbed vertices. The strict augmentation bound is semantic and is
later derived from actual bucket exhaustion. -/
theorem runCurrentBucket_blossomClasses (B : CurrentBucketState M i cut)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut + 2 < p.length)
    (hlow : NonrootLow M (cut + 2) B.forest)
    (hclasses : BudBlossomClasses M (cut + 2) B.forest) :
    NonrootLow M (cut + 2) (runCurrentBucket hc htop hstageTen B es hqueued).1.state.forest ∧
      BudBlossomClasses M (cut + 2) (runCurrentBucket hc htop hstageTen B es hqueued).1.state.forest := by
  induction es generalizing B with
  | nil => simpa only [runCurrentBucket, CurrentBucketOutcome.state] using And.intro hlow hclasses
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    rw [runCurrentBucket]
    split
    · exact ih B _ hlow hclasses
    · split
      · exact ⟨hlow, hclasses⟩
      · rename_i hsame bneck S trees highest region hout
        let R : PetalRecord M := {
          cap := i + 1, prior := B.state, forest := B.forest, invariant := B.bud,
          queueSound := B.stage.classification.2.2, tenacity := 2 * i + 1,
          left := a, right := b, queued := hqueued (a, b) List.mem_cons_self,
          known := B.stage.current_bridge_known a b
            (B.stage.classification.2.2 _ a b (hqueued (a,b) List.mem_cons_self)).1
            (B.stage.classification.2.2 _ a b (hqueued (a,b) List.mem_cons_self)).2,
          different := hsame, bottleneck := bneck, selected := S, trees := trees,
          highest := highest, region := region, computed := hout }
        obtain ⟨P⟩ := B.represented
        exact ih _ _ (R.after_nonrootLow P hc htop hstageTen.symm hlow)
          (R.after_blossomClasses P hc hnoaug hstageTen.symm hlow hclasses)

/-- A complete exhausted bucket establishes the exact semantic blossom/base
representation for the next search level. All support completeness and the
strict augmentation bound are derived from the actual loop, not assumed. -/
theorem runCurrentBucket_exhausted_lower_representation (B : CurrentBucketState M i cut)
    (hrep : LowerBlossomRepresentation M cut B.state B.forest)
    (hoff : MaxLabelsOffRoots B.state B.forest)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (hcomplete : ∀ u v, Bridge M u v → MaximumMatching.edgeTenacity M u v = some (2 * i + 1) →
      (u, v) ∈ es ∨ (v, u) ∈ es)
    (B' : CurrentBucketState M i cut)
    (hexhausted : (runCurrentBucket hc htop hstageTen B es hqueued).1 = .exhausted B') :
    LowerBlossomRepresentation M (2 * i + 1) B'.state B'.forest := by
  have hnext := runCurrentBucket_exhausted_next_lower_bound hc htop hstageTen B hrep hoff
    es hqueued hcomplete B' hexhausted
  have hnoaug : ∀ p : AltPath M, p.Augmenting → cut + 2 < p.length := by
    intro p hp
    have hh := hnext p hp
    omega
  have hclasses := (runCurrentBucket_blossomClasses hc htop hstageTen B es hqueued hnoaug
    (nonrootLow_of_lower B.bud hrep) (budBlossomClasses_of_lower B.bud hc hrep)).2
  rw [hexhausted] at hclasses
  have hclasses' : BudBlossomClasses M (2 * i + 1) B'.forest := by
    simpa only [CurrentBucketOutcome.state, hstageTen] using hclasses
  exact hclasses'.lower_representation (fun v _ _ =>
    runCurrentBucket_exhausted_roots_high hc htop hstageTen B hrep hoff es hqueued hcomplete B' hexhausted v)

/-- At the processed tenacity the final bud is the vertex's canonical base,
not merely a representative of its recursive blossom. -/
theorem runCurrentBucket_exhausted_base (B : CurrentBucketState M i cut)
    (hrep : LowerBlossomRepresentation M cut B.state B.forest)
    (hoff : MaxLabelsOffRoots B.state B.forest)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (hcomplete : ∀ u v, Bridge M u v → MaximumMatching.edgeTenacity M u v = some (2 * i + 1) →
      (u, v) ∈ es ∨ (v, u) ∈ es)
    (B' : CurrentBucketState M i cut)
    (hexhausted : (runCurrentBucket hc htop hstageTen B es hqueued).1 = .exhausted B')
    (v : Fin n) (hten : tenacity M v = some (2 * i + 1)) :
    IsBase M v (B'.forest.root v) := by
  have hr := runCurrentBucket_exhausted_lower_representation hc htop hstageTen B hrep hoff
    es hqueued hcomplete B' hexhausted
  obtain ⟨e, o, he, ho, _, _, hsum⟩ := finite_levels_of_tenacity v (2 * i + 1) hten
  have hmin : minlevel M v = some (min e o) := by
    simp only [minlevel, he, ho, levelMin]
  have hv := B'.stage.min.2.1 v (min e o) hmin (by omega)
  obtain ⟨hhigh, hmem⟩ := hr v (min e o) hv
  rcases hmem with hroot | hbl
  · rw [← hroot, hten] at hhigh
    change 2 * i + 1 < 2 * i + 1 at hhigh
    omega
  · rw [← hstageTen] at hbl
    rcases hbl with hbase | ⟨w, _, _, hlow⟩
    · exact hbase.2
    · obtain ⟨a, ha, hac⟩ := blossom_tenacity_bound cut w v hlow
      have hh := Option.some.inj (ha.symm.trans hten)
      omega

/-- Functional form of the end-of-level bud/base correspondence. -/
theorem runCurrentBucket_exhausted_base_eq (B : CurrentBucketState M i cut)
    (hrep : LowerBlossomRepresentation M cut B.state B.forest)
    (hoff : MaxLabelsOffRoots B.state B.forest)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (hcomplete : ∀ u v, Bridge M u v → MaximumMatching.edgeTenacity M u v = some (2 * i + 1) →
      (u, v) ∈ es ∨ (v, u) ∈ es)
    (B' : CurrentBucketState M i cut)
    (hexhausted : (runCurrentBucket hc htop hstageTen B es hqueued).1 = .exhausted B')
    (v : Fin n) (hten : tenacity M v = some (2 * i + 1)) :
    base M v = some (B'.forest.root v) :=
  (base_eq_some_iff v (B'.forest.root v)).2
    (runCurrentBucket_exhausted_base hc htop hstageTen B hrep hoff es hqueued hcomplete B' hexhausted v hten)

end MaximumMatching.Search
