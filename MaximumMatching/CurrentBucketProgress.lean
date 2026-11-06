import MaximumMatching.CurrentBucket

/-! Monotone bud classes and completed-trigger accounting for the actual
current-bucket loop. Exhaustion here means the supplied bucket was processed;
semantic support coverage is a separate remaining implication. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

namespace PetalRecord

theorem starts_selected (R : PetalRecord M) :
    R.selected (R.forest.root R.left) ∧ R.selected (R.forest.root R.right) := by
  obtain ⟨p, hpf, hpb, _⟩ := R.trees.red.path R.bottleneck (Or.inl rfl)
  obtain ⟨q, hqf, hqb, _⟩ := R.trees.green.path R.bottleneck (Or.inl rfl)
  exact ⟨(R.region _).2 ⟨p, Or.inl hpf, hpb, ⟨0, by omega⟩, hpf⟩,
    (R.region _).2 ⟨q, Or.inr hqf, hqb, ⟨0, by omega⟩, hqf⟩⟩

theorem after_trigger_equal (R : PetalRecord M) :
    R.after.root R.left = R.after.root R.right :=
  (R.after_selected R.left R.starts_selected.1).trans (R.after_selected R.right R.starts_selected.2).symm

/-- A fixed old root survives unless MAX's computed list includes it. The
bottleneck survives even though it belongs to the selected region. -/
theorem after_root_eq_or_newRoot (R : PetalRecord M) (v : Fin n)
    (hv : R.forest.root v = v) : R.after.root v = v ∨ v ∈ R.newRoots := by
  by_cases hnew : v ∈ R.newRoots
  · exact Or.inr hnew
  · left
    by_cases hsel : R.selected v
    · have hb : v = R.bottleneck := by
        by_cases he : v = R.bottleneck
        · exact he
        · exact False.elim (hnew ((R.mem_newRoots v).2 ⟨hsel, he⟩))
      exact (R.after_selected v (by simpa only [selectedFiber, hv] using hsel)).trans hb.symm
    · exact (R.after_outside v (by simpa only [selectedFiber, hv] using hsel)).trans hv

end PetalRecord

namespace CurrentBucketOutcome

def state {i cut : Nat} : CurrentBucketOutcome M i cut → CurrentBucketState M i cut
  | .exhausted B => B
  | .found B _ => B

end CurrentBucketOutcome

section
variable [DecidableRel G.Adj] {i cut : Nat}
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)

/-- Any two vertices already in one bud class remain together after the
actual bucket loop, including if a disjoint witness stops the loop early. -/
theorem runCurrentBucket_root_congr (B : CurrentBucketState M i cut)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (u v : Fin n) (heq : B.forest.root u = B.forest.root v) :
    (runCurrentBucket hc htop hstageTen B es hqueued).1.state.forest.root u =
      (runCurrentBucket hc htop hstageTen B es hqueued).1.state.forest.root v := by
  induction es generalizing B with
  | nil => simpa only [runCurrentBucket, CurrentBucketOutcome.state] using heq
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    rw [runCurrentBucket]
    split
    · exact ih B _ heq
    · split
      · exact heq
      · apply ih
        exact B.forest.mergeManyInto_root_congr _ _ u v heq

/-- Exhausting the supplied bucket accounts for every supplied trigger: its
endpoints lie in the same final bud class, including triggers skipped because
they had already merged. Repeated triggers require no extra hypothesis. -/
theorem runCurrentBucket_exhausted_trigger_equal (B : CurrentBucketState M i cut)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (B' : CurrentBucketState M i cut)
    (hexhausted : (runCurrentBucket hc htop hstageTen B es hqueued).1 = .exhausted B')
    (u v : Fin n) (hmem : (u, v) ∈ es) :
    B'.forest.root u = B'.forest.root v := by
  induction es generalizing B B' with
  | nil => simp at hmem
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    rw [runCurrentBucket] at hexhausted
    split at hexhausted
    · rename_i hsame
      rcases List.mem_cons.mp hmem with he | he
      · obtain ⟨hu, hv⟩ := Prod.mk.inj he
        have hh := runCurrentBucket_root_congr hc htop hstageTen B es
          (fun e he => hqueued e (List.mem_cons_of_mem (a, b) he)) a b hsame
        rw [hexhausted] at hh
        simpa only [CurrentBucketOutcome.state, hu, hv] using hh
      · exact ih B _ B' hexhausted he
    · split at hexhausted
      · contradiction
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
        let next := CurrentBucketState.afterPetal R B.represented hc htop
          hstageTen.symm hstageTen rfl B.stage
        have hq : ∀ e, e ∈ es → e ∈ next.state.bucket (2 * i + 1) := by
          intro e he
          exact R.maxEvent_bucket_mono i e.1 e.2 _
            (hqueued e (List.mem_cons_of_mem (a, b) he))
        change (runCurrentBucket hc htop hstageTen next es hq).1 = .exhausted B' at hexhausted
        rcases List.mem_cons.mp hmem with he | he
        · obtain ⟨hu, hv⟩ := Prod.mk.inj he
          have hh := runCurrentBucket_root_congr hc htop hstageTen next es hq a b
            R.after_trigger_equal
          rw [hexhausted] at hh
          simpa only [CurrentBucketOutcome.state, hu, hv] using hh
        · exact ih next hq B' hexhausted he

/-- MAX and petal contraction leave all minimum labels unchanged throughout
bucket processing, including when a disjoint witness stops the loop. -/
theorem runCurrentBucket_minLabel (B : CurrentBucketState M i cut)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1)) :
    (runCurrentBucket hc htop hstageTen B es hqueued).1.state.state.minLabel = B.state.minLabel := by
  induction es generalizing B with
  | nil => simp only [runCurrentBucket, CurrentBucketOutcome.state]
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    rw [runCurrentBucket]
    split
    · exact ih B _
    · split
      · rfl
      · exact (ih _ _).trans (funext (maxProcessVertices_minLabel M i _ B.state))

/-- The actual bucket loop retains MIN's predecessor lists. -/
theorem runCurrentBucket_predecessors (B : CurrentBucketState M i cut)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1)) :
    (runCurrentBucket hc htop hstageTen B es hqueued).1.state.state.predecessors =
      B.state.predecessors := by
  induction es generalizing B with
  | nil => simp only [runCurrentBucket, CurrentBucketOutcome.state]
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    rw [runCurrentBucket]
    split
    · exact ih B _
    · split
      · rfl
      · exact (ih _ _).trans (maxProcessVertices_predecessors M i _ B.state)

/-- Already assigned maximum labels survive every actual MAX event in the
bucket loop. -/
theorem runCurrentBucket_preserves_known_maxLabel (B : CurrentBucketState M i cut)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (v : Fin n) (k : Nat) (hknown : B.state.maxLabel v = some k) :
    (runCurrentBucket hc htop hstageTen B es hqueued).1.state.state.maxLabel v = some k := by
  induction es generalizing B with
  | nil => simpa only [runCurrentBucket, CurrentBucketOutcome.state] using hknown
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    rw [runCurrentBucket]
    split
    · exact ih B _ hknown
    · split
      · exact hknown
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
        apply ih
        obtain ⟨P⟩ := B.represented
        exact (R.maxEvent_correct_of_current P i (2 * i + 1) hc htop
          hstageTen.symm hstageTen rfl B.stage).2.2.2 v k hknown

/-- Every vertex that starts as its own bud root either remains a root or
receives a maximum-level assignment during the actual bucket loop. -/
theorem runCurrentBucket_root_eq_or_known_maxLabel (B : CurrentBucketState M i cut)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (v : Fin n) (hroot : B.forest.root v = v) :
    (runCurrentBucket hc htop hstageTen B es hqueued).1.state.forest.root v = v ∨
      ∃ k, (runCurrentBucket hc htop hstageTen B es hqueued).1.state.state.maxLabel v = some k := by
  induction es generalizing B with
  | nil => exact Or.inl (by simpa only [runCurrentBucket, CurrentBucketOutcome.state] using hroot)
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    rw [runCurrentBucket]
    split
    · exact ih B _ hroot
    · split
      · exact Or.inl hroot
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
        rcases R.after_root_eq_or_newRoot v hroot with hstay | hnew
        · exact ih _ _ hstay
        · right
          obtain ⟨P⟩ := B.represented
          have hten := (R.newRoots_support_of_current P hc htop hstageTen.symm v hnew).1
          obtain ⟨lo, hlo, _⟩ := minlevel_le_half_tenacity v i hten
          have hmax := (maxlevel_eq_tenacity_sub v (2 * i + 1) lo hten hlo).2
          have hset := (R.maxEvent_correct_of_current P i (2 * i + 1) hc htop
            hstageTen.symm hstageTen rfl B.stage).2.2.1 v hnew
          exact ⟨_, runCurrentBucket_preserves_known_maxLabel hc htop hstageTen _ es _ v _
            (hset.trans hmax)⟩

/-- An initially fixed vertex that remains unlabeled by MAX cannot have been
absorbed into another final bud. -/
theorem runCurrentBucket_root_eq_of_maxLabel_none (B : CurrentBucketState M i cut)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (v : Fin n) (hroot : B.forest.root v = v)
    (hnone : (runCurrentBucket hc htop hstageTen B es hqueued).1.state.state.maxLabel v = none) :
    (runCurrentBucket hc htop hstageTen B es hqueued).1.state.forest.root v = v := by
  rcases runCurrentBucket_root_eq_or_known_maxLabel hc htop hstageTen B es hqueued v hroot with h | ⟨k, hk⟩
  · exact h
  · rw [hnone] at hk
    contradiction

end
end MaximumMatching.Search
