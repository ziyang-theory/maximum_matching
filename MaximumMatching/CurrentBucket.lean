import MaximumMatching.CurrentBridgeRepresentation
import MaximumMatching.MatchingSearchGraph

section CurrentBucketFacts

/-! Operational facts for processing a fixed complete current-tenacity bucket.
All queued current bridges have computable tenacity, and actual MAX refreshes
retain every previously queued edge. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

theorem current_bridge_tenacity_available (s : State V) (i : Nat)
    (hc : MinCompleteBelow M i s) (hx : MaxCompleteBelowTenacity M (2 * i + 1) s)
    (u v : V) (hb : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (2 * i + 1)) :
    edgeTenacity M s u v = some (2 * i + 1) := by
  by_cases hm : M.mate u = some v
  · obtain ⟨j, huj, _, hum, hvm, _, _, hsum⟩ := matched_bridge_levels hb hm (2 * i + 1) ht
    have hji : j = i := by omega
    have hjodd := level_parity M 1 u j huj
    have hu := hc u j hum (by omega)
    have hv := hc v j hvm (by omega)
    simp [edgeTenacity, hm, parityLabel, hu, hv, hjodd,
      show j + j + 1 = 2 * i + 1 by omega]
  · exact unmatched_bridge_tenacity_available s i u v hc hx hb hm ht

theorem StageState.current_bridge_known {i : Nat} {s : State V}
    (h : StageState M (i + 1) (2 * i + 1) s) (u v : V)
    (hb : Bridge M u v) (ht : MaximumMatching.edgeTenacity M u v = some (2 * i + 1)) :
    edgeTenacity M s u v = some (2 * i + 1) :=
  current_bridge_tenacity_available s i
    (fun w k hw hk => h.min.2.1 w k hw (by omega)) h.maxComplete u v hb ht

theorem assignMax_bucket (s : State V) (t : Nat) (x : V) :
    (assignMax s t x).bucket = s.bucket := by
  unfold assignMax
  split <;> rfl

section Finite
variable {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]

theorem maxProcessVertices_bucket_mono (M : Matching G) (i : Nat) (s : State (Fin n))
    (xs : List (Fin n)) (u v : Fin n) (t : Nat) (h : (u, v) ∈ s.bucket t) :
    (u, v) ∈ (maxProcessVertices M i xs s).bucket t := by
  induction xs generalizing s with
  | nil => exact h
  | cons x xs ih => exact ih _ (maxProcessVertex_bucket_mono M i x u v s t h)

theorem PetalRecord.maxEvent_bucket_mono {M : Matching G} (R : PetalRecord M) (i : Nat)
    (u v : Fin n) (t : Nat) (h : (u, v) ∈ R.prior.bucket t) :
    (u, v) ∈ (R.maxEvent i).1.bucket t :=
  maxProcessVertices_bucket_mono M i R.prior R.newRoots u v t h

end Finite
end MaximumMatching.Search

end CurrentBucketFacts

section CurrentBucket

/-! Concrete processing of a fixed current-tenacity bucket. Each distinct-root
trigger runs DDFS once; bottleneck events execute actual MAX and contraction.
The executable result retains raw disjoint DDFS paths, not a path selected by
classical choice. Matching-path recovery and complete support coverage remain
separate theorems. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)}

/-- Operational state plus erased correctness and path-representation proofs.
The representation is existential in Prop, so it is not a runtime oracle. -/
structure CurrentBucketState (M : Matching G) (i cut : Nat) where
  state : State (Fin n)
  forest : BudForest (Fin n)
  stage : StageState M (i + 1) (2 * i + 1) state
  bud : BudGraphInvariant M (i + 1) state forest
  represented : Nonempty (CurrentBridgeRepresentation M cut bud)

namespace CurrentBucketState
variable {M : Matching G} {i cut : Nat}

/-- Build the next operational node from the actual recorded MAX event.
Its representation proof is erased, while all state and forest operations
remain the executable ones already defined. -/
def afterPetal [DecidableRel G.Adj] (R : PetalRecord M)
    (hP : Nonempty (CurrentBridgeRepresentation M cut R.invariant))
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hten : R.tenacity = cut + 2) (hstageTen : cut + 2 = 2 * i + 1)
    (hcap : R.cap = i + 1) (hstage : StageState M (i + 1) (2 * i + 1) R.prior) :
    CurrentBucketState M i cut where
  state := (R.maxEvent i).1
  forest := R.after
  stage := by
    obtain ⟨P⟩ := hP
    exact (R.maxEvent_correct_of_current P i (2 * i + 1) hc htop hten hstageTen hcap hstage).1
  bud := by
    obtain ⟨P⟩ := hP
    exact (R.maxEvent_correct_of_current P i (2 * i + 1) hc htop hten hstageTen hcap hstage).2.1
  represented := by
    obtain ⟨P⟩ := hP
    exact ⟨R.maxEvent_representation P i _⟩

end CurrentBucketState

/-- A disjoint output from the actual call at its precise matching state. -/
structure CurrentBucketWitness {M : Matching G} {i cut : Nat} (B : CurrentBucketState M i cut) where
  left : Fin n
  right : Fin n
  queued : (left, right) ∈ B.state.bucket (2 * i + 1)
  red : DDFS.Path (predecessorGraph B.state B.forest B.bud)
  green : DDFS.Path (predecessorGraph B.state B.forest B.bud)
  red_bottom : red.ToBottom (B.forest.root left)
  green_bottom : green.ToBottom (B.forest.root right)
  disjoint : red.Disjoint green
  computed : DDFS.Machine.executeFull B.bud.reachBottom (B.forest.root left) (B.forest.root right) =
    .disjoint red green red_bottom green_bottom disjoint

inductive CurrentBucketOutcome (M : Matching G) (i cut : Nat) where
  | exhausted (state : CurrentBucketState M i cut)
  | found (state : CurrentBucketState M i cut) (witness : CurrentBucketWitness state)

/-- Execute a fixed list of queued current bridges. The list may have
repetitions; already-contracted equal roots are skipped. Each newly formed
petal is retained with its actual prior state for later path recovery. -/
def runCurrentBucket [DecidableRel G.Adj] {M : Matching G} {i cut : Nat}
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)
    (B : CurrentBucketState M i cut) (es : List (Fin n × Fin n))
    (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1)) :
    CurrentBucketOutcome M i cut × List (PetalRecord M) :=
  match es with
  | [] => (.exhausted B, [])
  | (u, v) :: rest =>
    have he := hqueued (u, v) List.mem_cons_self
    have hb := B.stage.classification.2.2 (2 * i + 1) u v he
    have hknown := B.stage.current_bridge_known u v hb.1 hb.2
    if hsame : B.forest.root u = B.forest.root v then
      runCurrentBucket hc htop hstageTen B rest
        (fun e he => hqueued e (List.mem_cons_of_mem (u, v) he))
    else
      match hout : DDFS.Machine.executeFull B.bud.reachBottom (B.forest.root u) (B.forest.root v) with
      | .disjoint p q hp hq hd =>
        (.found B {
          left := u, right := v, queued := he, red := p, green := q,
          red_bottom := hp, green_bottom := hq, disjoint := hd, computed := hout }, [])
      | .bottleneck b S trees highest region =>
        let R : PetalRecord M := {
          cap := i + 1, prior := B.state, forest := B.forest, invariant := B.bud,
          queueSound := B.stage.classification.2.2, tenacity := 2 * i + 1,
          left := u, right := v, queued := he, known := hknown, different := hsame,
          bottleneck := b, selected := S, trees := trees, highest := highest,
          region := region, computed := hout }
        let next := CurrentBucketState.afterPetal R B.represented hc htop hstageTen.symm hstageTen rfl B.stage
        let result := runCurrentBucket hc htop hstageTen next rest (by
          intro e he'
          exact R.maxEvent_bucket_mono i e.1 e.2 (2 * i + 1)
            (hqueued e (List.mem_cons_of_mem (u, v) he')))
        (result.1, R :: result.2)
termination_by es.length

namespace CurrentBucketWitness
variable {M : Matching G} {i cut : Nat} {B : CurrentBucketState M i cut}

/-- A returned raw disjoint certificate has a real shortest augmenting path
through its actual queued trigger. This is a soundness theorem, not an
executable path reconstruction by classical choice. -/
theorem shortest_augmenting (W : CurrentBucketWitness B)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) :
    ∃ p : AltPath M, p.Augmenting ∧ p.length = 2 * i + 1 ∧
      p.ContainsEdge W.left W.right ∧
      ∀ q : AltPath M, q.Augmenting → p.length ≤ q.length := by
  obtain ⟨P⟩ := B.represented
  have hb := B.stage.classification.2.2 (2 * i + 1) W.left W.right W.queued
  have hk := B.stage.current_bridge_known W.left W.right hb.1 hb.2
  obtain ⟨hu, hv⟩ := edgeTenacity_has_minLabels B.state W.left W.right (2 * i + 1) hk
  obtain ⟨p, hp, hlen, hedge, hshort⟩ := P.disjoint_bridge_paths_shortest hc htop
    W.left W.right hb.1 (by rw [hstageTen]; exact hb.2) hu hv
    W.red W.green W.red_bottom W.green_bottom W.disjoint
  exact ⟨p, hp, hlen.trans hstageTen, hedge, hshort⟩

end CurrentBucketWitness
end MaximumMatching.Search

end CurrentBucket

section CurrentBucketProgress

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

end CurrentBucketProgress

section CurrentBucketRootLabels

/-! Maximum labels belong to absorbed roots. This operational invariant is
initialized by the empty MAX state and is preserved by actual MIN, MAX, and
petal contraction. It does not assume canonical blossom/base correspondence. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

/-- Current bud roots have not received a MAX assignment. -/
def MaxLabelsOffRoots (s : State V) (F : BudForest V) : Prop :=
  ∀ v, F.root v = v → s.maxLabel v = none

theorem initial_maxLabelsOffRoots (M : Matching G) (F : BudForest V) :
    MaxLabelsOffRoots (initial M) F := by
  intro v _
  rfl

section Finite
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

namespace PetalRecord

/-- Every root surviving an actual petal was already a root beforehand. -/
theorem after_root_was_root (R : PetalRecord M) (v : Fin n)
    (hv : R.after.root v = v) : R.forest.root v = v := by
  have hr := R.after_root v
  rw [hv] at hr
  split at hr
  · have hb := R.forest.root_of_fixed R.bottleneck
      (R.selected_fixed R.bottleneck R.trees.bottleneck_mem)
    simpa only [hr] using hb
  · exact hr.symm

/-- MAX labels only the newly absorbed roots; every surviving root retains its
previously unknown maximum label, including the selected bottleneck itself. -/
theorem maxEvent_maxLabelsOffRoots [DecidableRel G.Adj] (R : PetalRecord M) (i : Nat)
    (h : MaxLabelsOffRoots R.prior R.forest) :
    MaxLabelsOffRoots (R.maxEvent i).1 R.after := by
  intro v hv
  have hold := R.after_root_was_root v hv
  have hnot : v ∉ R.newRoots := by
    intro hnew
    obtain ⟨hsel, hne⟩ := (R.mem_newRoots v).1 hnew
    have hafter := R.after_selected v (by simpa only [selectedFiber, hold] using hsel)
    exact hne (hv.symm.trans hafter)
  exact (R.maxEvent_outside i v hnot).trans (h v hold)

end PetalRecord

variable [DecidableRel G.Adj]

theorem scanLevelWithBuds_maxLabelsOffRoots (M : Matching G) (i : Nat)
    (s : State (Fin n)) (F : BudForest (Fin n)) (h : BudGraphInvariant M i s F)
    (hoff : MaxLabelsOffRoots s F) :
    MaxLabelsOffRoots (scanLevelWithBuds M i s F h).1 (scanLevelWithBuds M i s F h).2 := by
  intro v hv
  rw [scanLevelWithBuds_root] at hv
  exact (scanCandidates_maxLabel (allCandidates n) s i v).trans (hoff v hv)

namespace CurrentBucketState

theorem afterPetal_maxLabelsOffRoots {i cut : Nat} (R : PetalRecord M)
    (hP : Nonempty (CurrentBridgeRepresentation M cut R.invariant))
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hten : R.tenacity = cut + 2) (hstageTen : cut + 2 = 2 * i + 1)
    (hcap : R.cap = i + 1) (hstage : StageState M (i + 1) (2 * i + 1) R.prior)
    (hoff : MaxLabelsOffRoots R.prior R.forest) :
    MaxLabelsOffRoots (afterPetal R hP hc htop hten hstageTen hcap hstage).state
      (afterPetal R hP hc htop hten hstageTen hcap hstage).forest :=
  R.maxEvent_maxLabelsOffRoots i hoff

end CurrentBucketState

/-- The complete bucket loop preserves the absence of MAX labels at its final
roots, whether it exhausts the list or stops at a disjoint-path witness. -/
theorem runCurrentBucket_maxLabelsOffRoots {i cut : Nat}
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) (B : CurrentBucketState M i cut)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (hoff : MaxLabelsOffRoots B.state B.forest) :
    MaxLabelsOffRoots (runCurrentBucket hc htop hstageTen B es hqueued).1.state.state
      (runCurrentBucket hc htop hstageTen B es hqueued).1.state.forest := by
  induction es generalizing B with
  | nil => simpa only [runCurrentBucket, CurrentBucketOutcome.state] using hoff
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    rw [runCurrentBucket]
    split
    · exact ih B _ hoff
    · split
      · exact hoff
      · apply ih
        exact PetalRecord.maxEvent_maxLabelsOffRoots _ i hoff

end Finite
end MaximumMatching.Search

end CurrentBucketRootLabels
