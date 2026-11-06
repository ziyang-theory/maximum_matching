import MaximumMatching.MinComplete
import MaximumMatching.BridgeClassification

/-! Semantic correctness of the actual bridge lists and tenacity buckets.
These results concern stored edges and executable enqueue/scan operations;
completion of MAX's support discovery remains separate. -/
namespace MaximumMatching.Search
variable {V : Type} {G : Graph V} {M : Matching G}
variable [DecidableEq V]

/-- Every operationally computed finite edge tenacity is its semantic value.
Unknown parity labels cannot manufacture a finite tenacity. -/
theorem edgeTenacity_sound (s : State V) (hs : LabelsSound M s) (u v : V) (t : Nat)
    (ht : edgeTenacity M s u v = some t) : MaximumMatching.edgeTenacity M u v = some t := by
  unfold edgeTenacity at ht
  by_cases hm : M.mate u = some v
  · simp only [hm, ite_true] at ht
    cases hu : parityLabel s u 1 with
    | none => simp [hu] at ht
    | some a =>
      cases hv : parityLabel s v 1 with
      | none => simp [hu, hv] at ht
      | some b =>
        have heq : a + b + 1 = t := by simpa [hu, hv] using ht
        have hau := parityLabel_sound s hs u 1 a hu
        have hbv := parityLabel_sound s hs v 1 b hv
        simp only [MaximumMatching.edgeTenacity, hm, ite_true, matchedEdgeTenacity,
          hau, hbv, levelAdd, Option.map_some, heq]
  · simp only [hm, ite_false] at ht
    cases hu : parityLabel s u 0 with
    | none => simp [hu] at ht
    | some a =>
      cases hv : parityLabel s v 0 with
      | none => simp [hu, hv] at ht
      | some b =>
        have heq : a + b + 1 = t := by simpa [hu, hv] using ht
        have hau := parityLabel_sound s hs u 0 a hu
        have hbv := parityLabel_sound s hs v 0 b hv
        simp only [MaximumMatching.edgeTenacity, hm, ite_false,
          hau, hbv, levelAdd, Option.map_some, heq]

def PropsSound (M : Matching G) (s : State V) : Prop :=
  ∀ u v, (u, v) ∈ s.props → Predecessor M u v

def BridgesSound (M : Matching G) (s : State V) : Prop :=
  ∀ u v, (u, v) ∈ s.bridges → Bridge M u v

def BucketsSound (M : Matching G) (s : State V) : Prop :=
  ∀ t u v, (u, v) ∈ s.bucket t →
    Bridge M u v ∧ MaximumMatching.edgeTenacity M u v = some t

def ClassificationSound (M : Matching G) (s : State V) : Prop :=
  PropsSound M s ∧ BridgesSound M s ∧ BucketsSound M s

omit [DecidableEq V] in
theorem enqueue_bucketsSound (s : State V) (hs : BucketsSound M s) (u v : V)
    (hb : Bridge M u v) (t : Option Nat)
    (ht : ∀ k, t = some k → MaximumMatching.edgeTenacity M u v = some k) :
    BucketsSound M (enqueue s u v t) := by
  cases t with
  | none => exact hs
  | some k =>
    intro j a b hmem
    change (a, b) ∈ (if j = k then (u, v) :: s.bucket j else s.bucket j) at hmem
    split at hmem
    next hj =>
      rcases List.mem_cons.mp hmem with he | hold
      · have he' := Prod.mk.inj he
        exact ⟨by simpa only [he'.1, he'.2] using hb,
          by simpa only [he'.1, he'.2, hj] using ht k rfl⟩
      · exact hs j a b hold
    next _ => exact hs j a b hmem

/-- Every actual classification by MIN is sound, including deferred bridges
whose operational tenacity is still unknown. -/
theorem scanCandidate_classificationSound [DecidableRel G.Adj]
    (s : State V) (i : Nat) (u v : V) (hi : MinInvariant M i s)
    (hc : ClassificationSound M s) : ClassificationSound M (scanCandidate M i u v s) := by
  unfold scanCandidate
  split
  next hg =>
    have hlevel := parityLabel_sound s hi.1 u (i % 2) i hg.2.1
    unfold scan
    split
    · exact hc
    next hseen =>
      have hfalse : seen s u v = false := Bool.eq_false_iff.mpr hseen
      split
      next ha =>
        have hp := (scan_assigns_semantic s i u v hi.2.1 hlevel hg.1 hg.2.2 hfalse ha).2.1
        refine ⟨?_, hc.2.1, hc.2.2⟩
        intro a b hmem
        rcases List.mem_cons.mp hmem with he | hold
        · have he' := Prod.mk.inj he
          simpa only [he'.1, he'.2] using hp
        · exact hc.1 a b hold
      next ha =>
        have hb := scan_rejects_bridge s i u v hi.1 hi.2.2.1 hlevel hg.1 hfalse
          (Bool.eq_false_iff.mpr ha)
        have hs' : BridgesSound M { s with bridges := (u, v) :: s.bridges } := by
          intro a b hmem
          rcases List.mem_cons.mp hmem with he | hold
          · have he' := Prod.mk.inj he
            simpa only [he'.1, he'.2] using hb
          · exact hc.2.1 a b hold
        have hbs := enqueue_bucketsSound
          { { s with scanned := (u, v) :: s.scanned } with bridges := (u, v) :: s.bridges }
          hc.2.2 u v hb (edgeTenacity M s u v) (fun k hk => edgeTenacity_sound s hi.1 u v k hk)
        refine ⟨?_, ?_, hbs⟩
        · unfold enqueue; split <;> exact hc.1
        · unfold enqueue; split <;> exact hs'
  next _ => exact hc

theorem scanCandidates_classificationSound [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (i : Nat) (hi : MinInvariant M i s)
    (hc : ClassificationSound M s) : ClassificationSound M (scanCandidates M i xs s) := by
  induction xs generalizing s with
  | nil => exact hc
  | cons e es ih =>
    exact ih _ (scanCandidate_minInvariant s i e.1 e.2 hi)
      (scanCandidate_classificationSound s i e.1 e.2 hi hc)

omit [DecidableEq V] in
theorem initial_classificationSound (M : Matching G) : ClassificationSound M (initial M) := by
  simp [ClassificationSound, PropsSound, BridgesSound, BucketsSound, initial]

/-- The first concrete MIN stage correctly classifies and buckets every edge
it stores, independently of any structural blossom or MAX theorem. -/
theorem initial_scanLevel_classificationSound {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) : ClassificationSound M (scanLevel M 0 (initial M)) :=
  scanCandidates_classificationSound (allCandidates n) (initial M) 0
    (initial_minInvariant M) (initial_classificationSound M)

/-- Reconsider stored bridge tenacities after MAX makes a parity label known. -/
def refreshBridges (M : Matching G) (edges : List (V × V)) (s : State V) : State V :=
  edges.foldl (fun state e => enqueue state e.1 e.2 (edgeTenacity M state e.1 e.2)) s

omit [DecidableEq V] in
theorem enqueue_minLabel (s : State V) (u v w : V) (t : Option Nat) :
    (enqueue s u v t).minLabel w = s.minLabel w := by cases t <;> rfl

omit [DecidableEq V] in
theorem enqueue_maxLabel (s : State V) (u v w : V) (t : Option Nat) :
    (enqueue s u v t).maxLabel w = s.maxLabel w := by cases t <;> rfl

omit [DecidableEq V] in
theorem enqueue_bucket_mono (s : State V) (u v a b : V) (t : Option Nat) (k : Nat)
    (h : (a, b) ∈ s.bucket k) : (a, b) ∈ (enqueue s u v t).bucket k := by
  cases t with
  | none => exact h
  | some j =>
    change (a, b) ∈ (if k = j then (u, v) :: s.bucket k else s.bucket k)
    split
    · exact List.mem_cons_of_mem _ h
    · exact h

omit [DecidableEq V] in
theorem enqueue_mem (s : State V) (u v : V) (t : Nat) :
    (u, v) ∈ (enqueue s u v (some t)).bucket t := by simp [enqueue]

theorem refreshBridges_labels (M : Matching G) (edges : List (V × V)) (s : State V) :
    (∀ v, (refreshBridges M edges s).minLabel v = s.minLabel v) ∧
      (∀ v, (refreshBridges M edges s).maxLabel v = s.maxLabel v) := by
  induction edges generalizing s with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons e es ih =>
    have hh := ih (enqueue s e.1 e.2 (edgeTenacity M s e.1 e.2))
    exact ⟨fun v => (hh.1 v).trans (enqueue_minLabel s e.1 e.2 v _),
      fun v => (hh.2 v).trans (enqueue_maxLabel s e.1 e.2 v _)⟩

theorem edgeTenacity_enqueue (s : State V) (a b u v : V) (t : Option Nat) :
    edgeTenacity M (enqueue s a b t) u v = edgeTenacity M s u v := by cases t <;> rfl

theorem refreshBridges_bucket_mono (M : Matching G) (edges : List (V × V)) (s : State V)
    (u v : V) (t : Nat) (h : (u, v) ∈ s.bucket t) :
    (u, v) ∈ (refreshBridges M edges s).bucket t := by
  induction edges generalizing s with
  | nil => exact h
  | cons e es ih => exact ih _ (enqueue_bucket_mono s e.1 e.2 u v _ t h)

theorem refreshBridges_complete (M : Matching G) (edges : List (V × V)) (s : State V)
    (u v : V) (t : Nat) (hmem : (u, v) ∈ edges) (ht : edgeTenacity M s u v = some t) :
    (u, v) ∈ (refreshBridges M edges s).bucket t := by
  induction edges generalizing s with
  | nil => simp at hmem
  | cons e es ih =>
    rcases List.mem_cons.mp hmem with he | he
    · subst e
      apply refreshBridges_bucket_mono M es (enqueue s u v (edgeTenacity M s u v)) u v t
      change (u, v) ∈ (enqueue s u v (edgeTenacity M s u v)).bucket t
      rw [ht]
      exact enqueue_mem s u v t
    · exact ih _ he ((edgeTenacity_enqueue s e.1 e.2 u v _).trans ht)

theorem refreshBridges_bucketsSound (M : Matching G) (edges : List (V × V)) (s : State V)
    (hs : LabelsSound M s) (hb : BucketsSound M s)
    (he : ∀ u v, (u, v) ∈ edges → Bridge M u v) :
    BucketsSound M (refreshBridges M edges s) := by
  induction edges generalizing s with
  | nil => exact hb
  | cons e es ih =>
    apply ih _
    · constructor <;> intro v k hv
      · apply hs.1 v k
        simpa only [enqueue_minLabel] using hv
      · apply hs.2 v k
        simpa only [enqueue_maxLabel] using hv
    · exact enqueue_bucketsSound s hb e.1 e.2 (he e.1 e.2 (by simp)) _
        (fun k hk => edgeTenacity_sound s hs e.1 e.2 k hk)
    · intro u v hmem
      exact he u v (List.mem_cons_of_mem _ hmem)

/-- The concrete MAX incident-edge refresh considers the already registered
bridge orientations touching the newly labeled vertex. -/
def refreshIncident (M : Matching G) (v : V) (s : State V) : State V :=
  refreshBridges M (s.bridges.filter fun e => decide (e.1 = v ∨ e.2 = v)) s

theorem refreshIncident_bucketsSound (M : Matching G) (v : V) (s : State V)
    (hs : LabelsSound M s) (hc : ClassificationSound M s) :
    BucketsSound M (refreshIncident M v s) := by
  apply refreshBridges_bucketsSound M _ s hs hc.2.2
  intro a b hmem
  exact hc.2.1 a b (List.mem_filter.mp hmem).1

theorem refreshIncident_complete (M : Matching G) (w u v : V) (s : State V) (t : Nat)
    (hbridge : (u, v) ∈ s.bridges) (hincident : u = w ∨ v = w)
    (ht : edgeTenacity M s u v = some t) :
    (u, v) ∈ (refreshIncident M w s).bucket t := by
  apply refreshBridges_complete M _ s u v t
  · exact List.mem_filter.mpr ⟨hbridge, by simpa only [decide_eq_true_eq] using hincident⟩
  · exact ht

end MaximumMatching.Search
