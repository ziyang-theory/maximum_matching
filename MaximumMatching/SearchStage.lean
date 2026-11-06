import MaximumMatching.MaxBridgeRefresh

section BridgePending

/-! Event invariant for bridge scheduling across MIN and MAX. A finite-known
unmatched bridge is already queued, unless one of its outer endpoints has not
yet reached its MIN scan level. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

theorem outer_of_even_minlevel (v : V) (k : Nat)
    (hmin : minlevel M v = some k) (hke : k % 2 = 0) : Outer M v := by
  have he : evenlevel M v = some k := by simpa only [hke] using level_of_minlevel v k hmin
  cases ho : oddlevel M v with
  | none => simp [Outer, he, ho, levelLT]
  | some o =>
    have hop := level_parity M 1 v o ho
    have hm : min k o = k := by simpa only [minlevel, he, ho, levelMin, Option.some.injEq] using hmin
    change levelLT (evenlevel M v) (oddlevel M v)
    rw [he, ho]
    change k < o
    omega

namespace Search
variable [DecidableEq V]

def MaxLabelsHaveMin (s : State V) : Prop :=
  ∀ v k, s.maxLabel v = some k → ∃ lo, s.minLabel v = some lo

def UnmatchedPending (M : Matching G) (i : Nat) (s : State V) : Prop :=
  ∀ u v t, Bridge M u v → M.mate u ≠ some v → edgeTenacity M s u v = some t →
    EdgeInBucket s t u v ∨
      (Outer M u ∧ ∃ k, minlevel M u = some k ∧ i ≤ k) ∨
      (Outer M v ∧ ∃ k, minlevel M v = some k ∧ i ≤ k)

omit [DecidableEq V] in
theorem initial_maxLabelsHaveMin (M : Matching G) : MaxLabelsHaveMin (initial M) := by
  intro v k h
  change none = some k at h
  contradiction

theorem scanCandidate_maxLabelsHaveMin [DecidableRel G.Adj]
    (s : State V) (i : Nat) (a b : V) (hi : MinInvariant M i s) (hm : MaxLabelsHaveMin s) :
    MaxLabelsHaveMin (scanCandidate M i a b s) := by
  intro v k hv
  have hprev : s.maxLabel v = some k := (scanCandidate_preserves_maxLabel s i a b v).symm.trans hv
  obtain ⟨lo, hlo⟩ := hm v k hprev
  exact ⟨lo, scanCandidate_preserves_minLabel s i a b v lo hi.1 hi.2.1 hlo⟩

theorem scanCandidate_minLabel_origin [DecidableRel G.Adj]
    (s : State V) (i : Nat) (a b v : V) (k : Nat)
    (h : (scanCandidate M i a b s).minLabel v = some k) :
    s.minLabel v = some k ∨ (v = b ∧ k = i + 1) := by
  unfold scanCandidate at h
  split at h
  · unfold scan at h
    split at h
    · exact Or.inl h
    · split at h
      · change (if v = b then some (i + 1) else s.minLabel v) = some k at h
        split at h
        next he => exact Or.inr ⟨he, (Option.some.inj h).symm⟩
        next _ => exact Or.inl h
      · unfold enqueue at h
        split at h <;> exact Or.inl h
  · exact Or.inl h

/-- A newly available even parity label during MIN is necessarily a newly
assigned outer minlevel i+1. An inner vertex's even maxlevel cannot appear in
MIN, because MAX labels are unchanged. -/
theorem scanCandidate_evenLabel_origin [DecidableRel G.Adj]
    (s : State V) (i : Nat) (a b v : V) (k : Nat)
    (hi : MinInvariant M i s) (hm : MaxLabelsHaveMin s)
    (hk : parityLabel (scanCandidate M i a b s) v 0 = some k) :
    parityLabel s v 0 = some k ∨
      (Outer M v ∧ minlevel M v = some (i + 1) ∧ (i + 1) % 2 = 0) := by
  cases hlo : s.minLabel v with
  | some lo =>
    have hl' := scanCandidate_preserves_minLabel s i a b v lo hi.1 hi.2.1 hlo
    exact Or.inl (by simpa only [parityLabel, hl', hlo, scanCandidate_preserves_maxLabel] using hk)
  | none =>
    have hmax : s.maxLabel v = none := by
      cases hx : s.maxLabel v with
      | none => rfl
      | some x =>
        obtain ⟨j, hj⟩ := hm v x hx
        rw [hlo] at hj
        contradiction
    obtain ⟨lo, hnew⟩ := parityLabel_has_minLabel _ v 0 k hk
    have he : lo = i + 1 := by
      rcases scanCandidate_minLabel_origin s i a b v lo hnew with hold | hh
      · rw [hlo] at hold; contradiction
      · exact hh.2
    subst lo
    have hpar : (i + 1) % 2 = 0 := by
      simp only [parityLabel, hnew, scanCandidate_preserves_maxLabel, hmax] at hk
      by_cases hp : (i + 1) % 2 = 0
      · exact hp
      · simp [hp] at hk
    have hmin := (scanCandidate_labelsSound s i a b hi.1 hi.2.1).1 v (i + 1) hnew
    exact Or.inr ⟨outer_of_even_minlevel v (i + 1) hmin hpar, hmin, hpar⟩

/-- A newly finite unmatched-edge tenacity in MIN has a newly assigned outer
endpoint. This is the event needed to advance the pending-bridge invariant. -/
theorem scanCandidate_unmatchedTenacity_origin [DecidableRel G.Adj]
    (s : State V) (i : Nat) (a b u v : V) (t : Nat)
    (hi : MinInvariant M i s) (hm : MaxLabelsHaveMin s) (hn : M.mate u ≠ some v)
    (ht : edgeTenacity M (scanCandidate M i a b s) u v = some t) :
    edgeTenacity M s u v = some t ∨
      (Outer M u ∧ minlevel M u = some (i + 1) ∧ (i + 1) % 2 = 0) ∨
      (Outer M v ∧ minlevel M v = some (i + 1) ∧ (i + 1) % 2 = 0) := by
  simp only [edgeTenacity, hn, ite_false] at ht
  cases hu : parityLabel (scanCandidate M i a b s) u 0 with
  | none => simp [hu] at ht
  | some x =>
    cases hv : parityLabel (scanCandidate M i a b s) v 0 with
    | none => simp [hu, hv] at ht
    | some y =>
      rcases scanCandidate_evenLabel_origin s i a b u x hi hm hu with huold | hunew
      · rcases scanCandidate_evenLabel_origin s i a b v y hi hm hv with hvold | hvnew
        · exact Or.inl (by simpa [edgeTenacity, hn, huold, hvold, hu, hv] using ht)
        · exact Or.inr (Or.inr hvnew)
      · exact Or.inr (Or.inl hunew)

theorem scanCandidates_unmatchedTenacity_origin [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (i : Nat) (u v : V) (t : Nat)
    (hi : MinInvariant M i s) (hm : MaxLabelsHaveMin s) (hn : M.mate u ≠ some v)
    (ht : edgeTenacity M (scanCandidates M i xs s) u v = some t) :
    edgeTenacity M s u v = some t ∨
      (Outer M u ∧ minlevel M u = some (i + 1) ∧ (i + 1) % 2 = 0) ∨
      (Outer M v ∧ minlevel M v = some (i + 1) ∧ (i + 1) % 2 = 0) := by
  induction xs generalizing s with
  | nil => exact Or.inl ht
  | cons e es ih =>
    rcases ih _ (scanCandidate_minInvariant s i e.1 e.2 hi)
      (scanCandidate_maxLabelsHaveMin s i e.1 e.2 hi hm) ht with hold | hnew
    · exact scanCandidate_unmatchedTenacity_origin s i e.1 e.2 u v t hi hm hn hold
    · exact Or.inr hnew

/-- An outer endpoint's appropriate level is the first possible scan level of
its unmatched edge, even when the other endpoint is inner. -/
theorem outer_endpoint_unseen (s : State V) (i : Nat) (u v : V)
    (hbefore : ScannedBefore M i s) (hu : Outer M u) (hmin : minlevel M u = some i)
    (hadj : G.Adj u v) (hn : M.mate u ≠ some v) : seen s u v = false := by
  have hue : evenlevel M u = some i := (minlevel_eq_even_of_outer u hu).symm.trans hmin
  have hip := level_parity M 0 u i hue
  apply Bool.eq_false_iff.mpr
  intro hs
  have hmem : (u, v) ∈ s.scanned ∨ (v, u) ∈ s.scanned := by simpa only [seen, decide_eq_true_eq] using hs
  rcases hmem with hmem | hmem
  · obtain ⟨j, hji, hj, hpar⟩ := hbefore u v hmem
    have hjp : j % 2 = 0 := by have h : j % 2 ≠ 1 := fun h => hn (hpar.2 h); omega
    rw [hjp] at hj
    have he := Option.some.inj (hj.symm.trans hue)
    omega
  · obtain ⟨j, hji, hj, hpar⟩ := hbefore v u hmem
    have hnm : M.mate v ≠ some u := fun h => hn (M.symm h)
    have hjp : j % 2 = 0 := by have h : j % 2 ≠ 1 := fun h => hnm (hpar.2 h); omega
    obtain ⟨k, hk, hkj⟩ := minlevel_neighbor_bound v u j hj (G.symm hadj) hpar
    have hki := Option.some.inj (hk.symm.trans hmin)
    omega

theorem scanCandidates_bucket_mono [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (i : Nat) (u v : V) (t : Nat)
    (h : (u, v) ∈ s.bucket t) : (u, v) ∈ (scanCandidates M i xs s).bucket t := by
  induction xs generalizing s with
  | nil => exact h
  | cons e es ih => exact ih _ (scanCandidate_bucket_mono s i e.1 e.2 u v t h)

theorem initial_unmatchedPending (M : Matching G) : UnmatchedPending M 0 (initial M) := by
  intro u v t _ _ ht
  obtain ⟨⟨lo, hlo⟩, _⟩ := edgeTenacity_has_minLabels (initial M) u v t ht
  have hbound := initial_minLabelsBound M u lo hlo
  have he : lo = 0 := by omega
  subst lo
  have hm := (initial_labelsSound M).1 u 0 hlo
  exact Or.inr (Or.inl ⟨outer_of_even_minlevel u 0 hm rfl, 0, hm, Nat.le_refl _⟩)

/-- Completing MIN advances the pending outer endpoint from level i to i+1.
An endpoint exactly at level i triggers a fresh scan and queues its bridge. -/
theorem scanLevel_unmatchedPending {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (s : State (Fin n)) (i : Nat)
    (hi : MinInvariant M i s) (hf : FrontierAvailable M i s) (hm : MaxLabelsHaveMin s)
    (hb : ScannedBefore M i s) (hp : UnmatchedPending M i s) :
    UnmatchedPending M (i + 1) (scanLevel M i s) := by
  intro u v t hbridge hn ht
  rcases scanCandidates_unmatchedTenacity_origin (allCandidates n) s i u v t hi hm hn ht with hold | hnew | hnew
  · have outer_queued (a b : Fin n) (hab : Bridge M a b) (hnab : M.mate a ≠ some b)
        (hta : edgeTenacity M s a b = some t) (ha : Outer M a) (hmin : minlevel M a = some i) :
        EdgeInBucket (scanLevel M i s) t a b := by
      have hae := (minlevel_eq_even_of_outer a ha).symm.trans hmin
      have hip := level_parity M 0 a i hae
      apply scanLevel_queues_known M s i a b t hi hf hab
        (by simpa only [hip] using hae) (by simp [hnab, hip]) hta
      intro hseen
      have hfalse := outer_endpoint_unseen s i a b hb ha hmin hab.1 hnab
      rw [hfalse] at hseen
      contradiction
    rcases hp u v t hbridge hn hold with hqueued | hu | hv
    · rcases hqueued with hmem | hmem
      · exact Or.inl (Or.inl (scanCandidates_bucket_mono (allCandidates n) s i u v t hmem))
      · exact Or.inl (Or.inr (scanCandidates_bucket_mono (allCandidates n) s i v u t hmem))
    · obtain ⟨hu, k, hk, hik⟩ := hu
      by_cases hki : k = i
      · subst k
        exact Or.inl (outer_queued u v hbridge hn hold hu hk)
      · exact Or.inr (Or.inl ⟨hu, k, hk, by omega⟩)
    · obtain ⟨hv, k, hk, hik⟩ := hv
      by_cases hki : k = i
      · subst k
        have hnm : M.mate v ≠ some u := fun h => hn (M.symm h)
        have hq := outer_queued v u (bridge_symm hbridge) hnm ((edgeTenacity_comm s v u).trans hold) hv hk
        exact Or.inl hq.symm
      · exact Or.inr (Or.inr ⟨hv, k, hk, by omega⟩)
  · exact Or.inr (Or.inl ⟨hnew.1, i + 1, hnew.2.1, Nat.le_refl _⟩)
  · exact Or.inr (Or.inr ⟨hnew.1, i + 1, hnew.2.1, Nat.le_refl _⟩)

theorem edgeTenacity_of_labels_eq (s r : State V) (u v : V)
    (hmin : ∀ w, r.minLabel w = s.minLabel w) (hmax : ∀ w, r.maxLabel w = s.maxLabel w) :
    edgeTenacity M r u v = edgeTenacity M s u v := by
  simp only [edgeTenacity, parityLabel, hmin, hmax]

theorem assignMax_minLabel (s : State V) (t : Nat) (u v : V) :
    (assignMax s t u).minLabel v = s.minLabel v := by unfold assignMax; split <;> rfl

theorem assignMax_other_evenLabel (s : State V) (t : Nat) (u v : V) (hne : v ≠ u) :
    parityLabel (assignMax s t u) v 0 = parityLabel s v 0 := by
  unfold assignMax
  split
  · rfl
  · simp only [parityLabel, hne, ite_false]

theorem assignMax_evenLabel_of_even (s : State V) (t : Nat) (u v : V) (lo : Nat)
    (hl : s.minLabel u = some lo) (hp : lo % 2 = 0) :
    parityLabel (assignMax s t u) v 0 = parityLabel s v 0 := by
  by_cases he : v = u
  · subst v
    simp [assignMax, hl, parityLabel, hp]
  · exact assignMax_other_evenLabel s t u v he

theorem maxProcessVertex_edgeTenacity {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (w u v : Fin n) (s : State (Fin n)) :
    edgeTenacity M (maxProcessVertex M i w s) u v =
      edgeTenacity M (assignMax s (2 * i + 1) w) u v := by
  unfold maxProcessVertex
  dsimp only
  split
  · rfl
  · split
    · apply edgeTenacity_of_labels_eq
      · intro z; exact (refreshKnownEdges_labels _ _ z).1
      · intro z; exact (refreshKnownEdges_labels _ _ z).2
    · rfl

theorem maxProcessVertex_bucket_mono {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (w u v : Fin n) (s : State (Fin n)) (t : Nat)
    (h : (u, v) ∈ s.bucket t) : (u, v) ∈ (maxProcessVertex M i w s).bucket t := by
  have ha : (u, v) ∈ (assignMax s (2 * i + 1) w).bucket t := by
    unfold assignMax; split <;> exact h
  unfold maxProcessVertex
  dsimp only
  split
  · exact ha
  · split
    · exact refreshKnownEdges_bucket_mono _ _ u v t ha
    · exact ha

/-- A newly known unmatched bridge at a MAX assignment is queued by that same
vertex step. Otherwise it was already known before the assignment. -/
theorem maxProcessVertex_unmatched_ready {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (s : State (Fin n)) (i k : Nat) (w u v : Fin n) (t : Nat)
    (hi : MinInvariant M k s) (hwt : tenacity M w = some (2 * i + 1))
    (hb : Bridge M u v) (hn : M.mate u ≠ some v)
    (ht : edgeTenacity M (maxProcessVertex M i w s) u v = some t) :
    EdgeInBucket (maxProcessVertex M i w s) t u v ∨ edgeTenacity M s u v = some t := by
  have hta := (maxProcessVertex_edgeTenacity M i w u v s).symm.trans ht
  cases hlo : s.minLabel w with
  | none =>
    exact Or.inr (by simpa only [assignMax, hlo] using hta)
  | some lo =>
    by_cases hp : lo % 2 = 1
    · by_cases hinc : u = w ∨ v = w
      · have hassigned : (assignMax s (2 * i + 1) w).minLabel w = some lo := by simp [assignMax, hlo]
        have hmem := refreshIncidentAll_complete M w u v _ k t
          (assignMax_minInvariant s k (2 * i + 1) w hi hwt) hb hinc hta
        exact Or.inl (Or.inl (by simpa only [maxProcessVertex, hassigned, hp, ite_true] using hmem))
      · have hu : u ≠ w := fun h => hinc (Or.inl h)
        have hv : v ≠ w := fun h => hinc (Or.inr h)
        exact Or.inr (by simpa only [edgeTenacity, hn, ite_false,
          assignMax_other_evenLabel s (2 * i + 1) w u hu,
          assignMax_other_evenLabel s (2 * i + 1) w v hv] using hta)
    · have he : lo % 2 = 0 := by omega
      exact Or.inr (by simpa only [edgeTenacity, hn, ite_false,
        assignMax_evenLabel_of_even s (2 * i + 1) w u lo hlo he,
        assignMax_evenLabel_of_even s (2 * i + 1) w v lo hlo he] using hta)

theorem maxProcessVertex_unmatchedPending {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (s : State (Fin n)) (i k : Nat) (w : Fin n)
    (hi : MinInvariant M k s) (hwt : tenacity M w = some (2 * i + 1))
    (hp : UnmatchedPending M k s) : UnmatchedPending M k (maxProcessVertex M i w s) := by
  intro u v t hb hn ht
  rcases maxProcessVertex_unmatched_ready M s i k w u v t hi hwt hb hn ht with hq | hold
  · exact Or.inl hq
  · rcases hp u v t hb hn hold with hq | houter
    · rcases hq with hmem | hmem
      · exact Or.inl (Or.inl (maxProcessVertex_bucket_mono M i w u v s t hmem))
      · exact Or.inl (Or.inr (maxProcessVertex_bucket_mono M i w v u s t hmem))
    · exact Or.inr houter

end Search
end MaximumMatching

end BridgePending

section BridgeComplete

/-! Completeness of the current tenacity bucket after concrete MIN. Earlier
MAX assignment/refresh events are captured by initialized and preserved state
invariants. No completeness of the current MAX support search is assumed. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

theorem semantic_edgeTenacity_comm (u v : V) : edgeTenacity M u v = edgeTenacity M v u := by
  classical
  by_cases hm : M.mate u = some v
  · have hm' := M.symm hm
    simp only [edgeTenacity, hm, hm', ite_true, matchedEdgeTenacity]
    cases he : oddlevel M u <;> cases hf : oddlevel M v <;> simp [levelAdd, Nat.add_comm]
  · have hm' : M.mate v ≠ some u := fun h => hm (M.symm h)
    simp only [edgeTenacity, hm, hm', ite_false]
    cases he : evenlevel M u <;> cases hf : evenlevel M v <;> simp [levelAdd, Nat.add_comm]

theorem unmatched_bridge_outer_minlevel_bound (u v : V) (i k : Nat)
    (hb : Bridge M u v) (hn : M.mate u ≠ some v) (hu : Outer M u)
    (ht : edgeTenacity M u v = some (2 * i + 1)) (hk : minlevel M u = some k) : k ≤ i := by
  obtain ⟨t, hut, hti⟩ := (unmatched_bridge_tenacity hb hn (2 * i + 1) ht).1 hu
  obtain ⟨e, o, he, ho, _, _, hsum⟩ := finite_levels_of_tenacity u t hut
  have hmin : minlevel M u = some e := (minlevel_eq_even_of_outer u hu).trans he
  have hek := Option.some.inj (hmin.symm.trans hk)
  have hlt : e < o := by simpa only [Outer, he, ho, levelLT] using hu
  omega

namespace Search
variable [DecidableEq V]

omit [DecidableEq V] in
/-- Lemma 8.1 puts a bridge endpoint's required evenlevel either at a known
outer minlevel ≤i or at an inner maxlevel assigned at a strictly earlier
vertex tenacity. Both cases use actual operational label lookup. -/
theorem unmatched_bridge_evenLabel_available (s : State V) (i : Nat) (u v : V)
    (hc : MinCompleteBelow M i s) (hx : MaxCompleteBelowTenacity M (2 * i + 1) s)
    (hb : Bridge M u v) (hn : M.mate u ≠ some v)
    (ht : MaximumMatching.edgeTenacity M u v = some (2 * i + 1))
    (e : Nat) (he : evenlevel M u = some e) : parityLabel s u 0 = some e := by
  have hep := level_parity M 0 u e he
  by_cases hu : Outer M u
  · have hmin : minlevel M u = some e := (minlevel_eq_even_of_outer u hu).trans he
    have hei := unmatched_bridge_outer_minlevel_bound u v i e hb hn hu ht hmin
    have hlabel := hc u e hmin hei
    simp [parityLabel, hlabel, hep]
  · obtain ⟨k, hk, _⟩ := minlevel_le_of_level u e (by simpa only [hep] using he)
    have hinner : Inner M u := ⟨⟨k, hk⟩, hu⟩
    obtain ⟨t, hut, hti⟩ := (unmatched_bridge_tenacity hb hn (2 * i + 1) ht).2 hinner
    obtain ⟨o, ho, hoe, hmin⟩ := inner_oddlevel_lt_evenlevel u e he hinner
    have hop := level_parity M 1 u o ho
    have hsum : e + o = t := by simpa only [tenacity, he, ho, levelAdd, Option.some.injEq] using hut
    have hmax : maxlevel M u = some e := by simp [maxlevel, he, ho, levelMax, Nat.max_eq_left (by omega : o ≤ e)]
    have hlabel := hc u o hmin (by omega)
    have hlabelmax := (hx u t hut hti).trans hmax
    simp [parityLabel, hlabel, hlabelmax, hop, hep]

/-- Every unmatched bridge of current tenacity already has a computable
operational tenacity before this MIN pass, including both mixed and inner cases. -/
theorem unmatched_bridge_tenacity_available (s : State V) (i : Nat) (u v : V)
    (hc : MinCompleteBelow M i s) (hx : MaxCompleteBelowTenacity M (2 * i + 1) s)
    (hb : Bridge M u v) (hn : M.mate u ≠ some v)
    (ht : MaximumMatching.edgeTenacity M u v = some (2 * i + 1)) :
    edgeTenacity M s u v = some (2 * i + 1) := by
  have ht' : (levelAdd (evenlevel M u) (evenlevel M v)).map (· + 1) = some (2 * i + 1) := by
    simpa only [MaximumMatching.edgeTenacity, hn, ite_false] using ht
  cases he : evenlevel M u with
  | none => simp [he, levelAdd] at ht'
  | some e =>
    cases hf : evenlevel M v with
    | none => simp [he, hf, levelAdd] at ht'
    | some f =>
      have he' := unmatched_bridge_evenLabel_available s i u v hc hx hb hn ht e he
      have hnm : M.mate v ≠ some u := fun h => hn (M.symm h)
      have hf' := unmatched_bridge_evenLabel_available s i v u hc hx (bridge_symm hb) hnm
        ((semantic_edgeTenacity_comm v u).trans ht) f hf
      simpa [edgeTenacity, hn, he', hf', he, hf, levelAdd] using ht'

theorem scanCandidates_preserves_edgeTenacity [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (i : Nat) (u v : V) (t : Nat)
    (hi : MinInvariant M i s) (ht : edgeTenacity M s u v = some t) :
    edgeTenacity M (scanCandidates M i xs s) u v = some t := by
  induction xs generalizing s with
  | nil => exact ht
  | cons e es ih =>
    exact ih _ (scanCandidate_minInvariant s i e.1 e.2 hi)
      (scanCandidate_preserves_edgeTenacity s i e.1 e.2 u v t hi ht)

/-- Task 2: the actual MIN enumeration has queued every bridge of tenacity
2i+1, in either stored orientation. The mixed/inner cases use the pending-event
invariant maintained by previous actual MAX refresh steps. -/
theorem scanLevel_current_bucket_complete {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (s : State (Fin n)) (i : Nat)
    (hi : MinInvariant M i s) (hx : MaxCompleteBelowTenacity M (2 * i + 1) s)
    (hm : MaxLabelsHaveMin s) (hbefore : ScannedBefore M i s) (hp : UnmatchedPending M i s)
    (u v : Fin n) (hb : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (2 * i + 1)) :
    EdgeInBucket (scanLevel M i s) (2 * i + 1) u v := by
  have hf := frontierAvailable_of_prior_levels s i hi.2.1 hx
  by_cases hn : M.mate u = some v
  · exact scanLevel_matched_bridge_queued M s i u v hi hf hbefore hb hn ht
  · have havail := unmatched_bridge_tenacity_available s i u v hi.2.1 hx hb hn ht
    have hknown := scanCandidates_preserves_edgeTenacity (allCandidates n) s i u v (2 * i + 1) hi havail
    have hpending := scanLevel_unmatchedPending M s i hi hf hm hbefore hp u v (2 * i + 1) hb hn hknown
    rcases hpending with hq | houter | houter
    · exact hq
    · obtain ⟨hu, k, hk, hki⟩ := houter
      have hle := unmatched_bridge_outer_minlevel_bound u v i k hb hn hu ht hk
      omega
    · obtain ⟨hv, k, hk, hki⟩ := houter
      have hnm : M.mate v ≠ some u := fun h => hn (M.symm h)
      have hle := unmatched_bridge_outer_minlevel_bound v u i k (bridge_symm hb) hnm hv
        ((semantic_edgeTenacity_comm v u).trans ht) hk
      omega

end Search
end MaximumMatching

end BridgeComplete

section SearchStage

/-! Initialized MIN/MAX stage invariants for the concrete local operations.
The complete vertex list at the current tenacity remains a support-discovery
obligation. Given that list, its labels and all bridge-refresh events are
executed and verified here; no current-stage label correctness is assumed. -/
namespace MaximumMatching.Search
variable {V : Type} {G : Graph V} {M : Matching G}
variable [DecidableEq V]

structure StageState (M : Matching G) (level cutoff : Nat) (s : State V) : Prop where
  min : MinInvariant M level s
  minBound : MinLabelsBound level s
  scanned : ScannedBefore M level s
  classification : ClassificationSound M s
  maxHasMin : MaxLabelsHaveMin s
  pending : UnmatchedPending M level s
  maxComplete : MaxCompleteBelowTenacity M cutoff s

/-- Before search level i, all smaller eligible tenacities have been handled. -/
def StageInvariant (M : Matching G) (i : Nat) (s : State V) : Prop :=
  StageState M i (2 * i + 1) s

theorem initial_stageInvariant (M : Matching G) : StageInvariant M 0 (initial M) := by
  refine ⟨initial_minInvariant M, initial_minLabelsBound M, initial_scannedBefore M,
    initial_classificationSound M, initial_maxLabelsHaveMin M, initial_unmatchedPending M, ?_⟩
  intro v t ht hlt
  have hp := tenacity_odd M v t ht
  omega

theorem scanCandidates_maxLabel [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (i : Nat) (v : V) :
    (scanCandidates M i xs s).maxLabel v = s.maxLabel v := by
  induction xs generalizing s with
  | nil => rfl
  | cons e es ih => exact (ih _).trans (scanCandidate_preserves_maxLabel s i e.1 e.2 v)

theorem scanCandidates_maxLabelsHaveMin [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (i : Nat) (hi : MinInvariant M i s) (hm : MaxLabelsHaveMin s) :
    MaxLabelsHaveMin (scanCandidates M i xs s) := by
  induction xs generalizing s with
  | nil => exact hm
  | cons e es ih =>
    exact ih _ (scanCandidate_minInvariant s i e.1 e.2 hi)
      (scanCandidate_maxLabelsHaveMin s i e.1 e.2 hi hm)

/-- Actual exhaustive MIN advances all minlevel, predecessor, classification,
scan-provenance, and pending-bridge invariants to the next boundary. -/
theorem scanLevel_stageState {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (s : State (Fin n)) (h : StageInvariant M i s) :
    StageState M (i + 1) (2 * i + 1) (scanLevel M i s) := by
  have hf := frontierAvailable_of_prior_levels s i h.min.2.1 h.maxComplete
  refine ⟨(scanLevel_complete M i s h.min hf).1,
    scanCandidates_minLabelsBound (allCandidates n) s i (fun v k hk => Nat.le_trans (h.minBound v k hk) (by omega)),
    scanLevel_scannedBefore M s i h.min h.scanned,
    scanCandidates_classificationSound (allCandidates n) s i h.min h.classification,
    scanCandidates_maxLabelsHaveMin (allCandidates n) s i h.min h.maxHasMin,
    scanLevel_unmatchedPending M s i h.min hf h.maxHasMin h.scanned h.pending, ?_⟩
  intro v t ht hlt
  exact (scanCandidates_maxLabel (allCandidates n) s i v).trans (h.maxComplete v t ht hlt)

/-- Task 2 at the explicit stage boundary, including all matched, outer,
inner, and mixed bridge cases. -/
theorem scanLevel_stage_bucket_complete {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (s : State (Fin n)) (h : StageInvariant M i s)
    (u v : Fin n) (hb : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (2 * i + 1)) :
    EdgeInBucket (scanLevel M i s) (2 * i + 1) u v :=
  scanLevel_current_bucket_complete M s i h.min h.maxComplete h.maxHasMin h.scanned h.pending u v hb ht

theorem assignMax_maxLabelsHaveMin (s : State V) (t : Nat) (u : V) (h : MaxLabelsHaveMin s) :
    MaxLabelsHaveMin (assignMax s t u) := by
  unfold assignMax
  split
  · exact h
  next lo hlo =>
    intro v k hv
    change (if v = u then some (t - lo) else s.maxLabel v) = some k at hv
    split at hv
    next he => exact ⟨lo, by simpa only [he] using hlo⟩
    next _ => exact h v k hv

theorem maxProcessVertex_labels {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (u v : Fin n) (s : State (Fin n)) :
    (maxProcessVertex M i u s).minLabel v = s.minLabel v ∧
      (maxProcessVertex M i u s).maxLabel v = (assignMax s (2 * i + 1) u).maxLabel v := by
  have hmin := assignMax_minLabel s (2 * i + 1) u v
  unfold maxProcessVertex
  dsimp only
  split
  · exact ⟨hmin, rfl⟩
  · split
    · have hh := refreshKnownEdges_labels (M := M)
        ((allCandidates n).filter fun e => decide (e.1 = u ∨ e.2 = u)) (assignMax s (2 * i + 1) u) v
      exact ⟨hh.1.trans hmin, hh.2⟩
    · exact ⟨hmin, rfl⟩

theorem refreshKnownEdges_scanned [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) : (refreshKnownEdges M xs s).scanned = s.scanned := by
  induction xs generalizing s with
  | nil => rfl
  | cons e es ih =>
    apply Eq.trans (ih _)
    unfold refreshKnownEdge
    dsimp only
    split
    · split <;> rfl
    · rfl

theorem maxProcessVertex_scanned {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (u : Fin n) (s : State (Fin n)) :
    (maxProcessVertex M i u s).scanned = s.scanned := by
  have ha : (assignMax s (2 * i + 1) u).scanned = s.scanned := by
    unfold assignMax; split <;> rfl
  unfold maxProcessVertex
  dsimp only
  split
  · exact ha
  · split
    · exact (refreshKnownEdges_scanned _ _).trans ha
    · exact ha

theorem maxProcessVertex_preserves_known_maxLabel {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (u v : Fin n) (s : State (Fin n)) (k : Nat)
    (hs : LabelsSound M s) (ht : tenacity M u = some (2 * i + 1)) (hv : s.maxLabel v = some k) :
    (maxProcessVertex M i u s).maxLabel v = some k :=
  (maxProcessVertex_labels M i u v s).2.trans
    (assignMax_preserves_known_maxLabel s (2 * i + 1) u v k hs ht hv)

omit [DecidableEq V] in
/-- A genuine finite-tenacity vertex has a finite maximum level. -/
theorem finite_maxlevel (v : V) (t : Nat) (ht : tenacity M v = some t) :
    ∃ k, maxlevel M v = some k := by
  obtain ⟨e, o, he, ho, _, _, _⟩ := finite_levels_of_tenacity v t ht
  exact ⟨max e o, by simp [maxlevel, he, ho, levelMax]⟩

/-- One actual MAX vertex step preserves every stage boundary invariant and
all earlier maxlevel assignments, while completing the current vertex. -/
theorem maxProcessVertex_stageState {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i cutoff : Nat) (u : Fin n) (s : State (Fin n))
    (h : StageState M (i + 1) cutoff s) (ht : tenacity M u = some (2 * i + 1)) :
    StageState M (i + 1) cutoff (maxProcessVertex M i u s) := by
  obtain ⟨hmin, hbound, hclass, _⟩ := maxProcessVertex_correct M i u s h.min h.minBound h.classification ht
  refine ⟨hmin, hbound, ?_, hclass, ?_,
    maxProcessVertex_unmatchedPending M s i (i + 1) u h.min ht h.pending, ?_⟩
  · intro a b hmem
    rw [maxProcessVertex_scanned] at hmem
    exact h.scanned a b hmem
  · intro v k hv
    have hlabels := maxProcessVertex_labels M i u v s
    have ha : (assignMax s (2 * i + 1) u).maxLabel v = some k := hlabels.2.symm.trans hv
    obtain ⟨lo, hlo⟩ := assignMax_maxLabelsHaveMin s (2 * i + 1) u h.maxHasMin v k ha
    exact ⟨lo, hlabels.1.trans ((assignMax_minLabel s (2 * i + 1) u v).symm.trans hlo)⟩
  · intro v t hvt hlt
    obtain ⟨k, hk⟩ := finite_maxlevel v t hvt
    exact (maxProcessVertex_preserves_known_maxLabel M i u v s k h.min.1 ht
      ((h.maxComplete v t hvt hlt).trans hk)).trans hk.symm

/-- Execute the concrete MAX label/incident-refresh step on a finite list. -/
def maxProcessVertices {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (vs : List (Fin n)) (s : State (Fin n)) : State (Fin n) :=
  vs.foldl (fun state v => maxProcessVertex M i v state) s

theorem maxProcessVertices_stageState {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i cutoff : Nat) (vs : List (Fin n)) (s : State (Fin n))
    (h : StageState M (i + 1) cutoff s) (ht : ∀ v ∈ vs, tenacity M v = some (2 * i + 1)) :
    StageState M (i + 1) cutoff (maxProcessVertices M i vs s) := by
  induction vs generalizing s with
  | nil => exact h
  | cons v vs ih =>
    exact ih _ (maxProcessVertex_stageState M i cutoff v s h (ht v (by simp)))
      (fun w hw => ht w (List.mem_cons_of_mem _ hw))

theorem maxProcessVertices_preserves_known_maxLabel {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i cutoff : Nat) (vs : List (Fin n)) (s : State (Fin n))
    (h : StageState M (i + 1) cutoff s) (ht : ∀ v ∈ vs, tenacity M v = some (2 * i + 1))
    (v : Fin n) (k : Nat) (hv : s.maxLabel v = some k) :
    (maxProcessVertices M i vs s).maxLabel v = some k := by
  induction vs generalizing s with
  | nil => exact hv
  | cons u us ih =>
    exact ih _ (maxProcessVertex_stageState M i cutoff u s h (ht u (by simp)))
      (fun w hw => ht w (List.mem_cons_of_mem _ hw))
      (maxProcessVertex_preserves_known_maxLabel M i u v s k h.min.1 (ht u (by simp)) hv)

/-- Every listed vertex receives its correct maxlevel, including after later
assignments and queue refreshes; duplicate support-list entries are allowed. -/
theorem maxProcessVertices_member_correct {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i cutoff : Nat) (vs : List (Fin n)) (s : State (Fin n))
    (h : StageState M (i + 1) cutoff s) (ht : ∀ v ∈ vs, tenacity M v = some (2 * i + 1))
    (v : Fin n) (hv : v ∈ vs) :
    (maxProcessVertices M i vs s).maxLabel v = maxlevel M v := by
  induction vs generalizing s with
  | nil => simp at hv
  | cons u us ih =>
    have hut := ht u (by simp)
    have hs := maxProcessVertex_stageState M i cutoff u s h hut
    rcases List.mem_cons.mp hv with he | he
    · subst u
      obtain ⟨k, hk⟩ := finite_maxlevel v (2 * i + 1) hut
      have hset := (maxProcessVertex_correct M i v s h.min h.minBound h.classification hut).2.2.2
      exact (maxProcessVertices_preserves_known_maxLabel M i cutoff us _ hs
        (fun w hw => ht w (List.mem_cons_of_mem _ hw)) v k (hset.trans hk)).trans hk.symm
    · exact ih _ hs (fun w hw => ht w (List.mem_cons_of_mem _ hw)) he

/-- A complete current-tenacity vertex list advances the stage induction.
The list is an explicit input: concrete DDFS support discovery must construct
it. This theorem executes MIN, assignments, and all incident refreshes itself. -/
theorem searchLevel_stageInvariant {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (vs : List (Fin n)) (s : State (Fin n))
    (h : StageInvariant M i s)
    (hsound : ∀ v ∈ vs, tenacity M v = some (2 * i + 1))
    (hcover : ∀ v, tenacity M v = some (2 * i + 1) → v ∈ vs) :
    StageInvariant M (i + 1) (maxProcessVertices M i vs (scanLevel M i s)) := by
  have hmin := scanLevel_stageState M i s h
  have hout := maxProcessVertices_stageState M i (2 * i + 1) vs _ hmin hsound
  refine ⟨hout.min, hout.minBound, hout.scanned, hout.classification, hout.maxHasMin, hout.pending, ?_⟩
  intro v t ht hlt
  by_cases hprev : t < 2 * i + 1
  · exact hout.maxComplete v t ht hprev
  · have hodd := tenacity_odd M v t ht
    have heq : t = 2 * i + 1 := by omega
    subst t
    exact maxProcessVertices_member_correct M i (2 * i + 1) vs _ hmin hsound v (hcover v ht)

end MaximumMatching.Search

end SearchStage
