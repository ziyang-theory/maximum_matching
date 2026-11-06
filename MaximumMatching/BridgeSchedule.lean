import MaximumMatching.MaxCorrectness

/-! Concrete scheduling of known bridge tenacities during MIN. The invariants
record actual previous scans and enqueue events. Deferred unknown bridge
labels are handled by the separately verified MAX incident refresh. -/
namespace MaximumMatching.Search
variable {V : Type} {G : Graph V} {M : Matching G}
variable [DecidableEq V]

def EdgeInBucket (s : State V) (t : Nat) (u v : V) : Prop :=
  (u, v) ∈ s.bucket t ∨ (v, u) ∈ s.bucket t

def KnownBridgeQueued (s : State V) (t : Nat) (u v : V) : Prop :=
  seen s u v = true → EdgeInBucket s t u v

/-- Recorded scans came from actual appropriate parity levels below i. -/
def ScannedBefore (M : Matching G) (i : Nat) (s : State V) : Prop :=
  ∀ u v, (u, v) ∈ s.scanned → ∃ j, j < i ∧ level M (j % 2) u = some j ∧
    ((M.mate u = some v) ↔ j % 2 = 1)

theorem edgeTenacity_comm (s : State V) (u v : V) :
    edgeTenacity M s u v = edgeTenacity M s v u := by
  by_cases hm : M.mate u = some v
  · have hm' := M.symm hm
    simp only [edgeTenacity, hm, hm', ite_true]
    cases hu : parityLabel s u 1 <;> cases hv : parityLabel s v 1 <;>
      simp_all [Nat.add_comm]
  · have hm' : M.mate v ≠ some u := fun h => hm (M.symm h)
    simp only [edgeTenacity, hm, hm', ite_false]
    cases hu : parityLabel s u 0 <;> cases hv : parityLabel s v 0 <;>
      simp_all [Nat.add_comm]

theorem scan_bucket_mono (s : State V) (i : Nat) (a b u v : V) (t : Nat)
    (h : (u, v) ∈ s.bucket t) : (u, v) ∈ (scan M i a b s).bucket t := by
  unfold scan
  split
  · exact h
  · split
    · exact h
    · exact enqueue_bucket_mono _ a b u v _ t h

theorem scanCandidate_bucket_mono [DecidableRel G.Adj]
    (s : State V) (i : Nat) (a b u v : V) (t : Nat) (h : (u, v) ∈ s.bucket t) :
    (u, v) ∈ (scanCandidate M i a b s).bucket t := by
  unfold scanCandidate
  split
  · exact scan_bucket_mono s i a b u v t h
  · exact h

omit [DecidableEq V] in
/-- A true bridge can never pass MIN's predecessor-admission branch when
all earlier minimum levels are already assigned. -/
theorem bridge_scan_rejects (s : State V) (i : Nat) (u v : V)
    (hc : MinCompleteBelow M i s) (hb : Bridge M u v)
    (hu : level M (i % 2) u = some i) (hpar : (M.mate u = some v) ↔ i % 2 = 1) :
    admits (s.minLabel v) (i + 1) = false := by
  apply Bool.eq_false_iff.mpr
  intro ha
  have hp := (minlevel_of_scan_guard u v i hu hb.1 hpar
    (admits_semantic_lower_bound s i hc v ha)).2
  exact hb.2 (Or.inl hp)

theorem scan_queues_known (s : State V) (i : Nat) (u v : V) (t : Nat)
    (hseen : seen s u v = false) (ha : admits (s.minLabel v) (i + 1) = false)
    (ht : edgeTenacity M s u v = some t) : (u, v) ∈ (scan M i u v s).bucket t := by
  simp [scan, hseen, ha, ht, enqueue]

/-- Once a finite bridge tenacity is known, a new scan in either orientation
queues it; an existing queue entry survives every other candidate scan. -/
theorem scanCandidate_knownBridgeQueued [DecidableRel G.Adj]
    (s : State V) (i : Nat) (a b u v : V) (t : Nat)
    (hi : MinInvariant M i s) (hb : Bridge M u v) (ht : edgeTenacity M s u v = some t)
    (hq : KnownBridgeQueued s t u v) : KnownBridgeQueued (scanCandidate M i a b s) t u v := by
  intro hseen
  by_cases hold : seen s u v = true
  · rcases hq hold with hmem | hmem
    · exact Or.inl (scanCandidate_bucket_mono s i a b u v t hmem)
    · exact Or.inr (scanCandidate_bucket_mono s i a b v u t hmem)
  · by_cases hg : G.Adj a b ∧ parityLabel s a (i % 2) = some i ∧
        ((M.mate a = some b) ↔ i % 2 = 1)
    · have hstate : scanCandidate M i a b s = scan M i a b s := by simp [scanCandidate, hg]
      rw [hstate] at hseen ⊢
      rcases scan_seen_cases s i a b u v hseen with hprev | hab | hba
      · exact False.elim (hold hprev)
      · rcases hab with ⟨ha, hb'⟩
        subst a
        subst b
        have hu := parityLabel_sound s hi.1 u (i % 2) i hg.2.1
        exact Or.inl (scan_queues_known s i u v t (Bool.eq_false_iff.mpr hold)
          (bridge_scan_rejects s i u v hi.2.1 hb hu hg.2.2) ht)
      · rcases hba with ⟨hb', ha⟩
        subst a
        subst b
        have hv := parityLabel_sound s hi.1 v (i % 2) i hg.2.1
        have hfalse : seen s v u = false := by rw [seen_comm]; exact Bool.eq_false_iff.mpr hold
        exact Or.inr (scan_queues_known s i v u t hfalse
          (bridge_scan_rejects s i v u hi.2.1 (bridge_symm hb) hv hg.2.2)
          ((edgeTenacity_comm s v u).trans ht))
    · have hstate : scanCandidate M i a b s = s := by simp [scanCandidate, hg]
      exact False.elim (hold (hstate ▸ hseen))

theorem scanCandidate_preserves_edgeTenacity [DecidableRel G.Adj]
    (s : State V) (i : Nat) (a b u v : V) (t : Nat)
    (hi : MinInvariant M i s) (ht : edgeTenacity M s u v = some t) :
    edgeTenacity M (scanCandidate M i a b s) u v = some t := by
  unfold edgeTenacity at ht ⊢
  let parity := if M.mate u = some v then 1 else 0
  change (do let x ← parityLabel s u parity; let y ← parityLabel s v parity; some (x + y + 1)) = some t at ht
  change (do let x ← parityLabel (scanCandidate M i a b s) u parity
             let y ← parityLabel (scanCandidate M i a b s) v parity; some (x + y + 1)) = some t
  cases hu : parityLabel s u parity with
  | none => simp [hu] at ht
  | some x =>
    cases hv : parityLabel s v parity with
    | none => simp [hu, hv] at ht
    | some y =>
      have hu' := scanCandidate_preserves_parityLabel s i a b u parity x hi.1 hi.2.1 hu
      have hv' := scanCandidate_preserves_parityLabel s i a b v parity y hi.1 hi.2.1 hv
      simpa only [hu, hv, hu', hv'] using ht

theorem scanCandidates_knownBridgeQueued [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (i : Nat) (u v : V) (t : Nat)
    (hi : MinInvariant M i s) (hb : Bridge M u v) (ht : edgeTenacity M s u v = some t)
    (hq : KnownBridgeQueued s t u v) : KnownBridgeQueued (scanCandidates M i xs s) t u v := by
  induction xs generalizing s with
  | nil => exact hq
  | cons e es ih =>
    exact ih _ (scanCandidate_minInvariant s i e.1 e.2 hi)
      (scanCandidate_preserves_edgeTenacity s i e.1 e.2 u v t hi ht)
      (scanCandidate_knownBridgeQueued s i e.1 e.2 u v t hi hb ht hq)

/-- Complete MIN enumeration queues a known bridge at the first available
parity level, provided an earlier scan has already queued it or no earlier
scan has occurred. The latter will be derived from scan provenance below. -/
theorem scanLevel_queues_known {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (s : State (Fin n)) (i : Nat) (u v : Fin n) (t : Nat)
    (hi : MinInvariant M i s) (hf : FrontierAvailable M i s)
    (hb : Bridge M u v) (hu : level M (i % 2) u = some i)
    (hpar : (M.mate u = some v) ↔ i % 2 = 1)
    (ht : edgeTenacity M s u v = some t) (hq : KnownBridgeQueued s t u v) :
    EdgeInBucket (scanLevel M i s) t u v := by
  exact scanCandidates_knownBridgeQueued (allCandidates n) s i u v t hi hb ht hq
    (scanCandidates_marks_member (allCandidates n) s i u v hi hf (mem_allCandidates u v) hb.1 hu hpar)

theorem scan_scanned_cases (s : State V) (i : Nat) (a b u v : V)
    (h : (u, v) ∈ (scan M i a b s).scanned) :
    (u = a ∧ v = b) ∨ (u, v) ∈ s.scanned := by
  unfold scan at h
  split at h
  · exact Or.inr h
  · split at h
    · simpa only [List.mem_cons, Prod.mk.injEq] using h
    · unfold enqueue at h
      split at h <;> simpa only [List.mem_cons, Prod.mk.injEq] using h

omit [DecidableEq V] in
theorem scannedBefore_mono (s : State V) (i j : Nat) (hij : i ≤ j)
    (h : ScannedBefore M i s) : ScannedBefore M j s := by
  intro u v huv
  obtain ⟨k, hk, hl, hp⟩ := h u v huv
  exact ⟨k, by omega, hl, hp⟩

theorem scanCandidate_scannedBefore [DecidableRel G.Adj]
    (s : State V) (i : Nat) (a b : V) (hs : LabelsSound M s)
    (h : ScannedBefore M (i + 1) s) : ScannedBefore M (i + 1) (scanCandidate M i a b s) := by
  intro u v huv
  unfold scanCandidate at huv
  split at huv
  next hg =>
    rcases scan_scanned_cases s i a b u v huv with he | hold
    · exact ⟨i, by omega, by simpa only [he.1] using parityLabel_sound s hs a (i % 2) i hg.2.1,
        by simpa only [he.1, he.2] using hg.2.2⟩
    · exact h u v hold
  next _ => exact h u v huv

theorem scanCandidates_scannedBefore [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (i : Nat) (hi : MinInvariant M i s)
    (h : ScannedBefore M (i + 1) s) : ScannedBefore M (i + 1) (scanCandidates M i xs s) := by
  induction xs generalizing s with
  | nil => exact h
  | cons e es ih =>
    exact ih _ (scanCandidate_minInvariant s i e.1 e.2 hi)
      (scanCandidate_scannedBefore s i e.1 e.2 hi.1 h)

omit [DecidableEq V] in
theorem initial_scannedBefore (M : Matching G) : ScannedBefore M 0 (initial M) := by
  intro u v h
  change (u, v) ∈ ([] : List (V × V)) at h
  contradiction

/-- If both appropriate endpoint levels are i, neither orientation could have
been scanned at a strictly earlier level. -/
theorem equal_endpoint_levels_unseen (s : State V) (i : Nat) (u v : V)
    (hbefore : ScannedBefore M i s)
    (hu : level M (i % 2) u = some i) (hv : level M (i % 2) v = some i)
    (hpar : (M.mate u = some v) ↔ i % 2 = 1) : seen s u v = false := by
  have impossible (a b : V) (ha : level M (i % 2) a = some i)
      (hp : (M.mate a = some b) ↔ i % 2 = 1) (hab : (a, b) ∈ s.scanned) : False := by
    obtain ⟨j, hji, hj, hjp⟩ := hbefore a b hab
    have hparity : j % 2 = i % 2 := by
      by_cases hm : M.mate a = some b
      · have hi' := hp.1 hm
        have hj' := hjp.1 hm
        omega
      · have hi' : i % 2 ≠ 1 := fun h => hm (hp.2 h)
        have hj' : j % 2 ≠ 1 := fun h => hm (hjp.2 h)
        omega
    rw [hparity, ha] at hj
    have he := Option.some.inj hj
    omega
  apply Bool.eq_false_iff.mpr
  intro hs
  have hm : (u, v) ∈ s.scanned ∨ (v, u) ∈ s.scanned := by simpa only [seen, decide_eq_true_eq] using hs
  rcases hm with hm | hm
  · exact impossible u v hu hpar hm
  · have hp : (M.mate v = some u) ↔ i % 2 = 1 :=
      ⟨fun h => hpar.1 (M.symm h), fun h => M.symm (hpar.2 h)⟩
    exact impossible v u hv hp hm

/-- MIN alone queues every bridge whose two appropriate endpoint levels equal
the current level. This includes all matched bridges and unmatched bridges
with two outer endpoints at the current tenacity. -/
theorem scanLevel_equal_levels_queues {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (s : State (Fin n)) (i : Nat) (u v : Fin n)
    (hi : MinInvariant M i s) (hf : FrontierAvailable M i s) (hbefore : ScannedBefore M i s)
    (hb : Bridge M u v) (hu : level M (i % 2) u = some i) (hv : level M (i % 2) v = some i)
    (hpar : (M.mate u = some v) ↔ i % 2 = 1) :
    EdgeInBucket (scanLevel M i s) (2 * i + 1) u v := by
  have hu' := hf u hu
  have hv' := hf v hv
  have ht : edgeTenacity M s u v = some (2 * i + 1) := by
    by_cases hm : M.mate u = some v
    · have hip := hpar.1 hm
      rw [hip] at hu' hv'
      simp [edgeTenacity, hm, hu', hv', Nat.two_mul]
    · have hip : i % 2 = 0 := by have hh : i % 2 ≠ 1 := fun h => hm (hpar.2 h); omega
      rw [hip] at hu' hv'
      simp [edgeTenacity, hm, hu', hv', Nat.two_mul]
  apply scanLevel_queues_known M s i u v (2 * i + 1) hi hf hb hu hpar ht
  intro hseen
  have hfalse := equal_endpoint_levels_unseen s i u v hbefore hu hv hpar
  rw [hfalse] at hseen
  contradiction

/-- Task 2 for every matched bridge at the current tenacity, derived from the
proved matched-bridge endpoint classification and actual scan provenance. -/
theorem scanLevel_matched_bridge_queued {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (s : State (Fin n)) (i : Nat) (u v : Fin n)
    (hi : MinInvariant M i s) (hf : FrontierAvailable M i s) (hbefore : ScannedBefore M i s)
    (hb : Bridge M u v) (hm : M.mate u = some v)
    (ht : MaximumMatching.edgeTenacity M u v = some (2 * i + 1)) :
    EdgeInBucket (scanLevel M i s) (2 * i + 1) u v := by
  obtain ⟨j, hju, hjv, _, _, _, _, hji⟩ := matched_bridge_levels hb hm (2 * i + 1) ht
  have he : j = i := by omega
  subst j
  have hip := level_parity M 1 u i hju
  exact scanLevel_equal_levels_queues M s i u v hi hf hbefore hb
    (by simpa only [hip] using hju) (by simpa only [hip] using hjv) (by simp [hm, hip])

/-- Task 2 for an unmatched bridge with two outer endpoints. -/
theorem scanLevel_outer_bridge_queued {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (s : State (Fin n)) (i : Nat) (u v : Fin n)
    (hi : MinInvariant M i s) (hf : FrontierAvailable M i s) (hbefore : ScannedBefore M i s)
    (hb : Bridge M u v) (hm : M.mate u ≠ some v)
    (hu : Outer M u) (hv : Outer M v)
    (ht : MaximumMatching.edgeTenacity M u v = some (2 * i + 1)) :
    EdgeInBucket (scanLevel M i s) (2 * i + 1) u v := by
  have ht' : (levelAdd (evenlevel M u) (evenlevel M v)).map (· + 1) = some (2 * i + 1) := by
    simpa only [MaximumMatching.edgeTenacity, hm, ite_false] using ht
  cases he : evenlevel M u with
  | none => simp [he, levelAdd] at ht'
  | some e =>
    cases hf' : evenlevel M v with
    | none => simp [he, hf', levelAdd] at ht'
    | some f =>
      have hsum : e + f + 1 = 2 * i + 1 := by
        simpa only [he, hf', levelAdd, Option.map_some, Option.some.injEq] using ht'
      have hef := (unmatched_bridge_outer_levels hb hm e f he hf' hu hv).1
      have hei : e = i := by omega
      have hfi : f = i := by omega
      subst e
      subst f
      have hip := level_parity M 0 u i he
      exact scanLevel_equal_levels_queues M s i u v hi hf hbefore hb
        (by simpa only [hip] using he) (by simpa only [hip] using hf') (by simp [hm, hip])

theorem scanLevel_scannedBefore {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (s : State (Fin n)) (i : Nat)
    (hi : MinInvariant M i s) (hb : ScannedBefore M i s) :
    ScannedBefore M (i + 1) (scanLevel M i s) :=
  scanCandidates_scannedBefore (allCandidates n) s i hi (scannedBefore_mono s i (i + 1) (by omega) hb)

end MaximumMatching.Search
