import MaximumMatching.BridgeBuckets

section BridgeSchedule

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

end BridgeSchedule

section MaxBridgeRefresh

/-! MAX registers and queues finite-known incident nonprops, including edges
not previously scanned by MIN. The nonprop test uses actual predecessor lists;
its correctness follows from completed MIN levels and assigned-label bounds. -/
namespace MaximumMatching.Search
variable {V : Type} {G : Graph V} {M : Matching G}
variable [DecidableEq V]

def MinLabelsBound (k : Nat) (s : State V) : Prop :=
  ∀ v lo, s.minLabel v = some lo → lo ≤ k

def knownProp (s : State V) (u v : V) : Bool :=
  decide (u ∈ s.predecessors v ∨ v ∈ s.predecessors u)

omit [DecidableEq V] in
theorem parityLabel_has_minLabel (s : State V) (v : V) (parity k : Nat)
    (h : parityLabel s v parity = some k) : ∃ lo, s.minLabel v = some lo := by
  cases hm : s.minLabel v with
  | none => simp [parityLabel, hm] at h
  | some lo => exact ⟨lo, rfl⟩

theorem edgeTenacity_has_minLabels (s : State V) (u v : V) (t : Nat)
    (ht : edgeTenacity M s u v = some t) :
    (∃ lo, s.minLabel u = some lo) ∧ (∃ lo, s.minLabel v = some lo) := by
  let parity := if M.mate u = some v then 1 else 0
  have hh : (do let x ← parityLabel s u parity; let y ← parityLabel s v parity; some (x + y + 1)) = some t := ht
  cases hu : parityLabel s u parity with
  | none => simp [hu] at hh
  | some a =>
    cases hv : parityLabel s v parity with
    | none => simp [hu, hv] at hh
    | some b => exact ⟨parityLabel_has_minLabel s u parity a hu, parityLabel_has_minLabel s v parity b hv⟩

theorem knownProp_sound (s : State V) (hs : PredecessorsSound M s) (u v : V)
    (h : knownProp s u v = true) : PropEdge M u v := by
  have hh : u ∈ s.predecessors v ∨ v ∈ s.predecessors u := by
    simpa only [knownProp, decide_eq_true_eq] using h
  exact hh.elim (fun h => Or.inl (hs u v h)) (fun h => Or.inr (hs v u h))

/-- Finite operational edge tenacity supplies assigned minlabels at both
endpoints. Their bound makes both possible prop orientations already recorded. -/
theorem knownProp_complete_of_finite_edge (s : State V) (k : Nat) (u v : V) (t : Nat)
    (hi : MinInvariant M k s) (hb : MinLabelsBound k s)
    (ht : edgeTenacity M s u v = some t) (hp : PropEdge M u v) : knownProp s u v = true := by
  obtain ⟨⟨a, ha⟩, ⟨b, hv⟩⟩ := edgeTenacity_has_minLabels s u v t ht
  apply decide_eq_true
  rcases hp with hp | hp
  · have hmin := hi.1.1 v b hv
    have hseen := hi.2.2.1 u v b hp hmin (hb v b hv)
    exact Or.inl (hi.2.2.2.1 u v hseen hp).1
  · have hmin := hi.1.1 u a ha
    have hseen := hi.2.2.1 v u a hp hmin (hb u a ha)
    exact Or.inr (hi.2.2.2.1 v u hseen hp).1

/-- The executable MAX check registers a finite-known incident nonprop even
when MIN has not yet scanned it. No semantic Bridge predicate is used as a
runtime guard. -/
def refreshKnownEdge [DecidableRel G.Adj] (M : Matching G) (u v : V) (s : State V) : State V :=
  if G.Adj u v ∧ knownProp s u v = false then
    match edgeTenacity M s u v with
    | none => s
    | some t => enqueue { s with bridges := (u, v) :: s.bridges } u v (some t)
  else s

theorem refreshKnownEdge_minInvariant [DecidableRel G.Adj]
    (s : State V) (k : Nat) (u v : V) (hi : MinInvariant M k s) :
    MinInvariant M k (refreshKnownEdge M u v s) := by
  unfold refreshKnownEdge
  split
  · split <;> exact hi
  · exact hi

theorem refreshKnownEdge_minLabelsBound [DecidableRel G.Adj]
    (s : State V) (k : Nat) (u v : V) (hb : MinLabelsBound k s) :
    MinLabelsBound k (refreshKnownEdge M u v s) := by
  unfold refreshKnownEdge
  split
  · split <;> exact hb
  · exact hb

theorem refreshKnownEdge_edgeTenacity [DecidableRel G.Adj]
    (s : State V) (a b u v : V) :
    edgeTenacity M (refreshKnownEdge M a b s) u v = edgeTenacity M s u v := by
  unfold refreshKnownEdge
  split
  · split <;> rfl
  · rfl

/-- Registration and enqueueing are sound under the completed MIN invariant;
in particular, absence from a predecessor list is not treated as a semantic
nonprop fact without a completeness argument. -/
theorem refreshKnownEdge_classificationSound [DecidableRel G.Adj]
    (s : State V) (k : Nat) (u v : V)
    (hi : MinInvariant M k s) (hb : MinLabelsBound k s) (hc : ClassificationSound M s) :
    ClassificationSound M (refreshKnownEdge M u v s) := by
  unfold refreshKnownEdge
  split
  next hg =>
    split
    · exact hc
    next t ht =>
      have hbridge : Bridge M u v := ⟨hg.1, by
        intro hp
        have hknown := knownProp_complete_of_finite_edge s k u v t hi hb ht hp
        rw [hg.2] at hknown
        contradiction⟩
      refine ⟨hc.1, ?_, enqueue_bucketsSound { s with bridges := (u, v) :: s.bridges }
        hc.2.2 u v hbridge (some t) (fun j hj => ?_)⟩
      · intro a b hmem
        rcases List.mem_cons.mp hmem with he | hold
        · have he' := Prod.mk.inj he
          simpa only [he'.1, he'.2] using hbridge
        · exact hc.2.1 a b hold
      · have he : t = j := Option.some.inj hj
        simpa only [he] using edgeTenacity_sound s hi.1 u v t ht
  next _ => exact hc

theorem refreshKnownEdge_bucket_mono [DecidableRel G.Adj]
    (s : State V) (a b u v : V) (t : Nat) (h : (u, v) ∈ s.bucket t) :
    (u, v) ∈ (refreshKnownEdge M a b s).bucket t := by
  unfold refreshKnownEdge
  split
  · split
    · exact h
    · exact enqueue_bucket_mono _ a b u v _ t h
  · exact h

/-- Any actual finite-known bridge is now queued, without a prior registry
membership or a prior MIN scan assumption. -/
theorem refreshKnownEdge_complete [DecidableRel G.Adj]
    (s : State V) (u v : V) (t : Nat) (hp : PredecessorsSound M s)
    (hb : Bridge M u v) (ht : edgeTenacity M s u v = some t) :
    (u, v) ∈ (refreshKnownEdge M u v s).bucket t := by
  have hk : knownProp s u v = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact hb.2 (knownProp_sound s hp u v h)
  simp [refreshKnownEdge, hb.1, hk, ht, enqueue]

def refreshKnownEdges [DecidableRel G.Adj] (M : Matching G)
    (edges : List (V × V)) (s : State V) : State V :=
  edges.foldl (fun state e => refreshKnownEdge M e.1 e.2 state) s

theorem refreshKnownEdges_minInvariant [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (k : Nat) (hi : MinInvariant M k s) :
    MinInvariant M k (refreshKnownEdges M xs s) := by
  induction xs generalizing s with
  | nil => exact hi
  | cons e es ih => exact ih _ (refreshKnownEdge_minInvariant s k e.1 e.2 hi)

theorem refreshKnownEdges_sound [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (k : Nat)
    (hi : MinInvariant M k s) (hb : MinLabelsBound k s) (hc : ClassificationSound M s) :
    ClassificationSound M (refreshKnownEdges M xs s) := by
  induction xs generalizing s with
  | nil => exact hc
  | cons e es ih =>
    exact ih _ (refreshKnownEdge_minInvariant s k e.1 e.2 hi)
      (refreshKnownEdge_minLabelsBound s k e.1 e.2 hb)
      (refreshKnownEdge_classificationSound s k e.1 e.2 hi hb hc)

theorem refreshKnownEdges_bucket_mono [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (u v : V) (t : Nat) (h : (u, v) ∈ s.bucket t) :
    (u, v) ∈ (refreshKnownEdges M xs s).bucket t := by
  induction xs generalizing s with
  | nil => exact h
  | cons e es ih => exact ih _ (refreshKnownEdge_bucket_mono s e.1 e.2 u v t h)

theorem refreshKnownEdges_complete [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (k : Nat) (u v : V) (t : Nat)
    (hi : MinInvariant M k s) (hb : Bridge M u v) (hmem : (u, v) ∈ xs)
    (ht : edgeTenacity M s u v = some t) :
    (u, v) ∈ (refreshKnownEdges M xs s).bucket t := by
  induction xs generalizing s with
  | nil => simp at hmem
  | cons e es ih =>
    rcases List.mem_cons.mp hmem with he | he
    · subst e
      exact refreshKnownEdges_bucket_mono es (refreshKnownEdge M u v s) u v t
        (refreshKnownEdge_complete s u v t hi.2.2.2.2 hb ht)
    · exact ih _ (refreshKnownEdge_minInvariant s k e.1 e.2 hi) he
        ((refreshKnownEdge_edgeTenacity s e.1 e.2 u v).trans ht)

/-- Enumerate incident vertex pairs and refresh their known bridge labels
for the MAX step. -/
def refreshIncidentAll {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (w : Fin n) (s : State (Fin n)) : State (Fin n) :=
  refreshKnownEdges M ((allCandidates n).filter fun e => decide (e.1 = w ∨ e.2 = w)) s

theorem refreshIncidentAll_sound {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (w : Fin n) (s : State (Fin n)) (k : Nat)
    (hi : MinInvariant M k s) (hb : MinLabelsBound k s) (hc : ClassificationSound M s) :
    ClassificationSound M (refreshIncidentAll M w s) :=
  refreshKnownEdges_sound _ s k hi hb hc

theorem refreshIncidentAll_complete {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (w u v : Fin n) (s : State (Fin n)) (k t : Nat)
    (hi : MinInvariant M k s) (hb : Bridge M u v) (hincident : u = w ∨ v = w)
    (ht : edgeTenacity M s u v = some t) :
    (u, v) ∈ (refreshIncidentAll M w s).bucket t := by
  apply refreshKnownEdges_complete _ s k u v t hi hb
  · exact List.mem_filter.mpr ⟨mem_allCandidates u v, by simpa only [decide_eq_true_eq] using hincident⟩
  · exact ht

omit [DecidableEq V] in
theorem initial_minLabelsBound (M : Matching G) : MinLabelsBound 0 (initial M) := by
  intro v lo h
  change (if M.mate v = none then some 0 else none) = some lo at h
  split at h
  · have he := Option.some.inj h
    omega
  · contradiction

theorem scan_minLabelsBound (s : State V) (i : Nat) (u v : V)
    (h : MinLabelsBound (i + 1) s) : MinLabelsBound (i + 1) (scan M i u v s) := by
  unfold scan
  split
  · exact h
  · split
    · intro w lo hw
      change (if w = v then some (i + 1) else s.minLabel w) = some lo at hw
      split at hw
      · have he := Option.some.inj hw; omega
      · exact h w lo hw
    · unfold enqueue; split <;> exact h

theorem scanCandidate_minLabelsBound [DecidableRel G.Adj] (s : State V) (i : Nat) (u v : V)
    (h : MinLabelsBound (i + 1) s) : MinLabelsBound (i + 1) (scanCandidate M i u v s) := by
  unfold scanCandidate
  split
  · exact scan_minLabelsBound s i u v h
  · exact h

theorem scanCandidates_minLabelsBound [DecidableRel G.Adj] (xs : List (V × V)) (s : State V)
    (i : Nat) (h : MinLabelsBound (i + 1) s) :
    MinLabelsBound (i + 1) (scanCandidates M i xs s) := by
  induction xs generalizing s with
  | nil => exact h
  | cons e es ih => exact ih _ (scanCandidate_minLabelsBound s i e.1 e.2 h)

theorem assignMax_minLabelsBound (s : State V) (k t : Nat) (v : V) (h : MinLabelsBound k s) :
    MinLabelsBound k (assignMax s t v) := by
  unfold assignMax
  split <;> exact h

theorem assignMax_classificationSound (s : State V) (t : Nat) (v : V) (h : ClassificationSound M s) :
    ClassificationSound M (assignMax s t v) := by
  unfold assignMax
  split <;> exact h

theorem refreshKnownEdge_labels [DecidableRel G.Adj] (s : State V) (u v w : V) :
    (refreshKnownEdge M u v s).minLabel w = s.minLabel w ∧
      (refreshKnownEdge M u v s).maxLabel w = s.maxLabel w := by
  unfold refreshKnownEdge
  split
  · split <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem refreshKnownEdges_labels [DecidableRel G.Adj] (xs : List (V × V)) (s : State V) (w : V) :
    (refreshKnownEdges M xs s).minLabel w = s.minLabel w ∧
      (refreshKnownEdges M xs s).maxLabel w = s.maxLabel w := by
  induction xs generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons e es ih =>
    have hh := ih (refreshKnownEdge M e.1 e.2 s)
    have he := refreshKnownEdge_labels (M := M) s e.1 e.2 w
    exact ⟨hh.1.trans he.1, hh.2.trans he.2⟩

/-- The source MAX vertex step: assign maxlevel, then reconsider all incident
finite-known nonprops exactly when the assigned minlevel has odd parity. -/
def maxProcessVertex {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (v : Fin n) (s : State (Fin n)) : State (Fin n) :=
  let assigned := assignMax s (2 * i + 1) v
  match assigned.minLabel v with
  | none => assigned
  | some lo => if lo % 2 = 1 then refreshIncidentAll M v assigned else assigned

theorem maxProcessVertex_correct {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (v : Fin n) (s : State (Fin n))
    (hi : MinInvariant M (i + 1) s) (hb : MinLabelsBound (i + 1) s)
    (hc : ClassificationSound M s) (ht : tenacity M v = some (2 * i + 1)) :
    MinInvariant M (i + 1) (maxProcessVertex M i v s) ∧
      MinLabelsBound (i + 1) (maxProcessVertex M i v s) ∧
      ClassificationSound M (maxProcessVertex M i v s) ∧
      (maxProcessVertex M i v s).maxLabel v = maxlevel M v := by
  let assigned := assignMax s (2 * i + 1) v
  have hia : MinInvariant M (i + 1) assigned := assignMax_minInvariant s (i + 1) (2 * i + 1) v hi ht
  have hba : MinLabelsBound (i + 1) assigned := assignMax_minLabelsBound s (i + 1) (2 * i + 1) v hb
  have hca : ClassificationSound M assigned := assignMax_classificationSound s (2 * i + 1) v hc
  have hset : assigned.maxLabel v = maxlevel M v :=
    assignMax_correct s i v (fun w k hw hk => hi.2.1 w k hw (by omega)) ht
  let P : State (Fin n) → Prop := fun state =>
    MinInvariant M (i + 1) state ∧ MinLabelsBound (i + 1) state ∧
      ClassificationSound M state ∧ state.maxLabel v = maxlevel M v
  change P (match assigned.minLabel v with
    | none => assigned
    | some lo => if lo % 2 = 1 then refreshIncidentAll M v assigned else assigned)
  cases hlo : assigned.minLabel v with
  | none => exact ⟨hia, hba, hca, hset⟩
  | some lo =>
    by_cases hp : lo % 2 = 1
    · simp only [hp, ite_true]
      have hlabels := refreshKnownEdges_labels (M := M)
        ((allCandidates n).filter fun e => decide (e.1 = v ∨ e.2 = v)) assigned
      refine ⟨refreshKnownEdges_minInvariant _ assigned (i + 1) hia, ?_,
        refreshIncidentAll_sound M v assigned (i + 1) hia hba hca, (hlabels v).2.trans hset⟩
      intro w k hw
      apply hba w k
      exact (hlabels w).1.symm.trans hw
    · simp only [hp, ite_false]
      exact ⟨hia, hba, hca, hset⟩

/-- A real inner support vertex activates the incident refresh, so any bridge
whose tenacity becomes known at this assignment is enqueued immediately. -/
theorem maxProcessVertex_queues_incident {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (w u v : Fin n) (s : State (Fin n)) (t : Nat)
    (hi : MinInvariant M (i + 1) s) (hw : Inner M w)
    (hwt : tenacity M w = some (2 * i + 1)) (hbridge : Bridge M u v)
    (hincident : u = w ∨ v = w)
    (ht : edgeTenacity M (assignMax s (2 * i + 1) w) u v = some t) :
    (u, v) ∈ (maxProcessVertex M i w s).bucket t := by
  obtain ⟨e, o, he, ho, _, hop, _⟩ := finite_levels_of_tenacity w (2 * i + 1) hwt
  obtain ⟨j, hj, _, hmin⟩ := inner_oddlevel_lt_evenlevel w e he hw
  have hjo : j = o := Option.some.inj (hj.symm.trans ho)
  have hjbound : j ≤ i := by
    obtain ⟨k, hk, hki⟩ := minlevel_le_half_tenacity w i hwt
    have hkj := Option.some.inj (hk.symm.trans hmin)
    omega
  have hlabel : s.minLabel w = some j := hi.2.1 w j hmin (by omega)
  have hpar : j % 2 = 1 := by omega
  have hassigned : (assignMax s (2 * i + 1) w).minLabel w = some j := by
    simp [assignMax, hlabel]
  simp only [maxProcessVertex, hassigned, hpar, ite_true]
  exact refreshIncidentAll_complete M w u v _ (i + 1) t
    (assignMax_minInvariant s (i + 1) (2 * i + 1) w hi hwt) hbridge hincident ht

end MaximumMatching.Search

end MaxBridgeRefresh
