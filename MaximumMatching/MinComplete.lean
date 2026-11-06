import MaximumMatching.MinScan

/-! Complete finite MIN candidate enumeration. The starting-state invariants
are initialized below and preserved by each actual guarded scan. Availability
of maxlevels from earlier MAX stages is exposed separately; this module does
not substitute a semantic search oracle for those stages. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Opposite orientations cannot both be predecessors: each would strictly
increase the semantic minimum level. -/
theorem predecessor_asymm {u v : V} (huv : Predecessor M u v) : ¬Predecessor M v u := by
  rintro ⟨q, hqu, hqm, hqpos, hqv⟩
  obtain ⟨p, hpv, hpm, hppos, hpu⟩ := huv
  have hpbound := minlevel_le_path M u q.length hqm (p.take (p.length - 1) (by omega)) hpu
  have hqbound := minlevel_le_path M v p.length hpm (q.take (q.length - 1) (by omega)) hqv
  simp only [AltPath.take_length] at hpbound hqbound
  omega

theorem minlevel_succ_has_predecessor (v : V) (i : Nat)
    (hv : minlevel M v = some (i + 1)) : ∃ u, Predecessor M u v := by
  obtain ⟨p, hp, hl⟩ := minlevel_witness M v (i + 1) hv
  refine ⟨p.vertex ⟨p.length - 1, by omega⟩, p, hp, ?_, by omega, rfl⟩
  simpa only [hl] using hv

namespace Search
variable [DecidableEq V]

/-- Any previously scanned prop has its actual oriented predecessor recorded
and its destination already labeled. This is preserved even if the later scan
would revisit the edge in the other orientation. -/
def SeenPredecessorsRecorded (M : Matching G) (s : State V) : Prop :=
  ∀ u v, seen s u v = true → Predecessor M u v →
    u ∈ s.predecessors v ∧ s.minLabel v = minlevel M v

def PredecessorsSound (M : Matching G) (s : State V) : Prop :=
  ∀ u v, u ∈ s.predecessors v → Predecessor M u v

/-- The semantic level-i frontier is already available at the start of MIN.
A theorem below derives this from earlier minlevel and maxlevel assignments. -/
def FrontierAvailable (M : Matching G) (i : Nat) (s : State V) : Prop :=
  ∀ u, level M (i % 2) u = some i → parityLabel s u (i % 2) = some i

/-- State invariant at the start and during a single MIN search level. -/
def MinInvariant (M : Matching G) (i : Nat) (s : State V) : Prop :=
  LabelsSound M s ∧ MinCompleteBelow M i s ∧ EarlierPropsSeen M i s ∧
    SeenPredecessorsRecorded M s ∧ PredecessorsSound M s

theorem scan_predecessors_mono (s : State V) (i : Nat) (a b u v : V)
    (h : u ∈ s.predecessors v) : u ∈ (scan M i a b s).predecessors v := by
  unfold scan
  split
  · exact h
  · split
    · change u ∈ (if v = b then a :: s.predecessors v else s.predecessors v)
      split
      · exact List.mem_cons_of_mem _ h
      · exact h
    · unfold enqueue
      split <;> exact h

theorem scan_seen_mono (s : State V) (i : Nat) (a b u v : V)
    (h : seen s u v = true) : seen (scan M i a b s) u v = true := by
  unfold scan
  split
  · exact h
  · have hh : (u, v) ∈ s.scanned ∨ (v, u) ∈ s.scanned := by
      simpa only [seen, decide_eq_true_eq] using h
    have hm : (u, v) ∈ (a, b) :: s.scanned ∨ (v, u) ∈ (a, b) :: s.scanned :=
      hh.elim (fun h => Or.inl (List.mem_cons_of_mem _ h))
        (fun h => Or.inr (List.mem_cons_of_mem _ h))
    split
    · simpa only [seen, decide_eq_true_eq] using hm
    · unfold enqueue
      split <;> simpa only [seen, decide_eq_true_eq] using hm

theorem scanCandidate_predecessors_mono [DecidableRel G.Adj]
    (s : State V) (i : Nat) (a b u v : V) (h : u ∈ s.predecessors v) :
    u ∈ (scanCandidate M i a b s).predecessors v := by
  unfold scanCandidate
  split
  · exact scan_predecessors_mono s i a b u v h
  · exact h

theorem scanCandidate_seen_mono [DecidableRel G.Adj]
    (s : State V) (i : Nat) (a b u v : V) (h : seen s u v = true) :
    seen (scanCandidate M i a b s) u v = true := by
  unfold scanCandidate
  split
  · exact scan_seen_mono s i a b u v h
  · exact h

/-- A guarded scan never changes an already-correct minimum label. -/
theorem scanCandidate_preserves_minLabel [DecidableRel G.Adj]
    (s : State V) (i : Nat) (a b v : V) (k : Nat)
    (hs : LabelsSound M s) (hc : MinCompleteBelow M i s) (hv : s.minLabel v = some k) :
    (scanCandidate M i a b s).minLabel v = some k := by
  have hs' := scanCandidate_labelsSound s i a b hs hc
  unfold scanCandidate
  split
  next hguard =>
    unfold scan
    split
    · exact hv
    next hseen =>
      split
      next ha =>
        change (if v = b then some (i + 1) else s.minLabel v) = some k
        by_cases he : v = b
        · have hnew : minlevel M v = some (i + 1) := hs'.1 v (i + 1) (by simp [scanCandidate, hguard, scan, hseen, ha, he])
          have hki := Option.some.inj ((hs.1 v k hv).symm.trans hnew)
          simp only [he, ite_true, hki]
        · simp only [he, ite_false, hv]
      · unfold enqueue
        split <;> exact hv
  · exact hv

theorem scanCandidate_preserves_maxLabel [DecidableRel G.Adj]
    (s : State V) (i : Nat) (a b v : V) :
    (scanCandidate M i a b s).maxLabel v = s.maxLabel v := by
  unfold scanCandidate
  split
  · exact scan_preserves_max M i a b v s
  · rfl

theorem scanCandidate_preserves_parityLabel [DecidableRel G.Adj]
    (s : State V) (i : Nat) (a b v : V) (parity k : Nat)
    (hs : LabelsSound M s) (hc : MinCompleteBelow M i s)
    (hv : parityLabel s v parity = some k) :
    parityLabel (scanCandidate M i a b s) v parity = some k := by
  cases hm : s.minLabel v with
  | none => simp [parityLabel, hm] at hv
  | some j =>
    have hm' := scanCandidate_preserves_minLabel s i a b v j hs hc hm
    simpa only [parityLabel, hm, hm', scanCandidate_preserves_maxLabel] using hv

/-- Later candidate scans retain the entire available level-i frontier. -/
theorem scanCandidate_frontierAvailable [DecidableRel G.Adj]
    (s : State V) (i : Nat) (a b : V)
    (hs : LabelsSound M s) (hc : MinCompleteBelow M i s) (hf : FrontierAvailable M i s) :
    FrontierAvailable M i (scanCandidate M i a b s) := by
  intro u hu
  exact scanCandidate_preserves_parityLabel s i a b u (i % 2) i hs hc (hf u hu)

/-- A scan only adds its own undirected edge to the seen set. -/
theorem scan_seen_cases (s : State V) (i : Nat) (a b u v : V)
    (h : seen (scan M i a b s) u v = true) :
    seen s u v = true ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
  have marked : ∀ t : State V, t.scanned = (a, b) :: s.scanned → seen t u v = true →
      seen s u v = true ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
    intro t ht hh
    simp only [seen, ht, decide_eq_true_eq, List.mem_cons, Prod.mk.injEq] at hh
    rcases hh with (hab | hold) | (hba | hold)
    · exact Or.inr (Or.inl hab)
    · exact Or.inl (by simp [seen, hold])
    · exact Or.inr (Or.inr ⟨hba.2, hba.1⟩)
    · exact Or.inl (by simp [seen, hold])
  unfold scan at h
  split at h
  · exact Or.inl h
  · split at h
    · exact marked _ rfl h
    · unfold enqueue at h
      split at h <;> exact marked _ rfl h

theorem scanCandidate_recorded_persists [DecidableRel G.Adj]
    (s : State V) (i : Nat) (a b u v : V)
    (hs : LabelsSound M s) (hc : MinCompleteBelow M i s)
    (hp : Predecessor M u v)
    (hr : u ∈ s.predecessors v ∧ s.minLabel v = minlevel M v) :
    u ∈ (scanCandidate M i a b s).predecessors v ∧
      (scanCandidate M i a b s).minLabel v = minlevel M v := by
  obtain ⟨p, _, hmin, _, _⟩ := hp
  exact ⟨scanCandidate_predecessors_mono s i a b u v hr.1,
    (scanCandidate_preserves_minLabel s i a b v p.length hs hc (hr.2.trans hmin)).trans hmin.symm⟩

/-- No true predecessor is lost when a scan marks an edge. An admission records
its correct orientation; a rejection proves neither orientation is a prop. -/
theorem scanCandidate_seenPredecessorsRecorded [DecidableRel G.Adj]
    (s : State V) (i : Nat) (a b : V)
    (hs : LabelsSound M s) (hc : MinCompleteBelow M i s)
    (hearlier : EarlierPropsSeen M i s) (hr : SeenPredecessorsRecorded M s) :
    SeenPredecessorsRecorded M (scanCandidate M i a b s) := by
  intro u v hseen hp
  by_cases hg : G.Adj a b ∧ parityLabel s a (i % 2) = some i ∧
      ((M.mate a = some b) ↔ i % 2 = 1)
  · have hstate : scanCandidate M i a b s = scan M i a b s := by simp [scanCandidate, hg]
    rw [hstate] at hseen
    rcases scan_seen_cases s i a b u v hseen with hold | hpair | hpair
    · exact scanCandidate_recorded_persists s i a b u v hs hc hp (hr u v hold hp)
    · rcases hpair with ⟨hu, hv⟩
      subst u
      subst v
      by_cases hseenold : seen s a b = true
      · exact scanCandidate_recorded_persists s i a b a b hs hc hp (hr a b hseenold hp)
      · have hfalse : seen s a b = false := Bool.eq_false_iff.mpr hseenold
        have hu := parityLabel_sound s hs a (i % 2) i hg.2.1
        by_cases ha : admits (s.minLabel b) (i + 1) = true
        · obtain ⟨hmin, _, hl, hpred⟩ := scan_assigns_semantic s i a b hc hu hg.1 hg.2.2 hfalse ha
          rw [hstate]
          exact ⟨by rw [hpred]; exact List.mem_cons_self, hl.trans hmin.symm⟩
        · have hbridge := scan_rejects_bridge s i a b hs hearlier hu hg.1 hfalse
            (Bool.eq_false_iff.mpr ha)
          exact False.elim (hbridge.2 (Or.inl hp))
    · rcases hpair with ⟨hu, hv⟩
      subst u
      subst v
      by_cases hseenold : seen s a b = true
      · have hba : seen s b a = true := by rw [seen_comm]; exact hseenold
        exact scanCandidate_recorded_persists s i a b b a hs hc hp (hr b a hba hp)
      · have hfalse : seen s a b = false := Bool.eq_false_iff.mpr hseenold
        have hu := parityLabel_sound s hs a (i % 2) i hg.2.1
        by_cases ha : admits (s.minLabel b) (i + 1) = true
        · have hpred := (scan_assigns_semantic s i a b hc hu hg.1 hg.2.2 hfalse ha).2.1
          exact False.elim (predecessor_asymm hpred hp)
        · have hbridge := scan_rejects_bridge s i a b hs hearlier hu hg.1 hfalse
            (Bool.eq_false_iff.mpr ha)
          exact False.elim (hbridge.2 (Or.inr hp))
  · have hstate : scanCandidate M i a b s = s := by simp [scanCandidate, hg]
    rw [hstate] at hseen ⊢
    exact hr u v hseen hp

theorem scanCandidate_predecessorsSound [DecidableRel G.Adj]
    (s : State V) (i : Nat) (a b : V)
    (hs : LabelsSound M s) (hc : MinCompleteBelow M i s) (hp : PredecessorsSound M s) :
    PredecessorsSound M (scanCandidate M i a b s) := by
  unfold scanCandidate
  split
  next hg =>
    unfold scan
    split
    · exact hp
    next hseen =>
      split
      next ha =>
        have hpred := (scan_assigns_semantic s i a b hc
          (parityLabel_sound s hs a (i % 2) i hg.2.1) hg.1 hg.2.2
          (Bool.eq_false_iff.mpr hseen) ha).2.1
        intro u v huv
        change u ∈ (if v = b then a :: s.predecessors v else s.predecessors v) at huv
        split at huv
        next hv =>
          rcases List.mem_cons.mp huv with hu | hu
          · simpa only [hu, hv] using hpred
          · exact hp u v hu
        next _ => exact hp u v huv
      next _ => unfold enqueue; split <;> exact hp
  next _ => exact hp

theorem scanCandidate_minInvariant [DecidableRel G.Adj]
    (s : State V) (i : Nat) (a b : V) (h : MinInvariant M i s) :
    MinInvariant M i (scanCandidate M i a b s) := by
  refine ⟨scanCandidate_labelsSound s i a b h.1 h.2.1,
    scanCandidate_minCompleteBelow s i a b h.2.1, ?_,
    scanCandidate_seenPredecessorsRecorded s i a b h.1 h.2.1 h.2.2.1 h.2.2.2.1,
    scanCandidate_predecessorsSound s i a b h.1 h.2.1 h.2.2.2.2⟩
  intro u v k hp hk hki
  exact scanCandidate_seen_mono s i a b u v (h.2.2.1 u v k hp hk hki)

theorem scanCandidates_minInvariant [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (i : Nat) (h : MinInvariant M i s) :
    MinInvariant M i (scanCandidates M i xs s) := by
  induction xs generalizing s with
  | nil => exact h
  | cons e es ih => exact ih _ (scanCandidate_minInvariant s i e.1 e.2 h)

theorem scanCandidates_frontierAvailable [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (i : Nat) (h : MinInvariant M i s)
    (hf : FrontierAvailable M i s) : FrontierAvailable M i (scanCandidates M i xs s) := by
  induction xs generalizing s with
  | nil => exact hf
  | cons e es ih =>
    exact ih _ (scanCandidate_minInvariant s i e.1 e.2 h)
      (scanCandidate_frontierAvailable s i e.1 e.2 h.1 h.2.1 hf)

theorem scanCandidates_seen_mono [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (i : Nat) (u v : V) (h : seen s u v = true) :
    seen (scanCandidates M i xs s) u v = true := by
  induction xs generalizing s with
  | nil => exact h
  | cons e es ih => exact ih _ (scanCandidate_seen_mono s i e.1 e.2 u v h)

/-- A listed edge with the semantic level-i parity guard is eventually scanned,
for any candidate order. Known frontier labels survive all preceding scans. -/
theorem scanCandidates_marks_member [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (i : Nat) (u v : V)
    (h : MinInvariant M i s) (hf : FrontierAvailable M i s)
    (hmem : (u, v) ∈ xs) (hadj : G.Adj u v)
    (hu : level M (i % 2) u = some i) (hpar : (M.mate u = some v) ↔ i % 2 = 1) :
    seen (scanCandidates M i xs s) u v = true := by
  induction xs generalizing s with
  | nil => simp at hmem
  | cons e es ih =>
    rcases List.mem_cons.mp hmem with he | he
    · subst e
      have hguard : scanCandidate M i u v s = scan M i u v s := by
        simp [scanCandidate, hadj, hf u hu, hpar]
      exact scanCandidates_seen_mono es _ i u v (by change seen (scanCandidate M i u v s) u v = true; rw [hguard]; exact scan_marks M i u v s)
    · exact ih _ (scanCandidate_minInvariant s i e.1 e.2 h)
        (scanCandidate_frontierAvailable s i e.1 e.2 h.1 h.2.1 hf) he

/-- Exhaustive MIN enumeration assigns every true next minlevel and records
all of its oriented predecessors, while preserving all recorded-state
invariants. No condition that these edges were initially unseen is needed. -/
theorem scanCandidates_complete [DecidableRel G.Adj]
    (xs : List (V × V)) (hall : ∀ u v, (u, v) ∈ xs)
    (s : State V) (i : Nat) (h : MinInvariant M i s) (hf : FrontierAvailable M i s) :
    MinInvariant M (i + 1) (scanCandidates M i xs s) ∧
      (∀ u v, minlevel M v = some (i + 1) →
        (u ∈ (scanCandidates M i xs s).predecessors v ↔ Predecessor M u v)) := by
  let result := scanCandidates M i xs s
  have hi : MinInvariant M i result := scanCandidates_minInvariant xs s i h
  have hseen (u v : V) (hv : minlevel M v = some (i + 1)) (hp : Predecessor M u v) :
      seen result u v = true := by
    obtain ⟨hadj, hu, hpar⟩ := (predecessor_iff_level_guard u v i hv).1 hp
    exact scanCandidates_marks_member xs s i u v h hf (hall u v) hadj hu hpar
  have hrecord (u v : V) (hv : minlevel M v = some (i + 1)) (hp : Predecessor M u v) :
      u ∈ result.predecessors v ∧ result.minLabel v = some (i + 1) := by
    have hh := hi.2.2.2.1 u v (hseen u v hv hp) hp
    exact ⟨hh.1, hh.2.trans hv⟩
  refine ⟨⟨hi.1, ?_, ?_, hi.2.2.2.1, hi.2.2.2.2⟩, ?_⟩
  · intro v k hv hk
    by_cases hki : k ≤ i
    · exact hi.2.1 v k hv hki
    · have he : k = i + 1 := by omega
      subst k
      obtain ⟨u, hp⟩ := minlevel_succ_has_predecessor v i hv
      exact (hrecord u v hv hp).2
  · intro u v k hp hv hk
    by_cases hki : k ≤ i
    · exact hi.2.2.1 u v k hp hv hki
    · have he : k = i + 1 := by omega
      subst k
      exact hseen u v hv hp
  · intro u v hv
    exact ⟨hi.2.2.2.2 u v, fun hp => (hrecord u v hv hp).1⟩

theorem initial_minInvariant (M : Matching G) : MinInvariant M 0 (initial M) := by
  refine ⟨initial_labelsSound M, initial_minCompleteBelow M, ?_, ?_, ?_⟩
  · intro u v k hp hv hk
    obtain ⟨p, _, hpm, hpos, _⟩ := hp
    have he := Option.some.inj (hpm.symm.trans hv)
    omega
  · intro u v hseen _
    simp [seen, initial] at hseen
  · intro u v hmem
    change u ∈ ([] : List V) at hmem
    contradiction

omit [DecidableEq V] in
theorem initial_frontierAvailable (M : Matching G) : FrontierAvailable M 0 (initial M) := by
  intro u hu
  have hfree : M.Free u := (evenlevel_zero_iff_free M u).1 hu
  have hlabel := (initial_free_iff M u).2 hfree
  simp [parityLabel, hlabel]

/-- All finite-tenacity vertices processed by earlier MAX stages have their
semantic maxlevel assigned. This describes preceding state, not the current
MIN stage's desired output. -/
def MaxCompleteBelowTenacity (M : Matching G) (t : Nat) (s : State V) : Prop :=
  ∀ v k, tenacity M v = some k → k < t → s.maxLabel v = maxlevel M v

omit [DecidableEq V] in
/-- Every parity level i is either a minlevel at most i, or a maxlevel whose
vertex tenacity is strictly below 2i+1. Thus the earlier MIN/MAX induction
hypotheses supply the actual frontier used by the executable scan guard. -/
theorem frontierAvailable_of_prior_levels (s : State V) (i : Nat)
    (hmin : MinCompleteBelow M i s) (hmax : MaxCompleteBelowTenacity M (2 * i + 1) s) :
    FrontierAvailable M i s := by
  intro v hv
  by_cases hie : i % 2 = 0
  · have he : evenlevel M v = some i := by simpa only [hie] using hv
    cases ho : oddlevel M v with
    | none =>
      have hm : minlevel M v = some i := by simp [minlevel, he, ho, levelMin]
      have hl := hmin v i hm (Nat.le_refl _)
      simp [parityLabel, hl, hie]
    | some o =>
      have hop := level_parity M 1 v o ho
      by_cases hio : i ≤ o
      · have hm : minlevel M v = some i := by simp [minlevel, he, ho, levelMin, Nat.min_eq_left hio]
        have hl := hmin v i hm (Nat.le_refl _)
        simp [parityLabel, hl, hie]
      · have hm : minlevel M v = some o := by simp [minlevel, he, ho, levelMin, Nat.min_eq_right (by omega : o ≤ i)]
        have hx : maxlevel M v = some i := by simp [maxlevel, he, ho, levelMax, Nat.max_eq_left (by omega : o ≤ i)]
        have ht : tenacity M v = some (i + o) := by simp [tenacity, he, ho, levelAdd]
        have hl := hmin v o hm (by omega)
        have hh := (hmax v (i + o) ht (by omega)).trans hx
        simp [parityLabel, hl, hh, hie, hop]
  · have hio : i % 2 = 1 := by omega
    have ho : oddlevel M v = some i := by simpa only [hio] using hv
    cases he : evenlevel M v with
    | none =>
      have hm : minlevel M v = some i := by simp [minlevel, he, ho, levelMin]
      have hl := hmin v i hm (Nat.le_refl _)
      simp [parityLabel, hl, hio]
    | some e =>
      have hep := level_parity M 0 v e he
      by_cases hie' : i ≤ e
      · have hm : minlevel M v = some i := by simp [minlevel, he, ho, levelMin, Nat.min_eq_right hie']
        have hl := hmin v i hm (Nat.le_refl _)
        simp [parityLabel, hl, hio]
      · have hm : minlevel M v = some e := by simp [minlevel, he, ho, levelMin, Nat.min_eq_left (by omega : e ≤ i)]
        have hx : maxlevel M v = some i := by simp [maxlevel, he, ho, levelMax, Nat.max_eq_right (by omega : e ≤ i)]
        have ht : tenacity M v = some (e + i) := by simp [tenacity, he, ho, levelAdd]
        have hl := hmin v e hm (by omega)
        have hh := (hmax v (e + i) ht (by omega)).trans hx
        simp [parityLabel, hl, hh, hio, hep]

/-- A concrete finite enumeration, including both orientations. The semantic
proof imposes no edge order. This definition does not claim linear enumeration
cost: all vertex pairs are generated. -/
def allCandidates (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => (u, v)

theorem mem_allCandidates {n : Nat} (u v : Fin n) : (u, v) ∈ allCandidates n := by
  simp [allCandidates]

def scanLevel {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (s : State (Fin n)) : State (Fin n) :=
  scanCandidates M i (allCandidates n) s

theorem scanLevel_complete {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (s : State (Fin n))
    (h : MinInvariant M i s) (hf : FrontierAvailable M i s) :
    MinInvariant M (i + 1) (scanLevel M i s) ∧
      (∀ u v, minlevel M v = some (i + 1) →
        (u ∈ (scanLevel M i s).predecessors v ↔ Predecessor M u v)) :=
  scanCandidates_complete (allCandidates n) mem_allCandidates s i h hf

/-- Task 1 of a general MIN stage follows from the explicit previously
established state invariants and earlier MAX assignments. -/
theorem scanLevel_complete_of_prior_levels {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (s : State (Fin n))
    (h : MinInvariant M i s) (hx : MaxCompleteBelowTenacity M (2 * i + 1) s) :
    MinInvariant M (i + 1) (scanLevel M i s) ∧
      (∀ u v, minlevel M v = some (i + 1) →
        (u ∈ (scanLevel M i s).predecessors v ↔ Predecessor M u v)) :=
  scanLevel_complete M i s h (frontierAvailable_of_prior_levels s i h.2.1 hx)

/-- The first concrete MIN stage is correct without a search-completeness
premise or any earlier MAX-stage assumptions. -/
theorem initial_scanLevel_complete {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) :
    MinInvariant M 1 (scanLevel M 0 (initial M)) ∧
      (∀ u v, minlevel M v = some 1 →
        (u ∈ (scanLevel M 0 (initial M)).predecessors v ↔ Predecessor M u v)) :=
  scanLevel_complete M 0 (initial M) (initial_minInvariant M) (initial_frontierAvailable M)

end Search
end MaximumMatching
