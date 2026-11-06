import MaximumMatching.MinCorrectness

/-! Semantic preservation for the executable MIN scan. The hypotheses express
the induction invariant at the start of search level `i`; establishing it for
the synchronized MIN/MAX phase remains a separate obligation. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

theorem level_of_minlevel (v : V) (k : Nat) (hk : minlevel M v = some k) :
    level M (k % 2) v = some k := by
  obtain ⟨p, hp, hl⟩ := minlevel_witness M v k hk
  apply (level_eq_some_iff M (k % 2) v k).2
  refine ⟨⟨p, hp, hl, rfl⟩, ?_⟩
  rintro l ⟨q, hq, hql, _⟩
  have h := minlevel_le_path M v k hk q hq
  omega

theorem level_of_maxlevel (v : V) (k : Nat) (hk : maxlevel M v = some k) :
    level M (k % 2) v = some k := by
  unfold maxlevel at hk
  cases he : evenlevel M v with
  | none => simp only [he, levelMax] at hk; contradiction
  | some e =>
    cases ho : oddlevel M v with
    | none => simp only [he, ho, levelMax] at hk; contradiction
    | some o =>
      have hep := level_parity M 0 v e he
      have hop := level_parity M 1 v o ho
      have hmax : max e o = k := by simpa only [he, ho, levelMax, Option.some.injEq] using hk
      by_cases hke : k % 2 = 0
      · have hek : e = k := by omega
        simpa only [hke, hek] using he
      · have hko : k % 2 = 1 := by omega
        have hok : o = k := by omega
        simpa only [hko, hok] using ho

namespace Search
variable [DecidableEq V]

/-- Every assigned label is the corresponding semantic minlevel or maxlevel.
Unknown labels are allowed; completeness is a separate predicate. -/
def LabelsSound (M : Matching G) (s : State V) : Prop :=
  (∀ v k, s.minLabel v = some k → minlevel M v = some k) ∧
  (∀ v k, s.maxLabel v = some k → maxlevel M v = some k)

def MinCompleteBelow (M : Matching G) (i : Nat) (s : State V) : Prop :=
  ∀ v k, minlevel M v = some k → k ≤ i → s.minLabel v = some k

/-- Every earlier oriented prop has already been scanned, in either direction. -/
def EarlierPropsSeen (M : Matching G) (i : Nat) (s : State V) : Prop :=
  ∀ u v k, Predecessor M u v → minlevel M v = some k → k ≤ i → seen s u v = true

omit [DecidableEq V] in
theorem parityLabel_sound (s : State V) (hs : LabelsSound M s)
    (v : V) (parity k : Nat) (h : parityLabel s v parity = some k) :
    level M parity v = some k := by
  unfold parityLabel at h
  cases hlo : s.minLabel v with
  | none => simp [hlo] at h
  | some lo =>
    simp only [hlo] at h
    dsimp at h
    split at h
    next hp =>
      have heq := Option.some.inj h
      have hl := level_of_minlevel v lo (hs.1 v lo hlo)
      rw [hp, heq] at hl
      exact hl
    next hp =>
      cases hhi : s.maxLabel v with
      | none => simp [hhi] at h
      | some hi =>
        simp only [hhi] at h
        dsimp at h
        split at h
        next hpar =>
          have heq := Option.some.inj h
          have hl := level_of_maxlevel v hi (hs.2 v hi hhi)
          rw [hpar, heq] at hl
          exact hl
        next _ => contradiction

omit [DecidableEq V] in
/-- Completeness at earlier levels makes MIN's operational admission test a
valid lower bound on the destination's true minimum level. -/
theorem admits_semantic_lower_bound (s : State V) (i : Nat)
    (hc : MinCompleteBelow M i s) (v : V)
    (ha : admits (s.minLabel v) (i + 1) = true) :
    levelLE (some (i + 1)) (minlevel M v) := by
  cases hm : minlevel M v with
  | none => trivial
  | some k =>
    change i + 1 ≤ k
    by_cases hki : k ≤ i
    · have hlabel := hc v k hm hki
      simp only [hlabel, admits, decide_eq_true_eq] at ha
      omega
    · omega

/-- An admitted fresh scan assigns the true minimum level and records an
actual oriented predecessor. This connects `scan` to its semantic guard. -/
theorem scan_assigns_semantic (s : State V) (i : Nat) (u v : V)
    (hc : MinCompleteBelow M i s)
    (hu : level M (i % 2) u = some i) (hadj : G.Adj u v)
    (hpar : (M.mate u = some v) ↔ i % 2 = 1)
    (hseen : seen s u v = false) (ha : admits (s.minLabel v) (i + 1) = true) :
    minlevel M v = some (i + 1) ∧ Predecessor M u v ∧
      (scan M i u v s).minLabel v = some (i + 1) ∧
      (scan M i u v s).predecessors v = u :: s.predecessors v := by
  obtain ⟨hmin, hpred⟩ := minlevel_of_scan_guard u v i hu hadj hpar
    (admits_semantic_lower_bound s i hc v ha)
  have hs := scan_assigns M i u v s hseen ha
  exact ⟨hmin, hpred, hs.1, hs.2.1⟩

/-- Rejection on an unseen edge really classifies a bridge, provided all
earlier props have been scanned. Both orientations of a possible prop are
excluded, including a source scanned at its maxlevel. -/
theorem scan_rejects_bridge (s : State V) (i : Nat) (u v : V)
    (hs : LabelsSound M s) (hearlier : EarlierPropsSeen M i s)
    (hu : level M (i % 2) u = some i) (hadj : G.Adj u v)
    (hseen : seen s u v = false) (ha : admits (s.minLabel v) (i + 1) = false) :
    Bridge M u v := by
  have htarget : ∃ k, minlevel M v = some k ∧ k ≤ i := by
    cases hv : s.minLabel v with
    | none => simp only [hv, admits] at ha; contradiction
    | some k =>
      have hki : ¬i + 1 ≤ k := by simpa only [hv, admits, decide_eq_false_iff_not] using ha
      exact ⟨k, hs.1 v k hv, by omega⟩
  obtain ⟨kv, hkv, hkvi⟩ := htarget
  obtain ⟨ku, hku, hkui⟩ := minlevel_le_of_level u i hu
  refine ⟨hadj, ?_⟩
  rintro (hp | hp)
  · have h := hearlier u v kv hp hkv hkvi
    rw [hseen] at h
    contradiction
  · have h := hearlier v u ku hp hku hkui
    rw [seen_comm, hseen] at h
    contradiction

/-- Every guarded scan preserves semantic label soundness. MIN does not need
to know whether its source label is a minlevel or a maxlevel. -/
theorem scanCandidate_labelsSound [DecidableRel G.Adj] (s : State V) (i : Nat) (u v : V)
    (hs : LabelsSound M s) (hc : MinCompleteBelow M i s) :
    LabelsSound M (scanCandidate M i u v s) := by
  unfold scanCandidate
  split
  next hguard =>
    have hu := parityLabel_sound s hs u (i % 2) i hguard.2.1
    unfold scan
    split
    · exact hs
    · split
      next ha =>
        have htrue : admits (s.minLabel v) (i + 1) = true := ha
        have hmin := (minlevel_of_scan_guard u v i hu hguard.1 hguard.2.2
          (admits_semantic_lower_bound s i hc v htrue)).1
        constructor
        · intro w k hw
          change (if w = v then some (i + 1) else s.minLabel w) = some k at hw
          split at hw
          next heq =>
            have hik := Option.some.inj hw
            simpa only [heq, hik] using hmin
          next _ => exact hs.1 w k hw
        · exact hs.2
      next _ =>
        unfold enqueue
        split <;> exact hs
  next _ => exact hs

/-- Labels at completed lower levels survive every scan at the current level. -/
theorem scan_minCompleteBelow (s : State V) (i : Nat) (u v : V)
    (hc : MinCompleteBelow M i s) : MinCompleteBelow M i (scan M i u v s) := by
  intro w k hw hki
  have hlabel := hc w k hw hki
  unfold scan
  split
  · exact hlabel
  · split
    next ha =>
      change (if w = v then some (i + 1) else s.minLabel w) = some k
      by_cases heq : w = v
      · have hvlabel : s.minLabel v = some k := by simpa only [heq] using hlabel
        simp only [hvlabel, admits, decide_eq_true_eq] at ha
        omega
      · simp only [heq, ite_false, hlabel]
    next _ =>
      unfold enqueue
      split <;> exact hlabel

theorem scanCandidate_minCompleteBelow [DecidableRel G.Adj]
    (s : State V) (i : Nat) (u v : V) (hc : MinCompleteBelow M i s) :
    MinCompleteBelow M i (scanCandidate M i u v s) := by
  unfold scanCandidate
  split
  · exact scan_minCompleteBelow s i u v hc
  · exact hc

/-- A complete fold of executable MIN candidates preserves semantic label
soundness and all lower-level assignments, for every candidate order. -/
theorem scanCandidates_preserves [DecidableRel G.Adj]
    (candidates : List (V × V)) (s : State V) (i : Nat)
    (hs : LabelsSound M s) (hc : MinCompleteBelow M i s) :
    LabelsSound M (scanCandidates M i candidates s) ∧
      MinCompleteBelow M i (scanCandidates M i candidates s) := by
  induction candidates generalizing s with
  | nil => exact ⟨hs, hc⟩
  | cons e es ih =>
    exact ih (scanCandidate M i e.1 e.2 s)
      (scanCandidate_labelsSound s i e.1 e.2 hs hc)
      (scanCandidate_minCompleteBelow s i e.1 e.2 hc)

end Search

/-- Semantic level zero is exactly the set of free vertices. -/
theorem minlevel_zero_iff_free (v : V) : minlevel M v = some 0 ↔ M.Free v := by
  constructor
  · intro h
    exact (evenlevel_zero_iff_free M v).1 (level_of_minlevel v 0 h)
  · intro h
    have he := (evenlevel_zero_iff_free M v).2 h
    unfold minlevel
    rw [he]
    cases ho : oddlevel M v <;> simp [levelMin]

namespace Search
variable [DecidableEq V]

omit [DecidableEq V] in
theorem initial_labelsSound (M : Matching G) : LabelsSound M (initial M) := by
  constructor
  · intro v k h
    dsimp only [initial] at h
    split at h
    next hv =>
      have hk : k = 0 := (Option.some.inj h).symm
      subst k
      exact (minlevel_zero_iff_free v).2 hv
    next _ => contradiction
  · intro v k h
    change none = some k at h
    contradiction

omit [DecidableEq V] in
theorem initial_minCompleteBelow (M : Matching G) : MinCompleteBelow M 0 (initial M) := by
  intro v k hk hk0
  have hk' : k = 0 := by omega
  subst k
  exact (initial_free_iff M v).2 ((minlevel_zero_iff_free v).1 hk)

/-- Every candidate enumeration in the initial MIN level assigns only correct
labels, without any completeness hypothesis about the enumeration. -/
theorem initial_scanCandidates_labelsSound [DecidableRel G.Adj]
    (M : Matching G) (candidates : List (V × V)) :
    LabelsSound M (scanCandidates M 0 candidates (initial M)) :=
  (scanCandidates_preserves candidates (initial M) 0
    (initial_labelsSound M) (initial_minCompleteBelow M)).1

end Search
end MaximumMatching
