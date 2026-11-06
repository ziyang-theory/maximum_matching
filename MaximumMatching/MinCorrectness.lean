import MaximumMatching.Min
import MaximumMatching.MinLevelEdges

/-! Semantic facts for MIN, including the predecessor-honesty argument in
Theorem 8.3, Task 1 (source p.38). These results do not assume the structural
base/bridge induction or correctness of MAX. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

theorem minlevel_le_of_level (v : V) (i : Nat)
    (hi : level M (i % 2) v = some i) :
    ∃ k, minlevel M v = some k ∧ k ≤ i := by
  by_cases he : i % 2 = 0
  · have hv : evenlevel M v = some i := by simpa only [he] using hi
    unfold minlevel
    rw [hv]
    cases ho : oddlevel M v with
    | none => exact ⟨i, rfl, Nat.le_refl _⟩
    | some o => exact ⟨min i o, rfl, Nat.min_le_left _ _⟩
  · have ho : i % 2 = 1 := by omega
    have hv : oddlevel M v = some i := by simpa only [ho] using hi
    unfold minlevel
    rw [hv]
    cases he : evenlevel M v with
    | none => exact ⟨i, rfl, Nat.le_refl _⟩
    | some e => exact ⟨min e i, rfl, Nat.min_le_right _ _⟩

theorem minlevel_finite_of_path (p : AltPath M) :
    ∃ k, minlevel M p.last = some k ∧ k ≤ p.length := by
  obtain ⟨i, hi, hip⟩ := p.prefix_level_bound ⟨p.length, by omega⟩
  have hpar := level_parity M (p.length % 2) p.last i hi
  obtain ⟨k, hk, hki⟩ := minlevel_le_of_level p.last i (by rw [hpar]; exact hi)
  exact ⟨k, hk, by omega⟩

namespace AltPath

/-- The last predecessor of a minlevel path is honest, even when earlier
prefixes are dishonest and the endpoint has infinite tenacity. -/
theorem minlevel_last_predecessor_honest (p : AltPath M)
    (hmin : minlevel M p.last = some p.length) (hpos : 0 < p.length) :
    p.BFSHonest ⟨p.length - 1, by omega⟩ := by
  let i : Fin (p.length + 1) := ⟨p.length - 1, by omega⟩
  apply (p.honest_iff_level i).2
  obtain ⟨k, hk, hki⟩ := p.prefix_level_bound i
  have hkeq : k = i.val := by
    apply Nat.le_antisymm hki
    apply Nat.le_of_not_lt
    intro hlt
    obtain ⟨q, hqend, hqlen, hqpar⟩ := ((level_eq_some_iff M (i.val % 2) (p.vertex i) k).1 hk).1
    have hfresh : ∀ j, q.vertex j ≠ p.last := by
      intro j hj
      have hb := minlevel_le_path M p.last p.length hmin (q.take j.val (by omega)) hj
      simp only [take_length] at hb
      have := j.isLt
      dsimp [i] at hlt
      omega
    have ha : G.Adj q.last p.last := by
      rw [hqend]
      have h := p.adjacent ⟨p.length - 1, by omega⟩
      simpa only [i, AltPath.last, show p.length - 1 + 1 = p.length by omega] using h
    have hpar : (M.mate q.last = some p.last) ↔ q.length % 2 = 1 := by
      rw [hqend, hqlen, hqpar]
      have h := p.alternating ⟨p.length - 1, by omega⟩
      simpa only [i, AltPath.last, show p.length - 1 + 1 = p.length by omega] using h
    let r := q.append p.last hfresh ha hpar
    have hb := minlevel_le_path M p.last p.length hmin r (append_last _ _ _ _ _)
    change p.length ≤ q.length + 1 at hb
    dsimp [i] at hlt
    omega
  simpa only [hkeq] using hk

end AltPath

/-- Exact semantic guard for an oriented prop at target minlevel `i+1`.
The source may be scanned at its maxlevel: requiring its minlevel to be `i`
would incorrectly exclude these predecessors. -/
theorem predecessor_iff_level_guard (u v : V) (i : Nat)
    (hv : minlevel M v = some (i + 1)) :
    Predecessor M u v ↔ G.Adj u v ∧ level M (i % 2) u = some i ∧
      ((M.mate u = some v) ↔ i % 2 = 1) := by
  constructor
  · rintro ⟨p, hp, hmin, hpos, hu⟩
    have hl : p.length = i + 1 := Option.some.inj (hmin.symm.trans hv)
    have hpred : p.vertex ⟨i, by omega⟩ = u := by simpa only [hl, Nat.add_sub_cancel] using hu
    have hlast : p.vertex ⟨i + 1, by omega⟩ = v := by
      simpa only [AltPath.last, hl] using hp
    have hhon := (p.honest_iff_level ⟨p.length - 1, by omega⟩).1
      (p.minlevel_last_predecessor_honest (by rw [hp]; exact hmin) hpos)
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hpred, hlast] using p.adjacent ⟨i, by omega⟩
    · simpa only [hl, Nat.add_sub_cancel, hpred] using hhon
    · simpa only [hpred, hlast] using p.alternating ⟨i, by omega⟩
  · rintro ⟨hadj, hlevel, hpar⟩
    obtain ⟨p, hp, hl, _⟩ := ((level_eq_some_iff M (i % 2) u i).1 hlevel).1
    have hfresh : ∀ j, p.vertex j ≠ v := by
      intro j hj
      have hb := minlevel_le_path M v (i + 1) hv (p.take j.val (by omega)) hj
      simp only [AltPath.take_length] at hb
      have := j.isLt
      omega
    have ha : G.Adj p.last v := by rw [hp]; exact hadj
    have hpa : (M.mate p.last = some v) ↔ p.length % 2 = 1 := by
      simpa only [hp, hl] using hpar
    refine ⟨p.append v hfresh ha hpa, AltPath.append_last _ _ _ _ _, ?_, ?_⟩
    · simpa only [AltPath.append_length, hl] using hv
    · refine ⟨by simp only [AltPath.append_length]; omega, ?_⟩
      change (if h : p.length + 1 - 1 ≤ p.length then
        p.vertex ⟨p.length + 1 - 1, by omega⟩ else v) = u
      simpa only [Nat.add_sub_cancel, Nat.le_refl, dite_true, AltPath.last] using hp

/-- Scanning from an actual parity level cannot create a spurious minlevel.
The lower-bound premise expresses that all earlier minlevels were found. -/
theorem minlevel_of_scan_guard (u v : V) (i : Nat)
    (hu : level M (i % 2) u = some i) (hadj : G.Adj u v)
    (hpar : (M.mate u = some v) ↔ i % 2 = 1)
    (hlower : levelLE (some (i + 1)) (minlevel M v)) :
    minlevel M v = some (i + 1) ∧ Predecessor M u v := by
  obtain ⟨p, hp, hl, _⟩ := ((level_eq_some_iff M (i % 2) u i).1 hu).1
  have lower (q : AltPath M) (hq : q.last = v) : i + 1 ≤ q.length := by
    obtain ⟨k, hk, hkq⟩ := minlevel_finite_of_path q
    rw [hq] at hk
    rw [hk] at hlower
    change i + 1 ≤ k at hlower
    omega
  have hfresh : ∀ j, p.vertex j ≠ v := by
    intro j hj
    have hb := lower (p.take j.val (by omega)) hj
    simp only [AltPath.take_length] at hb
    have := j.isLt
    omega
  have ha : G.Adj p.last v := by rw [hp]; exact hadj
  have hpa : (M.mate p.last = some v) ↔ p.length % 2 = 1 := by
    simpa only [hp, hl] using hpar
  let q := p.append v hfresh ha hpa
  obtain ⟨k, hk, hkq⟩ := minlevel_finite_of_path q
  have hqend : q.last = v := AltPath.append_last _ _ _ _ _
  rw [hqend] at hk
  have hlow := hlower
  rw [hk] at hlow
  change i + 1 ≤ k at hlow
  change k ≤ p.length + 1 at hkq
  have hkeq : k = i + 1 := by omega
  have hv : minlevel M v = some (i + 1) := by simpa only [hkeq] using hk
  exact ⟨hv, (predecessor_iff_level_guard u v i hv).2 ⟨hadj, hu, hpar⟩⟩

end MaximumMatching

namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- An appropriate edge from a finite parity level reaches a vertex of
minlevel at most one larger. The proof retains simple paths, handling an
already-occurring destination by taking a prefix rather than appending a walk. -/
theorem minlevel_neighbor_bound (u v : V) (i : Nat)
    (hu : level M (i % 2) u = some i) (hadj : G.Adj u v)
    (hpar : (M.mate u = some v) ↔ i % 2 = 1) :
    ∃ k, minlevel M v = some k ∧ k ≤ i + 1 := by
  classical
  obtain ⟨p, hp, hl, _⟩ := ((level_eq_some_iff M (i % 2) u i).1 hu).1
  by_cases hhit : ∃ j, p.vertex j = v
  · obtain ⟨j, hj⟩ := hhit
    obtain ⟨k, hk, hkj⟩ := minlevel_finite_of_path (p.take j.val (by omega))
    rw [AltPath.take_last, hj] at hk
    simp only [AltPath.take_length] at hkj
    exact ⟨k, hk, by have := j.isLt; omega⟩
  · have hfresh : ∀ j, p.vertex j ≠ v := by
      intro j hj
      exact hhit ⟨j, hj⟩
    have ha : G.Adj p.last v := by rw [hp]; exact hadj
    have hpa : (M.mate p.last = some v) ↔ p.length % 2 = 1 := by
      simpa only [hp, hl] using hpar
    obtain ⟨k, hk, hkp⟩ := minlevel_finite_of_path (p.append v hfresh ha hpa)
    rw [AltPath.append_last] at hk
    simp only [AltPath.append_length, hl] at hkp
    exact ⟨k, hk, hkp⟩

end MaximumMatching
