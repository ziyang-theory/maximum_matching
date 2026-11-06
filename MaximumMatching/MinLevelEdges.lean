import MaximumMatching.Structure

/-! Relating minimum alternating-path levels to directed prop edges.
The extension theorem below has no tenacity or BFS-honesty hypothesis. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V}

theorem minlevel_witness (M : Matching G) (v : V) (k : Nat)
    (hk : minlevel M v = some k) :
    ∃ p : AltPath M, p.last = v ∧ p.length = k := by
  unfold minlevel at hk
  cases he : evenlevel M v with
  | none =>
    simp only [he, levelMin] at hk
    obtain ⟨p, hp, hl, _⟩ := ((level_eq_some_iff M 1 v k).1 hk).1
    exact ⟨p, hp, hl⟩
  | some a =>
    cases ho : oddlevel M v with
    | none =>
      simp only [he, ho, levelMin, Option.some.injEq] at hk
      obtain ⟨p, hp, hl, _⟩ := ((level_eq_some_iff M 0 v a).1 he).1
      exact ⟨p, hp, hl.trans hk⟩
    | some b =>
      simp only [he, ho, levelMin, Option.some.injEq] at hk
      by_cases hab : a ≤ b
      · have ha : a = k := by omega
        obtain ⟨p, hp, hl, _⟩ := ((level_eq_some_iff M 0 v a).1 he).1
        exact ⟨p, hp, hl.trans ha⟩
      · have hb : b = k := by omega
        obtain ⟨p, hp, hl, _⟩ := ((level_eq_some_iff M 1 v b).1 ho).1
        exact ⟨p, hp, hl.trans hb⟩

theorem minlevel_le_path (M : Matching G) (v : V) (k : Nat)
    (hk : minlevel M v = some k) (p : AltPath M) (hp : p.last = v) :
    k ≤ p.length := by
  have hw : HasPathLength M (p.length % 2) v p.length := ⟨p, hp, rfl, rfl⟩
  have hf : ∃ l, level M (p.length % 2) v = some l ∧ l ≤ p.length := by
    cases he : level M (p.length % 2) v with
    | none => exact False.elim ((level_eq_none_iff M _ v).1 he ⟨p.length, hw⟩)
    | some l => exact ⟨l, rfl, ((level_eq_some_iff M _ v l).1 he).2 _ hw⟩
  obtain ⟨l, hl, hle⟩ := hf
  unfold minlevel at hk
  have hpar : p.length % 2 = 0 ∨ p.length % 2 = 1 := by omega
  rcases hpar with hpar | hpar
  · rw [hpar] at hl
    change evenlevel M v = some l at hl
    rw [hl] at hk
    cases ho : oddlevel M v <;> simp only [ho, levelMin, Option.some.injEq] at hk <;> omega
  · rw [hpar] at hl
    change oddlevel M v = some l at hl
    rw [hl] at hk
    cases he : evenlevel M v <;> simp only [he, levelMin, Option.some.injEq] at hk <;> omega

/-- A predecessor has strictly smaller minimum level whenever both are finite.
The prefix need not itself attain its minimum level. -/
theorem predecessor_minlevel_lt (M : Matching G) (u v : V) (i j : Nat)
    (hpred : Predecessor M u v)
    (hu : minlevel M u = some i) (hv : minlevel M v = some j) : i < j := by
  obtain ⟨p, hp, hmin, hpos, hend⟩ := hpred
  have hlen : p.length = j := Option.some.inj (hmin.symm.trans hv)
  have hb := minlevel_le_path M u i hu (p.take (p.length - 1) (by omega)) hend
  simp only [AltPath.take_length] at hb
  omega

theorem not_propEdge_of_minlevel_eq (M : Matching G) (u v : V) (k : Nat)
    (hu : minlevel M u = some k) (hv : minlevel M v = some k) :
    ¬ PropEdge M u v := by
  rintro (h | h)
  · have := predecessor_minlevel_lt M u v k k h hu hv
    omega
  · have := predecessor_minlevel_lt M v u k k h hv hu
    omega

/-- Consecutive minimum levels, adjacency, and the required matching parity
suffice for the edge to be an oriented prop. Freshness follows from minimality. -/
theorem predecessor_of_consecutive_minlevels (M : Matching G) (u v : V) (k : Nat)
    (hu : minlevel M u = some k) (hv : minlevel M v = some (k + 1))
    (hadj : G.Adj u v) (hpar : (M.mate u = some v) ↔ k % 2 = 1) :
    Predecessor M u v := by
  obtain ⟨p, hp, hl⟩ := minlevel_witness M u k hu
  have hfresh : ∀ i, p.vertex i ≠ v := by
    intro i hi
    have hb := minlevel_le_path M v (k + 1) hv (p.take i.val (by omega))
      (by simpa only [AltPath.take_last] using hi)
    simp only [AltPath.take_length] at hb
    omega
  have ha : G.Adj p.last v := hp ▸ hadj
  have hpa : (M.mate p.last = some v) ↔ p.length % 2 = 1 := by
    simpa only [hp, hl] using hpar
  let q := p.append v hfresh ha hpa
  refine ⟨q, p.append_last v hfresh ha hpa, ?_, ?_⟩
  · simpa only [q, AltPath.append_length, hl] using hv
  · refine ⟨by change 0 < p.length + 1; omega, ?_⟩
    change (if h : p.length + 1 - 1 ≤ p.length then
      p.vertex ⟨p.length + 1 - 1, by omega⟩ else v) = u
    simpa only [Nat.add_sub_cancel, Nat.le_refl, dite_true] using (show p.vertex ⟨p.length, by omega⟩ = u from hp)

end MaximumMatching
