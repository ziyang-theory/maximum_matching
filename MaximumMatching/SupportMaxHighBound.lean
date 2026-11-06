import MaximumMatching.SupportHighBound
import MaximumMatching.GeneralHighGeometry

/-! High-core bounds for maximum-level paths, including the shortest
augmenting-path threshold where a common base need not exist. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

private theorem even_maxlevel_strict_high_index_below_half (p : AltPath M)
    (hp : p.Shortest) (hpe : p.length % 2 = 0) (t : Nat)
    (hpt : tenacity M p.last = some t) (hmax : maxlevel M p.last = some p.length)
    (I : Fin (p.length + 1))
    (hhigh : levelLT (some t) (tenacity M (p.vertex I))) : 2 * I.val < t := by
  obtain ⟨e, o, he, ho, hep, hop, hsum⟩ := finite_levels_of_tenacity p.last t hpt
  have hpel : evenlevel M p.last = some p.length :=
    (level_eq_some_iff M 0 p.last p.length).2 (by simpa only [Shortest, hpe] using hp)
  have heq : e = p.length := Option.some.inj (he.symm.trans hpel)
  have hmax' : max e o = p.length := by
    simpa only [maxlevel, he, ho, levelMax, Option.some.injEq] using hmax
  have hqshort := (level_eq_some_iff M 1 p.last o).1 ho
  obtain ⟨q, hqend, hqlen, hqo⟩ := hqshort.1
  have hq : q.Shortest := by simpa only [Shortest, hqlen, hqo, hqend] using hqshort
  have htotal : p.length + q.length = t := by omega
  have htriangle := p.high_minlevel_triangle q hp hq hpe (by omega) hqend (by omega) I
    (by rw [htotal]; exact levelLT_le hhigh)
  have hmin := (p.limited_bfs_honesty hp I
    (by rw [hpt]; exact levelLT_le hhigh)).2 (by rw [hpt]; exact hhigh)
  rw [htotal, hmin, Option.some.injEq] at htriangle
  have htodd := tenacity_odd M p.last t hpt
  have hle := Nat.min_le_right I.val (t - I.val)
  have hIt : I.val ≤ t := by have := I.isLt; omega
  omega

/-- Strictly higher-tenacity vertices lie before the midpoint on any actual
maximum-level path. No strict augmentation threshold or common base is needed. -/
theorem maxlevel_strict_high_index_below_half (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length) (I : Fin (p.length + 1))
    (hhigh : levelLT (some t) (tenacity M (p.vertex I))) : 2 * I.val < t := by
  by_cases hpe : p.length % 2 = 0
  · exact p.even_maxlevel_strict_high_index_below_half hp hpe t hpt hmax I hhigh
  · have hpo : p.length % 2 = 1 := by omega
    have hpol : oddlevel M p.last = some p.length :=
      (level_eq_some_iff M 1 p.last p.length).2 (by simpa only [Shortest, hpo] using hp)
    cases hm : M.mate p.last with
    | none =>
      have he : evenlevel M p.last = some 0 := (evenlevel_zero_iff_free M p.last).2 hm
      have hlen : p.length = t := by
        simpa only [tenacity, he, hpol, levelAdd, Nat.zero_add, Option.some.injEq] using hpt
      obtain ⟨s, hs, hsl⟩ := p.augmenting_tenacity_bound ⟨hpo, hm⟩ I
      rw [hs] at hhigh
      change t < s at hhigh
      omega
    | some v =>
      obtain ⟨e, o, he, ho, hep, hop, hsum⟩ := finite_levels_of_tenacity p.last t hpt
      have hopeq : o = p.length := Option.some.inj (ho.symm.trans hpol)
      have hmax' : max e o = p.length := by
        simpa only [maxlevel, he, ho, levelMax, Option.some.injEq] using hmax
      let r := p.appendMatched hpo hm
      have hrlen : r.length = p.length + 1 := rfl
      have hrend : r.last = v := appendMatched_last _ _ _
      have hre : r.length % 2 = 0 := by omega
      have hr : r.Shortest := by
        unfold Shortest
        rw [hre, hrend, hrlen]
        exact (matched_shortest_iff M hm p.length).2
          (by simpa only [Shortest, hpo] using hp)
      have hrt : tenacity M r.last = some t := by
        rw [hrend]
        exact (matched_tenacity M hm).1.symm.trans hpt
      have hve : evenlevel M v = some (p.length + 1) := by
        rw [evenlevel_matched M hm, hpol]
        rfl
      have hvo : ∃ k, oddlevel M v = some k ∧ k + 1 = e := by
        have h := evenlevel_matched M (M.symm hm)
        rw [he] at h
        cases hv : oddlevel M v with
        | none => simp [hv] at h
        | some k => exact ⟨k, rfl, (by simpa only [hv, Option.map_some, Option.some.injEq] using h.symm)⟩
      obtain ⟨k, hvk, hke⟩ := hvo
      have hrmax : maxlevel M r.last = some r.length := by
        rw [hrend, hrlen]
        simp only [maxlevel, hve, hvk, levelMax, Nat.max_eq_left (by omega : k ≤ p.length + 1)]
      let J : Fin (r.length + 1) := ⟨I.val, by have := I.isLt; omega⟩
      have hvertex : r.vertex J = p.vertex I := by
        simp only [r, J, appendMatched, append, dite_eq_left (show I.val ≤ p.length by omega), Fin.eta]
      exact r.even_maxlevel_strict_high_index_below_half hr hre t hrt hrmax J
        (by rw [hvertex]; exact hhigh)

/-- Every high vertex of a maximum-level path has a finite minimum level
strictly below half the endpoint tenacity, including at the augmenting bound. -/
theorem maxlevel_high_vertex_minlevel_lt_half (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length) (I : Fin (p.length + 1))
    (hhigh : levelLE (some t) (tenacity M (p.vertex I))) :
    ∃ k, minlevel M (p.vertex I) = some k ∧ 2 * k < t := by
  by_cases heq : tenacity M (p.vertex I) = some t
  · obtain ⟨e, o, he, ho, _, _, hsum⟩ := finite_levels_of_tenacity (p.vertex I) t heq
    refine ⟨min e o, by simp only [minlevel, he, ho, levelMin], ?_⟩
    have hle := Nat.min_le_left e o
    have hle' := Nat.min_le_right e o
    have hodd := tenacity_odd M p.last t hpt
    omega
  · have hstrict : levelLT (some t) (tenacity M (p.vertex I)) := by
      cases hi : tenacity M (p.vertex I) with
      | none => trivial
      | some s =>
        have hs : t ≤ s := by simpa only [hi, levelLE] using hhigh
        have hne : s ≠ t := by intro h; apply heq; rw [hi, h]
        change t < s
        omega
    exact ⟨I.val, (p.limited_bfs_honesty hp I (by rw [hpt]; exact hhigh)).2
      (by rw [hpt]; exact hstrict),
      p.maxlevel_strict_high_index_below_half hp t hpt hmax I hstrict⟩

end MaximumMatching.AltPath
