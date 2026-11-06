import MaximumMatching.MinimumBridge

/-! The minimum-tenacity unique-bridge assertion for either endpoint parity.
The odd maxlevel case is reduced to the even case by its terminal matched edge;
that new edge is proved to be a prop and hence cannot be the unique bridge.
-/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

theorem finite_levels_of_tenacity (v : V) (t : Nat) (ht : tenacity M v = some t) :
    ∃ e o, evenlevel M v = some e ∧ oddlevel M v = some o ∧
      e % 2 = 0 ∧ o % 2 = 1 ∧ e + o = t := by
  unfold tenacity at ht
  cases he : evenlevel M v with
  | none => simp [he, levelAdd] at ht
  | some e =>
    cases ho : oddlevel M v with
    | none => simp [he, ho, levelAdd] at ht
    | some o =>
      refine ⟨e, o, rfl, rfl, level_parity M 0 v e he, level_parity M 1 v o ho, ?_⟩
      simpa only [he, ho, levelAdd, Option.some.injEq] using ht

theorem matched_edge_prop_of_even_minlevel {u v : V} (hm : M.mate u = some v)
    (e : Nat) (he : evenlevel M u = some e) (hmin : minlevel M u = some e) :
    PropEdge M u v := by
  obtain ⟨p, hp, hplen, hpe⟩ := ((level_eq_some_iff M 0 u e).1 he).1
  have hpm : M.mate p.last = some v := by rw [hp]; exact hm
  have hpos := p.even_matched_pos hpm
  have hlast := p.even_last_mate (by omega) hpos
  refine Or.inr ⟨p, hp, by rw [hplen]; exact hmin, hpos, ?_⟩
  exact M.mate_unique hlast hpm

namespace AltPath

/-- A path attaining the semantic maxlevel is shortest for its own parity.
The two finite parity levels cannot tie because they have opposite parity. -/
theorem shortest_of_maxlevel (p : AltPath M)
    (hmax : maxlevel M p.last = some p.length) : p.Shortest := by
  unfold maxlevel at hmax
  cases he : evenlevel M p.last with
  | none => simp only [he, levelMax] at hmax; contradiction
  | some e =>
    cases ho : oddlevel M p.last with
    | none => simp only [he, ho, levelMax] at hmax; contradiction
    | some o =>
      have hlen : max e o = p.length := by simpa only [he, ho, levelMax, Option.some.injEq] using hmax
      have he0 := level_parity M 0 p.last e he
      have ho1 := level_parity M 1 p.last o ho
      by_cases hp0 : p.length % 2 = 0
      · have hep : e = p.length := by omega
        unfold Shortest
        rw [hp0]
        exact (level_eq_some_iff M 0 p.last p.length).1 (by rw [← hep]; exact he)
      · have hp1 : p.length % 2 = 1 := by omega
        have hop : o = p.length := by omega
        unfold Shortest
        rw [hp1]
        exact (level_eq_some_iff M 1 p.last p.length).1 (by rw [← hop]; exact ho)

/-- All-parity statement of a unique bridge occurrence and its tenacity. -/
def UniqueTenacityBridge (p : AltPath M) (t : Nat) : Prop :=
  ∃ i : Fin p.length,
    Bridge M (p.vertex ⟨i.val, by omega⟩) (p.vertex ⟨i.val + 1, by omega⟩) ∧
    edgeTenacity M (p.vertex ⟨i.val, by omega⟩) (p.vertex ⟨i.val + 1, by omega⟩) = some t ∧
    ∀ j : Fin p.length, Bridge M (p.vertex ⟨j.val, by omega⟩)
      (p.vertex ⟨j.val + 1, by omega⟩) → j = i

theorem minimum_unique_bridge_even_maxlevel (p : AltPath M) (hp : p.Shortest)
    (hpe : p.length % 2 = 0) (t : Nat) (ht : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length)
    (hmin : ∀ v : V, levelLE (some t) (tenacity M v)) :
    p.UniqueTenacityBridge t := by
  obtain ⟨e, o, he, ho, he0, ho1, heo⟩ := finite_levels_of_tenacity p.last t ht
  have hpel : evenlevel M p.last = some p.length :=
    (level_eq_some_iff M 0 p.last p.length).2 (by simpa only [Shortest, hpe] using hp)
  have hpeeq : e = p.length := Option.some.inj (he.symm.trans hpel)
  have hmax' : max e o = p.length := by
    simpa only [maxlevel, he, ho, levelMax, Option.some.injEq] using hmax
  have hoe : o < p.length := by omega
  have hqshort := (level_eq_some_iff M 1 p.last o).1 ho
  obtain ⟨q, hqend, hqlen, hqo⟩ := hqshort.1
  have hq : q.Shortest := by
    simpa only [Shortest, hqlen, hqo, hqend] using hqshort
  have hsum : p.length + q.length = t := by omega
  have hh := p.minimum_unique_bridge q hp hq hpe (by omega) hqend (by omega)
    (by rw [hsum]; exact hmin)
  simpa only [UniqueTenacityBridge, hsum] using hh

/-- Lemma 6.13(2), minimum-tenacity case, for every maxlevel path and both
endpoint parities. Eligibility excludes a free endpoint in the odd case. -/
theorem minimum_unique_bridge_maxlevel (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (ht : EligibleTenacity M t) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length)
    (hmin : ∀ v : V, levelLE (some t) (tenacity M v)) :
    p.UniqueTenacityBridge t := by
  by_cases hpe : p.length % 2 = 0
  · exact p.minimum_unique_bridge_even_maxlevel hp hpe t hpt hmax hmin
  · have hpo : p.length % 2 = 1 := by omega
    obtain ⟨v, hmate⟩ := eligible_vertex_matched M t ht p.last hpt
    obtain ⟨e, o, he, ho, he0, ho1, heo⟩ := finite_levels_of_tenacity p.last t hpt
    have hpol : oddlevel M p.last = some p.length :=
      (level_eq_some_iff M 1 p.last p.length).2 (by simpa only [Shortest, hpo] using hp)
    have hopeq : o = p.length := Option.some.inj (ho.symm.trans hpol)
    have hmax' : max e o = p.length := by
      simpa only [maxlevel, he, ho, levelMax, Option.some.injEq] using hmax
    have heo' : e < o := by omega
    have hminu : minlevel M p.last = some e := by
      simp only [minlevel, he, ho, levelMin, Nat.min_eq_left (by omega : e ≤ o)]
    have hprop := matched_edge_prop_of_even_minlevel hmate e he hminu
    let r := p.appendMatched hpo hmate
    have hrlen : r.length = p.length + 1 := rfl
    have hrend : r.last = v := appendMatched_last _ _ _
    have hre : r.length % 2 = 0 := by omega
    have hr : r.Shortest := by
      unfold Shortest
      rw [hre, hrend, hrlen]
      exact (matched_shortest_iff M hmate p.length).2
        (by simpa only [Shortest, hpo] using hp)
    have hrt : tenacity M r.last = some t := by
      rw [hrend]
      exact (matched_tenacity M hmate).1.symm.trans hpt
    have hve : evenlevel M v = some (p.length + 1) := by
      rw [evenlevel_matched M hmate, hpol]
      rfl
    have hvo : ∃ k, oddlevel M v = some k ∧ k + 1 = e := by
      have h := evenlevel_matched M (M.symm hmate)
      rw [he] at h
      cases hv : oddlevel M v with
      | none => simp [hv] at h
      | some k => exact ⟨k, rfl, (by simpa only [hv, Option.map_some, Option.some.injEq] using h.symm)⟩
    obtain ⟨k, hvk, hke⟩ := hvo
    have hrmax : maxlevel M r.last = some r.length := by
      rw [hrend, hrlen]
      simp only [maxlevel, hve, hvk, levelMax, Nat.max_eq_left (by omega : k ≤ p.length + 1)]
    obtain ⟨i, hib, hit, hiuniq⟩ := r.minimum_unique_bridge_even_maxlevel hr hre t hrt hrmax hmin
    have hir : i.val < p.length := by
      by_cases hi : i.val < p.length
      · exact hi
      · have hiv : i.val = p.length := by have := i.isLt; omega
        have hb : Bridge M p.last v := by
          simpa only [last, r, appendMatched, append, hiv, Nat.le_refl, dite_true,
            show ¬p.length + 1 ≤ p.length by omega, dite_false] using hib
        exact False.elim (hb.2 hprop)
    have rvertex (j : Nat) (hj : j ≤ p.length) :
        r.vertex ⟨j, by rw [hrlen]; omega⟩ = p.vertex ⟨j, by omega⟩ := by
      simp only [r, appendMatched, append, dite_eq_left hj]
    refine ⟨⟨i.val, hir⟩, ?_, ?_, ?_⟩
    · simpa only [rvertex i.val (by omega), rvertex (i.val + 1) (by omega)] using hib
    · simpa only [rvertex i.val (by omega), rvertex (i.val + 1) (by omega)] using hit
    · intro j hj
      have hrj : Bridge M (r.vertex ⟨j.val, by rw [hrlen]; omega⟩)
          (r.vertex ⟨j.val + 1, by rw [hrlen]; omega⟩) := by
        simpa only [rvertex j.val (by omega), rvertex (j.val + 1) (by omega)] using hj
      have heq := hiuniq ⟨j.val, by rw [hrlen]; omega⟩ hrj
      exact Fin.ext (congrArg (fun x : Fin r.length => x.val) heq)

/-- The paper's formulation needs only an actual maxlevel path; its parity
shortestness is derived rather than required as an additional premise. -/
theorem minimum_maxlevel_path_unique_bridge (p : AltPath M)
    (t : Nat) (ht : EligibleTenacity M t) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length)
    (hmin : ∀ v : V, levelLE (some t) (tenacity M v)) :
    p.UniqueTenacityBridge t :=
  p.minimum_unique_bridge_maxlevel (p.shortest_of_maxlevel hmax) t ht hpt hmax hmin

end AltPath
end MaximumMatching
