import MaximumMatching.BaseGeometry
import MaximumMatching.MinScan

section MinimumBridge

/-! The unique bridge on a maxlevel path at minimum tenacity (Lemma 6.13(2)). -/
namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Precisely the middle edge is a bridge. All other edges are props, with the
predecessor direction reversed after the middle. -/
theorem minimum_bridge_iff (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (hmin : ∀ v : V, levelLE (some (p.length + q.length)) (tenacity M v))
    (i : Fin p.length) :
    Bridge M (p.vertex ⟨i.val, by omega⟩) (p.vertex ⟨i.val + 1, by omega⟩) ↔
      2 * i.val + 1 = p.length + q.length := by
  let u := p.vertex ⟨i.val, by omega⟩
  let v := p.vertex ⟨i.val + 1, by omega⟩
  have hu := p.minlevel_triangle q hp hq hpe hqo hend hinner hmin ⟨i.val, by omega⟩
  have hv := p.minlevel_triangle q hp hq hpe hqo hend hinner hmin ⟨i.val + 1, by omega⟩
  have ha : G.Adj u v := p.adjacent i
  have hpar : (M.mate u = some v) ↔ i.val % 2 = 1 := p.alternating i
  by_cases he : 2 * i.val + 1 = p.length + q.length
  · have hue : minlevel M u = some i.val := by
      simpa only [u, Nat.min_eq_left (show i.val ≤ p.length + q.length - i.val by omega)] using hu
    have hve : minlevel M v = some i.val := by
      simpa only [v, Nat.min_eq_right (show p.length + q.length - (i.val + 1) ≤ i.val + 1 by omega),
        show p.length + q.length - (i.val + 1) = i.val by omega, Nat.min_eq_right (show i.val ≤ i.val + 1 by omega)] using hv
    exact ⟨fun _ => he, fun _ => ⟨ha, not_propEdge_of_minlevel_eq M u v i.val hue hve⟩⟩
  · have hprop : PropEdge M u v := by
      by_cases hl : 2 * i.val + 1 < p.length + q.length
      · have hue : minlevel M u = some i.val := by
          simpa only [u, Nat.min_eq_left (show i.val ≤ p.length + q.length - i.val by omega)] using hu
        have hve : minlevel M v = some (i.val + 1) := by
          simpa only [v, Nat.min_eq_left (show i.val + 1 ≤ p.length + q.length - (i.val + 1) by omega)] using hv
        exact Or.inl (predecessor_of_consecutive_minlevels M u v i.val hue hve ha hpar)
      · have hue : minlevel M u = some (p.length + q.length - (i.val + 1) + 1) := by
          have hu' : minlevel M u = some (p.length + q.length - i.val) := by
            simpa only [u, Nat.min_eq_right (show p.length + q.length - i.val ≤ i.val by omega)] using hu
          simpa only [show p.length + q.length - i.val = p.length + q.length - (i.val + 1) + 1 by omega] using hu'
        have hve : minlevel M v = some (p.length + q.length - (i.val + 1)) := by
          simpa only [v, Nat.min_eq_right (show p.length + q.length - (i.val + 1) ≤ i.val + 1 by omega)] using hv
        refine Or.inr (predecessor_of_consecutive_minlevels M v u _ hve hue (G.symm ha) ?_)
        have hpmod : (p.length + q.length - (i.val + 1)) % 2 = i.val % 2 := by omega
        rw [hpmod]
        exact ⟨fun hm => hpar.1 (M.symm hm), fun h => M.symm (hpar.2 h)⟩
    exact ⟨fun hb => False.elim (hb.2 hprop), fun h => False.elim (he h)⟩

/-- The middle bridge has tenacity exactly that of the endpoint. -/
theorem minimum_middle_edge_tenacity (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (hmin : ∀ v : V, levelLE (some (p.length + q.length)) (tenacity M v))
    (i : Fin p.length) (hi : 2 * i.val + 1 = p.length + q.length) :
    edgeTenacity M (p.vertex ⟨i.val, by omega⟩) (p.vertex ⟨i.val + 1, by omega⟩) =
      some (p.length + q.length) := by
  let u := p.vertex ⟨i.val, by omega⟩
  let v := p.vertex ⟨i.val + 1, by omega⟩
  have hpar : (M.mate u = some v) ↔ i.val % 2 = 1 := p.alternating i
  have hvt : tenacity M v = some (p.length + q.length) :=
    p.tenacity_above_half q hp hq hpe hqo hend hinner hmin ⟨i.val + 1, by omega⟩ (by change p.length + q.length < 2 * (i.val + 1); omega)
  change edgeTenacity M u v = _
  unfold edgeTenacity
  by_cases hm : M.mate u = some v
  · rw [ite_eq_left hm, ← (matched_tenacity M hm).2, hvt]
  · rw [ite_eq_right hm]
    have hie : i.val % 2 = 0 := by have hn : ¬ i.val % 2 = 1 := fun h => hm (hpar.2 h); omega
    have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
    have hhu := (p.honest_iff_level ⟨i.val, by omega⟩).1
      (p.prefixes_honest_at_minimum hp _ hten hmin _)
    have hhv := (p.honest_iff_level ⟨i.val + 1, by omega⟩).1
      (p.prefixes_honest_at_minimum hp _ hten hmin _)
    have hue : evenlevel M u = some i.val := by simpa only [hie] using hhu
    have hvo : oddlevel M v = some (i.val + 1) := by
      simpa only [show (i.val + 1) % 2 = 1 by omega] using hhv
    have hve : evenlevel M v = some i.val := by
      unfold tenacity at hvt
      rw [hvo] at hvt
      cases he : evenlevel M v with
      | none => simp only [he, levelAdd] at hvt; contradiction
      | some k =>
        have hk : k + (i.val + 1) = p.length + q.length := by simpa only [he, levelAdd, Option.some.injEq] using hvt
        have hki : k = i.val := by omega
        exact congrArg some hki
    rw [hue, hve]
    simp only [levelAdd, Option.map_some]
    exact congrArg some (by omega)

/-- Minimum-tenacity case of the unique bridge assertion, for inner endpoints. -/
theorem minimum_unique_bridge (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (hmin : ∀ v : V, levelLE (some (p.length + q.length)) (tenacity M v)) :
    ∃ i : Fin p.length,
      Bridge M (p.vertex ⟨i.val, by omega⟩) (p.vertex ⟨i.val + 1, by omega⟩) ∧
      edgeTenacity M (p.vertex ⟨i.val, by omega⟩) (p.vertex ⟨i.val + 1, by omega⟩) = some (p.length + q.length) ∧
      ∀ j : Fin p.length, Bridge M (p.vertex ⟨j.val, by omega⟩) (p.vertex ⟨j.val + 1, by omega⟩) → j = i := by
  let i : Fin p.length := ⟨(p.length + q.length) / 2, by omega⟩
  have hi : 2 * i.val + 1 = p.length + q.length := by dsimp [i]; omega
  refine ⟨i, (p.minimum_bridge_iff q hp hq hpe hqo hend hinner hmin i).2 hi,
    p.minimum_middle_edge_tenacity q hp hq hpe hqo hend hinner hmin i hi, ?_⟩
  intro j hj
  have hjv := (p.minimum_bridge_iff q hp hq hpe hqo hend hinner hmin j).1 hj
  exact Fin.ext (by omega)

end AltPath
end MaximumMatching

end MinimumBridge

section MinimumBridgeAll

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

end MinimumBridgeAll

section MinimumSuffix

/-! The long parity path to a minimum-tenacity inner vertex has minimum tenacity
at every index from the short path's length onward. This strengthens the midpoint
geometry and supplies the suffix fact needed in the minimum-tenacity base case. -/
namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A first hit on an odd suffix beginning no earlier than the short path's
length must occur at an even index of the long path. An odd hit would give a
shorter same-parity replacement prefix; equality would identify the endpoint
with a strictly earlier vertex, violating simplicity. -/
theorem FirstHit.even_long_index {p q : AltPath M} {cut : Nat}
    (h : FirstHit q p cut) (hp : p.Shortest) (hpe : p.length % 2 = 0)
    (hcut : cut % 2 = 1) (hql : q.length ≤ cut)
    (hend : q.last = p.last) (_hinner : q.length < p.length) : h.pi.val % 2 = 0 := by
  by_cases he : h.pi.val % 2 = 0
  · exact he
  · have hpo : h.pi.val % 2 = 1 := by omega
    have hqo := h.odd hpe hcut
    have hb := p.no_shorter_disjoint_prefix hp h.pi.val (by omega)
      (q.take h.qi.val (by omega)) h.hit
      (by simp only [take_length, hqo, hpo]) h.forward_disjoint
    change h.pi.val ≤ h.qi.val at hb
    have hs := h.in_suffix
    have hi : h.qi.val = q.length := by omega
    have hj : h.pi.val = q.length := by omega
    have hqi : h.qi = ⟨q.length, by omega⟩ := Fin.ext hi
    have hlast : p.vertex h.pi = p.last := by
      rw [← h.hit, hqi]
      exact hend
    have heq := congrArg Fin.val (p.injective h.pi ⟨p.length, by omega⟩ hlast)
    change h.pi.val = p.length at heq
    omega

/-- After the short path's length, a first-hit splice supplies an opposite-parity
path of complementary length. The conclusion has no midpoint restriction. -/
theorem beyond_shorter_opposite (p q : AltPath M) (hp : p.Shortest)
    (hpe : p.length % 2 = 0) (hend : q.last = p.last)
    (hinner : q.length < p.length) (i : Fin (p.length + 1))
    (hi : q.length < i.val) :
    ∃ k, HasPathLength M ((i.val + 1) % 2) (p.vertex i) k ∧
      k ≤ p.length + q.length - i.val := by
  let cut := if i.val % 2 = 0 then i.val - 1 else i.val
  have hcodd : cut % 2 = 1 := by dsimp [cut]; split <;> omega
  have hcil : cut ≤ i.val := by dsimp [cut]; split <;> omega
  have hqcut : q.length ≤ cut := by dsimp [cut]; split <;> omega
  obtain ⟨h⟩ := firstHit_exists q p cut
    ⟨⟨q.length, by omega⟩, ⟨p.length, by omega⟩, by change cut ≤ p.length; omega, hend⟩
  have hqo := h.odd hpe hcodd
  have hpeven := h.even_long_index hp hpe hcodd hqcut hend hinner
  have hkj : i.val ≤ h.pi.val := by
    have hs := h.in_suffix
    dsimp [cut] at hs
    split at hs <;> omega
  let r := (q.take h.qi.val (by omega)).spliceReverse p i.val h.pi.val hkj
    (by omega) h.hit hqo hpeven (h.reverse_disjoint i.val hcil)
  have hrlen : r.length = h.qi.val + (h.pi.val - i.val) := rfl
  have hrend : r.last = p.vertex i := spliceReverse_last _ _ _ _ _ _ _ _ _ _
  refine ⟨r.length, ⟨r, hrend, rfl, by rw [hrlen]; omega⟩, ?_⟩
  rw [hrlen]
  omega

/-- Every vertex strictly after the short path's length has the same minimum
finite tenacity as the common endpoint. -/
theorem tenacity_beyond_shorter (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (hmin : ∀ v : V, levelLE (some (p.length + q.length)) (tenacity M v))
    (i : Fin (p.length + 1)) (hi : q.length < i.val) :
    tenacity M (p.vertex i) = some (p.length + q.length) := by
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hhon := p.prefixes_honest_at_minimum hp (p.length + q.length) hten hmin i
  exact (levels_of_opposite_bound (p.vertex i) i.val (p.length + q.length)
    ((p.honest_iff_level i).1 hhon) (by omega) (hmin _)
    (p.beyond_shorter_opposite q hp hpe hend hinner i hi)).1

/-- The whole suffix beginning at the short path's length has minimum tenacity.
The boundary index is odd and inherits tenacity from its matched successor. -/
theorem tenacity_suffix_minimum (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (hmin : ∀ v : V, levelLE (some (p.length + q.length)) (tenacity M v))
    (i : Fin (p.length + 1)) (hi : q.length ≤ i.val) :
    tenacity M (p.vertex i) = some (p.length + q.length) := by
  by_cases hlt : q.length < i.val
  · exact p.tenacity_beyond_shorter q hp hq hpe hqo hend hinner hmin i hlt
  · have he : i.val = q.length := by omega
    have hmatch := p.mate_next i.val (by omega) (by omega)
    have hnext := p.tenacity_beyond_shorter q hp hq hpe hqo hend hinner hmin
      ⟨i.val + 1, by omega⟩ (by change q.length < i.val + 1; omega)
    exact (matched_tenacity M hmatch).1.trans hnext

end AltPath
end MaximumMatching

end MinimumSuffix

section BaseUnique

/-! The minimum-tenacity base induction: the predecessor of an inner vertex
reduces the induction measure. The final theorem is in MinimumBase. -/
namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A minlevel predecessor of an inner endpoint, if it occurs on an even shortest
path to that endpoint, occurs at the same even index. An odd occurrence would
create vertex tenacity smaller than the assumed global minimum. -/
theorem minimum_predecessor_index (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last)
    (hmin : ∀ v : V, levelLE (some (p.length + q.length)) (tenacity M v))
    (i : Fin (p.length + 1))
    (hi : p.vertex i = q.vertex ⟨q.length - 1, by omega⟩) : i.val = q.length - 1 := by
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hqten : tenacity M q.last = some (p.length + q.length) := by rw [hend]; exact hten
  have hph := (p.honest_iff_level i).1 (p.prefixes_honest_at_minimum hp _ hten hmin i)
  have hqh := (q.honest_iff_level ⟨q.length - 1, by omega⟩).1
    (q.prefixes_honest_at_minimum hq _ hqten hmin _)
  have hue : evenlevel M (q.vertex ⟨q.length - 1, by omega⟩) = some (q.length - 1) := by
    simpa only [show (q.length - 1) % 2 = 0 by omega] using hqh
  rw [hi] at hph
  by_cases hie : i.val % 2 = 0
  · rw [hie] at hph
    exact Option.some.inj (hph.symm.trans hue)
  · have hio : i.val % 2 = 1 := by omega
    rw [hio] at hph
    have ht := hmin (q.vertex ⟨q.length - 1, by omega⟩)
    have hbad : p.length + q.length ≤ q.length - 1 + i.val := by
      simpa only [tenacity, hue, hph, levelAdd, levelLE] using ht
    omega

/-- A low-tenacity appended endpoint leaves the path's base unchanged. -/
theorem baseOnPath_append_low_iff (p : AltPath M) (v : V)
    (hfresh : ∀ i, p.vertex i ≠ v) (ha : G.Adj p.last v)
    (hpar : (M.mate p.last = some v) ↔ p.length % 2 = 1)
    (t : Nat) (hvt : tenacity M v = some t) (b : V) :
    p.BaseOnPath t b ↔ (p.append v hfresh ha hpar).BaseOnPath t b := by
  apply p.baseOnPath_initial_iff (p.append v hfresh ha hpar) (by simp)
  · intro i
    simp only [append, dite_eq_left (show i.val ≤ p.length by omega)]
  · intro j hj
    have hv : (p.append v hfresh ha hpar).vertex j = v := by
      simp only [append, dite_eq_right (show ¬j.val ≤ p.length by omega)]
    rw [hv, hvt]
    change ¬ t < t
    omega

/-- Appending the predecessor from an odd path is an alternating extension of
an even path, whenever simplicity permits it. -/
theorem inner_predecessor_append_parity (p q : AltPath M)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1) (hend : q.last = p.last) :
    (M.mate p.last = some (q.vertex ⟨q.length - 1, by omega⟩)) ↔ p.length % 2 = 1 := by
  have hlast : q.length - 1 + 1 = q.length := by omega
  have he := q.alternating ⟨q.length - 1, by omega⟩
  constructor
  · intro hm
    have hm' := M.symm hm
    rw [← hend] at hm'
    have ho : (q.length - 1) % 2 = 1 := he.1 (by simpa only [hlast, last] using hm')
    omega
  · intro h
    omega

/-- A finite-tenacity predecessor's fresh extension is its odd shortest path. -/
theorem minimum_predecessor_extension_shortest (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last)
    (hmin : ∀ v : V, levelLE (some (p.length + q.length)) (tenacity M v))
    (hfresh : ∀ i, p.vertex i ≠ q.vertex ⟨q.length - 1, by omega⟩)
    (hu : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) = some (p.length + q.length))
    (ha : G.Adj p.last (q.vertex ⟨q.length - 1, by omega⟩)) :
    (p.append _ hfresh ha (p.inner_predecessor_append_parity q hpe hqo hend)).Shortest := by
  have hten : tenacity M q.last = some (p.length + q.length) := by
    rw [hend]
    exact p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hqh := (q.honest_iff_level ⟨q.length - 1, by omega⟩).1
    (q.prefixes_honest_at_minimum hq _ hten hmin _)
  have hue : evenlevel M (q.vertex ⟨q.length - 1, by omega⟩) = some (q.length - 1) := by
    simpa only [show (q.length - 1) % 2 = 0 by omega] using hqh
  have huo : oddlevel M (q.vertex ⟨q.length - 1, by omega⟩) = some (p.length + 1) := by
    unfold tenacity at hu
    rw [hue] at hu
    cases ho : oddlevel M (q.vertex ⟨q.length - 1, by omega⟩) with
    | none => simp only [ho, levelAdd] at hu; contradiction
    | some k =>
      have hk : q.length - 1 + k = p.length + q.length := by
        simpa only [ho, levelAdd, Option.some.injEq] using hu
      exact congrArg some (by omega)
  unfold Shortest
  rw [append_length, show (p.length + 1) % 2 = 1 by omega, append_last]
  exact (level_eq_some_iff M 1 _ (p.length + 1)).1 huo


/-- The two shortest parities have the same base at minimum tenacity, assuming
base uniqueness only at strictly smaller minimum levels. This is the induction
step; the predecessor may be reached from any free root. -/
theorem minimum_parity_bases_agree (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (_ht : EligibleTenacity M (p.length + q.length))
    (hmin : ∀ v : V, levelLE (some (p.length + q.length)) (tenacity M v))
    (ih : ∀ (u : V) (k : Nat), minlevel M u = some k → k < q.length →
      tenacity M u = some (p.length + q.length) → HasUniqueBase M u (p.length + q.length))
    (b : V) :
    p.BaseOnPath (p.length + q.length) b ↔ q.BaseOnPath (p.length + q.length) b := by
  classical
  let u := q.vertex ⟨q.length - 1, by omega⟩
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hqten : tenacity M q.last = some (p.length + q.length) := by rw [hend]; exact hten
  have hqh := (q.honest_iff_level ⟨q.length - 1, by omega⟩).1
    (q.prefixes_honest_at_minimum hq _ hqten hmin _)
  have hue : evenlevel M u = some (q.length - 1) := by
    simpa only [show (q.length - 1) % 2 = 0 by omega] using hqh
  have hum : minlevel M u = some (q.length - 1) :=
    p.odd_minlevel_prefix q hp hq hpe hqo hend hinner hmin _
  have hqa : G.Adj p.last u := by
    have ha := G.symm (q.adjacent ⟨q.length - 1, by omega⟩)
    have he : q.length - 1 + 1 = q.length := by omega
    rw [← hend]
    simpa only [he, last, u] using ha
  have hqprefix : (q.take (q.length - 1) (by omega)).Shortest := by
    unfold Shortest
    rw [take_length, take_last]
    exact (level_eq_some_iff M ((q.length - 1) % 2) u (q.length - 1)).1 hqh
  have htail : ∀ j : Fin (p.length + 1), q.length - 1 < j.val →
      ¬ levelLT (some (p.length + q.length)) (tenacity M (p.vertex j)) := by
    intro j hj
    rw [p.tenacity_suffix_minimum q hp hq hpe hqo hend hinner hmin j (by omega)]
    change ¬p.length + q.length < p.length + q.length
    omega
  have hshared : ∃ c : V, p.BaseOnPath (p.length + q.length) c ∧
      q.BaseOnPath (p.length + q.length) c := by
    by_cases hut : tenacity M u = some (p.length + q.length)
    · obtain ⟨c, hc, _⟩ := ih u (q.length - 1) hum (by omega) hut
      have hqc := hc (q.take (q.length - 1) (by omega)) rfl hqprefix
      have hqc' := (q.baseOnPath_take_pred_iff (by omega) _ hqten c).1 hqc
      refine ⟨c, ?_, hqc'⟩
      by_cases hon : ∃ i : Fin (p.length + 1), p.vertex i = u
      · obtain ⟨i, hi⟩ := hon
        have hid := p.minimum_predecessor_index q hp hq hpe hqo hend hmin i hi
        have hpu : p.vertex ⟨q.length - 1, by omega⟩ = u := by
          have hie : i = ⟨q.length - 1, by omega⟩ := Fin.ext hid
          simpa only [hie] using hi
        have hpprefix : (p.take (q.length - 1) (by omega)).Shortest := by
          unfold Shortest
          rw [take_length, take_last]
          exact (level_eq_some_iff M _ _ _).1
            ((p.honest_iff_level _).1 (p.prefixes_honest_at_minimum hp _ hten hmin _))
        have hpc := hc (p.take (q.length - 1) (by omega)) hpu hpprefix
        exact ((p.take (q.length - 1) (by omega)).baseOnPath_initial_iff p
          (by simp; omega) (by intro j; rfl) _ (by simpa only [take_length] using htail) c).1 hpc
      · have hfresh : ∀ i, p.vertex i ≠ u := by intro i he; exact hon ⟨i, he⟩
        let r := p.append u hfresh hqa (p.inner_predecessor_append_parity q hpe hqo hend)
        have hr : r.Shortest := p.minimum_predecessor_extension_shortest q hp hq hpe hqo hend hmin hfresh hut hqa
        have hrc := hc r (append_last _ _ _ _ _) hr
        exact (p.baseOnPath_append_low_iff u hfresh hqa
          (p.inner_predecessor_append_parity q hpe hqo hend) _ hut c).2 hrc
    · have huhigh : levelLT (some (p.length + q.length)) (tenacity M u) := by
        have hm := hmin u
        cases hu : tenacity M u with
        | none => trivial
        | some l =>
          have hl : p.length + q.length ≤ l := by simpa only [hu, levelLE] using hm
          have hne : l ≠ p.length + q.length := by intro he; exact hut (hu.trans (congrArg some he))
          change p.length + q.length < l
          omega
      have hqc : q.BaseOnPath (p.length + q.length) u := by
        refine ⟨⟨q.length - 1, by omega⟩, rfl, huhigh, ?_⟩
        intro j hj
        have hjv : j = ⟨q.length, by omega⟩ := Fin.ext (by change j.val = q.length; change q.length - 1 < j.val at hj; omega)
        rw [hjv]
        change ¬levelLT (some (p.length + q.length)) (tenacity M q.last)
        rw [hqten]
        change ¬p.length + q.length < p.length + q.length
        omega
      have hon : ∃ i : Fin (p.length + 1), p.vertex i = u := by
        by_cases hn : ∃ i : Fin (p.length + 1), p.vertex i = u
        · exact hn
        apply False.elim
        have hfresh : ∀ i, p.vertex i ≠ u := by intro i he; exact hn ⟨i, he⟩
        let r := p.append u hfresh hqa (p.inner_predecessor_append_parity q hpe hqo hend)
        have hw : HasPathLength M 1 u (p.length + 1) :=
          ⟨r, append_last _ _ _ _ _, rfl, by omega⟩
        cases huo : oddlevel M u with
        | none => exact (level_eq_none_iff M 1 u).1 huo ⟨p.length + 1, hw⟩
        | some l =>
          have hle := ((level_eq_some_iff M 1 u l).1 huo).2 _ hw
          have hgt : p.length + q.length < q.length - 1 + l := by
            simpa only [tenacity, hue, huo, levelAdd, levelLT] using huhigh
          omega
      obtain ⟨i, hi⟩ := hon
      have hid := p.minimum_predecessor_index q hp hq hpe hqo hend hmin i hi
      refine ⟨u, ⟨i, hi, huhigh, ?_⟩, hqc⟩
      intro j hj
      exact htail j (by omega)
  obtain ⟨c, hpc, hqc⟩ := hshared
  constructor
  · intro hb
    have he := p.baseOnPath_unique _ b c hb hpc
    exact he.symm ▸ hqc
  · intro hb
    have he := q.baseOnPath_unique _ b c hb hqc
    exact he.symm ▸ hpc

end AltPath
end MaximumMatching

end BaseUnique

section MinimumBase

/-! Induction on minimum level for the common base at globally minimum finite
eligible tenacity. The inner-vertex argument uses the checked parity-agreement theorem; the
outer case reduces across its matched edge to a smaller minimum level. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V}

/-- Agreement between the even and odd shortest paths gives the common base;
existence comes from eligibility and uniqueness comes from one fixed path. -/
theorem unique_base_of_parity_agreement (M : Matching G) (t : Nat)
    (ht : EligibleTenacity M t) (v : V) (hvt : tenacity M v = some t)
    (agree : ∀ (p q : AltPath M), p.last = v → q.last = v →
      p.Shortest → q.Shortest → p.length % 2 = 0 → q.length % 2 = 1 →
      ∀ b, p.BaseOnPath t b ↔ q.BaseOnPath t b) : HasUniqueBase M v t := by
  obtain ⟨e, o, he, ho, hepar, hopar, _⟩ := finite_levels_of_tenacity v t hvt
  obtain ⟨p, hpv, hplen, _⟩ := ((level_eq_some_iff M 0 v e).1 he).1
  obtain ⟨q, hqv, hqlen, _⟩ := ((level_eq_some_iff M 1 v o).1 ho).1
  have hpe : p.length % 2 = 0 := by omega
  have hqo : q.length % 2 = 1 := by omega
  have hp : p.Shortest := by
    simpa only [AltPath.Shortest, hpe, hpv, hplen, hepar] using (level_eq_some_iff M 0 v e).1 he
  have hq : q.Shortest := by
    simpa only [AltPath.Shortest, hqo, hqv, hqlen, hopar] using (level_eq_some_iff M 1 v o).1 ho
  obtain ⟨b, hpb⟩ := p.baseOnPath_exists_of_eligible t ht
  have hqb := (agree p q hpv hqv hp hq hpe hqo b).1 hpb
  have hcommon : ∀ r : AltPath M, r.last = v → r.Shortest → r.BaseOnPath t b := by
    intro r hrv hr
    by_cases hre : r.length % 2 = 0
    · exact (agree r q hrv hqv hr hq hre hqo b).2 hqb
    · have hro : r.length % 2 = 1 := by omega
      exact (agree p r hpv hrv hp hr hpe hro b).1 hpb
  refine ⟨b, hcommon, ?_⟩
  intro c hc
  exact p.baseOnPath_unique t c b (hc p hpv hp) hpb

/-- The outer case reduces to its matched neighbor at a strictly smaller
minimum level. The only induction step left to the caller is the inner case. -/
theorem minimum_unique_base_induction (M : Matching G) (t : Nat)
    (ht : EligibleTenacity M t)
    (innerStep : ∀ (v : V) (k : Nat), minlevel M v = some k → Inner M v →
      tenacity M v = some t →
      (∀ (u : V) (j : Nat), minlevel M u = some j → j < k →
        tenacity M u = some t → HasUniqueBase M u t) → HasUniqueBase M v t)
    (v : V) (hvt : tenacity M v = some t) : HasUniqueBase M v t := by
  have aux : ∀ k (w : V), minlevel M w = some k → tenacity M w = some t →
      HasUniqueBase M w t := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro w hw hwt
      obtain ⟨e, o, he, ho, hepar, hopar, hsum⟩ := finite_levels_of_tenacity w t hwt
      by_cases houter : e < o
      · have hek : e = k := by
          simpa only [minlevel, he, ho, levelMin, Nat.min_eq_left (show e ≤ o by omega),
            Option.some.injEq] using hw
        obtain ⟨u, hm⟩ := eligible_vertex_matched M t ht w hwt
        have hodd := evenlevel_matched M (M.symm hm)
        have heven := evenlevel_matched M hm
        rw [he] at hodd
        rw [ho] at heven
        cases huo : oddlevel M u with
        | none => simp only [huo, Option.map_none] at hodd; contradiction
        | some j =>
          have hje : j + 1 = e := by
            simpa only [huo, Option.map_some, Option.some.injEq] using hodd.symm
          have huj : minlevel M u = some j := by
            simp only [minlevel, heven, Option.map_some, huo, levelMin]
            exact congrArg some (Nat.min_eq_right (by omega))
          have hut : tenacity M u = some t := (matched_tenacity M hm).1.symm.trans hwt
          have hub := ih j (by omega) u huj hut
          exact (matched_unique_base_iff M hm t hwt).2 hub
      · apply innerStep w k hw
        · refine ⟨⟨k, hw⟩, ?_⟩
          simpa only [Outer, he, ho, levelLT] using houter
        · exact hwt
        · intro u j hu hj hut
          exact ih j hj u hu hut
  obtain ⟨e, o, he, ho, _, _, _⟩ := finite_levels_of_tenacity v t hvt
  apply aux (min e o) v
  · simp only [minlevel, he, ho, levelMin]
  · exact hvt

/-- Lemma 6.13, Statement 1: every vertex of globally minimum finite eligible
tenacity has a path-independent base. The induction's inner step is discharged
by the proved parity agreement; no base-existence oracle is assumed. -/
theorem minimum_unique_base (M : Matching G) (t : Nat)
    (ht : EligibleTenacity M t)
    (hmin : ∀ w : V, levelLE (some t) (tenacity M w))
    (v : V) (hvt : tenacity M v = some t) : HasUniqueBase M v t := by
  apply minimum_unique_base_induction M t ht ?_ v hvt
  intro u k hku hinner hut ih
  apply unique_base_of_parity_agreement M t ht u hut
  intro p q hpv hqv hp hq hpe hqo b
  have he : evenlevel M u = some p.length := by
    apply (level_eq_some_iff M 0 u p.length).2
    simpa only [AltPath.Shortest, hpe, hpv] using hp
  have ho : oddlevel M u = some q.length := by
    apply (level_eq_some_iff M 1 u q.length).2
    simpa only [AltPath.Shortest, hqo, hqv] using hq
  have hsum : p.length + q.length = t := by
    simpa only [tenacity, he, ho, levelAdd, Option.some.injEq] using hut
  have hinner' : q.length < p.length := by
    have hn := hinner.2
    simp only [Outer, he, ho, levelLT] at hn
    omega
  have hkq : k = q.length := by
    have hh : min p.length q.length = k := by
      simpa only [minlevel, he, ho, levelMin, Option.some.injEq] using hku
    omega
  have ht' : EligibleTenacity M (p.length + q.length) := hsum ▸ ht
  have hmin' : ∀ w : V, levelLE (some (p.length + q.length)) (tenacity M w) := hsum ▸ hmin
  have ih' : ∀ (w : V) (j : Nat), minlevel M w = some j → j < q.length →
      tenacity M w = some (p.length + q.length) → HasUniqueBase M w (p.length + q.length) := by
    intro w j hw hj hwt
    rw [hsum] at hwt ⊢
    exact ih w j hw (by omega) hwt
  have h := p.minimum_parity_bases_agree q hp hq hpe hqo
    (hqv.trans hpv.symm) hinner' ht' hmin' ih' b
  simpa only [hsum] using h

end MaximumMatching

end MinimumBase

section PredecessorHonesty

/-! Lemma 6.18: honesty at a predecessor immediately before a vertex of the
endpoint's tenacity on a minlevel path. The proof establishes a stronger local
statement: the successor may have any tenacity at least that of the endpoint;
no restriction on the predecessor's tenacity or the path-relative base is needed.
-/
namespace MaximumMatching

variable {V : Type} {G : Graph V} {M : Matching G}

/-- Every finite tenacity is at least twice the minimum of its parity levels. -/
theorem twice_minlevel_le_tenacity (v : V) (k t : Nat)
    (hk : minlevel M v = some k) (ht : tenacity M v = some t) : 2 * k ≤ t := by
  obtain ⟨e, o, he, ho, _, _, hsum⟩ := finite_levels_of_tenacity v t ht
  have hm : min e o = k := by
    simpa only [minlevel, he, ho, levelMin, Option.some.injEq] using hk
  have he' := Nat.min_le_left e o
  have ho' := Nat.min_le_right e o
  omega

namespace AltPath

/-- A predecessor on a minimum-level path is BFS-honest whenever its successor
has tenacity at least that of the endpoint. This implies the local conclusion
of Lemma 6.18, including both endpoint parities and infinite successor tenacity. -/
theorem minlevel_predecessor_honest (p : AltPath M) (hp : p.Shortest)
    (hminpath : minlevel M p.last = some p.length)
    (t : Nat) (hten : tenacity M p.last = some t) (i : Fin p.length)
    (hsucc : levelLE (some t) (tenacity M (p.vertex ⟨i.val + 1, by omega⟩))) :
    p.BFSHonest ⟨i.val, by omega⟩ := by
  have htwice := twice_minlevel_le_tenacity p.last p.length t hminpath hten
  by_cases hie : i.val % 2 = 0
  · let u := p.vertex ⟨i.val, by omega⟩
    let w := p.vertex ⟨i.val + 1, by omega⟩
    have hsuccw : levelLE (some t) (tenacity M w) := hsucc
    have hwhon := (p.limited_bfs_honesty hp ⟨i.val + 1, by omega⟩ (by
      rw [hten]; exact hsucc)).1
    have hwo : oddlevel M w = some (i.val + 1) := by
      have hh := (p.honest_iff_level ⟨i.val + 1, by omega⟩).1 hwhon
      simpa only [show (i.val + 1) % 2 = 1 by omega] using hh
    obtain ⟨a, ha, hak⟩ := p.prefix_level_bound ⟨i.val, by omega⟩
    change a ≤ i.val at hak
    have hue : evenlevel M u = some a := by simpa only [hie] using ha
    apply (p.honest_iff_level ⟨i.val, by omega⟩).2
    change level M (i.val % 2) u = some i.val
    rw [hie]
    change evenlevel M u = some i.val
    rw [hue]
    apply congrArg some
    apply Nat.le_antisymm hak
    apply Nat.le_of_not_lt
    intro halt
    obtain ⟨q, hqu, hqa, hqpar⟩ := ((level_eq_some_iff M 0 u a).1 hue).1
    have hfresh : ∀ j, q.vertex j ≠ w := by
      intro j hj
      by_cases hje : j.val % 2 = 0
      · obtain ⟨b, hb, hbj⟩ := q.prefix_level_bound j
        have hwe : evenlevel M w = some b := by
          simpa only [hje, hj] using hb
        have hbound : t ≤ b + (i.val + 1) := by
          simpa only [tenacity, hwe, hwo, levelAdd, levelLE] using hsuccw
        omega
      · have hjo : j.val % 2 = 1 := by omega
        have hwitness : HasPathLength M 1 w j.val := by
          simpa only [hjo, hj] using q.prefix_witness j
        have hbound := ((level_eq_some_iff M 1 w (i.val + 1)).1 hwo).2 j.val hwitness
        omega
    have hpar : (M.mate q.last = some w) ↔ q.length % 2 = 1 := by
      rw [hqu, hqa]
      have hstep : (M.mate u = some w) ↔ i.val % 2 = 1 := p.alternating i
      simp only [hstep, hie, hqpar]
    have hadj : G.Adj q.last w := by rw [hqu]; exact p.adjacent i
    let r := q.append w hfresh hadj hpar
    have hr : HasPathLength M 1 w (a + 1) :=
      ⟨r, append_last _ _ _ _ _, by change q.length + 1 = a + 1; omega, by omega⟩
    have hbad := ((level_eq_some_iff M 1 w (i.val + 1)).1 hwo).2 (a + 1) hr
    omega
  · have hio : i.val % 2 = 1 := by omega
    have hmate := (p.alternating i).2 hio
    have hteneq := (matched_tenacity M hmate).1
    exact (p.limited_bfs_honesty hp ⟨i.val, by omega⟩ (by rw [hten, hteneq]; exact hsucc)).1

end AltPath
end MaximumMatching

end PredecessorHonesty
