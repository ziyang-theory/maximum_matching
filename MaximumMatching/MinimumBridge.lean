import MaximumMatching.MinTenacityGeometry
import MaximumMatching.MinLevelEdges

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
