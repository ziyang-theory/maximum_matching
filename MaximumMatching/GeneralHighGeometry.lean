import MaximumMatching.MinimumBridge

/-! Geometry of the high-tenacity core of a shortest maxlevel path. Unlike the
minimum-tenacity lemmas, only the vertices named in each statement need have
tenacity at least that of the endpoint. Lower blossoms elsewhere are allowed. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A high vertex has the same triangular minlevel as in the minimum case. -/
theorem high_minlevel_triangle (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (i : Fin (p.length + 1))
    (hi : levelLE (some (p.length + q.length)) (tenacity M (p.vertex i))) :
    minlevel M (p.vertex i) = some (min i.val (p.length + q.length - i.val)) := by
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hhon := (p.limited_bfs_honesty hp i (by rw [hten]; exact hi)).1
  have hlevel := (p.honest_iff_level i).1 hhon
  by_cases hhalf : 2 * i.val < p.length + q.length
  · have hm := minlevel_of_below_half (p.vertex i) i.val (p.length + q.length)
      hlevel hhalf hi
    rw [hm, Nat.min_eq_left (by omega)]
  · have hstrict : p.length + q.length < 2 * i.val := by omega
    exact (levels_of_opposite_bound (p.vertex i) i.val (p.length + q.length)
      hlevel (by omega) hi (p.above_half_opposite q hp hpe hqo hend hinner i hstrict)).2

/-- Every high vertex past the midpoint has exactly the endpoint's tenacity. -/
theorem high_tenacity_above_half (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (i : Fin (p.length + 1))
    (hi : levelLE (some (p.length + q.length)) (tenacity M (p.vertex i)))
    (hhalf : p.length + q.length < 2 * i.val) :
    tenacity M (p.vertex i) = some (p.length + q.length) := by
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hhon := (p.limited_bfs_honesty hp i (by rw [hten]; exact hi)).1
  exact (levels_of_opposite_bound (p.vertex i) i.val (p.length + q.length)
    ((p.honest_iff_level i).1 hhon) (by omega) hi
    (p.above_half_opposite q hp hpe hqo hend hinner i hhalf)).1

/-- Adjacent high vertices straddle the unique midpoint exactly when their
edge is a bridge. Edges involving low vertices require the lower-blossom step. -/
theorem high_edge_bridge_iff (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (i : Fin p.length)
    (hsource : levelLE (some (p.length + q.length))
      (tenacity M (p.vertex ⟨i.val, by omega⟩)))
    (htarget : levelLE (some (p.length + q.length))
      (tenacity M (p.vertex ⟨i.val + 1, by omega⟩))) :
    Bridge M (p.vertex ⟨i.val, by omega⟩) (p.vertex ⟨i.val + 1, by omega⟩) ↔
      2 * i.val + 1 = p.length + q.length := by
  let u := p.vertex ⟨i.val, by omega⟩
  let v := p.vertex ⟨i.val + 1, by omega⟩
  have hu := p.high_minlevel_triangle q hp hq hpe hqo hend hinner ⟨i.val, by omega⟩ hsource
  have hv := p.high_minlevel_triangle q hp hq hpe hqo hend hinner ⟨i.val + 1, by omega⟩ htarget
  have ha : G.Adj u v := p.adjacent i
  have hpar : (M.mate u = some v) ↔ i.val % 2 = 1 := p.alternating i
  by_cases he : 2 * i.val + 1 = p.length + q.length
  · have hue : minlevel M u = some i.val := by
      simpa only [u, Nat.min_eq_left (show i.val ≤ p.length + q.length - i.val by omega)] using hu
    have hve : minlevel M v = some i.val := by
      simpa only [v, Nat.min_eq_right (show p.length + q.length - (i.val + 1) ≤ i.val + 1 by omega),
        show p.length + q.length - (i.val + 1) = i.val by omega,
        Nat.min_eq_right (show i.val ≤ i.val + 1 by omega)] using hv
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

/-- The high-high midpoint bridge has the actual endpoint tenacity. This
proves the two adjacent-endpoint cases in the general bridge induction. -/
theorem high_middle_edge_tenacity (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (i : Fin p.length) (hi : 2 * i.val + 1 = p.length + q.length)
    (hsource : levelLE (some (p.length + q.length))
      (tenacity M (p.vertex ⟨i.val, by omega⟩)))
    (htarget : levelLE (some (p.length + q.length))
      (tenacity M (p.vertex ⟨i.val + 1, by omega⟩))) :
    edgeTenacity M (p.vertex ⟨i.val, by omega⟩) (p.vertex ⟨i.val + 1, by omega⟩) =
      some (p.length + q.length) := by
  let u := p.vertex ⟨i.val, by omega⟩
  let v := p.vertex ⟨i.val + 1, by omega⟩
  have hpar : (M.mate u = some v) ↔ i.val % 2 = 1 := p.alternating i
  have hvt : tenacity M v = some (p.length + q.length) :=
    p.high_tenacity_above_half q hp hq hpe hqo hend hinner ⟨i.val + 1, by omega⟩ htarget
      (by change p.length + q.length < 2 * (i.val + 1); omega)
  change edgeTenacity M u v = _
  unfold edgeTenacity
  by_cases hm : M.mate u = some v
  · rw [ite_eq_left hm, ← (matched_tenacity M hm).2, hvt]
  · rw [ite_eq_right hm]
    have hie : i.val % 2 = 0 := by have hn : ¬i.val % 2 = 1 := fun h => hm (hpar.2 h); omega
    have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
    have hhu := (p.honest_iff_level ⟨i.val, by omega⟩).1
      (p.limited_bfs_honesty hp _ (by rw [hten]; exact hsource)).1
    have hhv := (p.honest_iff_level ⟨i.val + 1, by omega⟩).1
      (p.limited_bfs_honesty hp _ (by rw [hten]; exact htarget)).1
    have hue : evenlevel M u = some i.val := by simpa only [hie] using hhu
    have hvo : oddlevel M v = some (i.val + 1) := by
      simpa only [show (i.val + 1) % 2 = 1 by omega] using hhv
    have hve : evenlevel M v = some i.val := by
      unfold tenacity at hvt
      rw [hvo] at hvt
      cases he : evenlevel M v with
      | none => simp only [he, levelAdd] at hvt; contradiction
      | some k =>
        have hk : k + (i.val + 1) = p.length + q.length := by
          simpa only [he, levelAdd, Option.some.injEq] using hvt
        exact congrArg some (by omega)
    rw [hue, hve]
    simp only [levelAdd, Option.map_some]
    exact congrArg some (by omega)

end MaximumMatching.AltPath
