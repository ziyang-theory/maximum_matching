import MaximumMatching.MinimumBridgeAll
import MaximumMatching.MinimumSuffix

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
