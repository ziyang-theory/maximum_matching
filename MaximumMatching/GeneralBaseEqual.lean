import MaximumMatching.GeneralBaseStep

/-! The equal-tenacity predecessor case of the general common-base induction.
Only the predecessor's tenacity is constrained; lower-tenacity vertices elsewhere
in either path are allowed. -/
namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- At an inner endpoint, an equal-tenacity predecessor has evenlevel `O-1`
and oddlevel `E+1`, where `E` and `O` are the endpoint's shortest levels. -/
theorem equal_predecessor_levels (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (hu : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) = some (p.length + q.length)) :
    evenlevel M (q.vertex ⟨q.length - 1, by omega⟩) = some (q.length - 1) ∧
      oddlevel M (q.vertex ⟨q.length - 1, by omega⟩) = some (p.length + 1) ∧
      minlevel M (q.vertex ⟨q.length - 1, by omega⟩) = some (q.length - 1) := by
  let u := q.vertex ⟨q.length - 1, by omega⟩
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hqten : tenacity M q.last = some (p.length + q.length) := by rw [hend]; exact hten
  have hqh := (q.honest_iff_level ⟨q.length - 1, by omega⟩).1
    (q.limited_bfs_honesty hq _ (by rw [hqten, hu]; change _ ≤ _; omega)).1
  have hue : evenlevel M u = some (q.length - 1) := by
    simpa only [show (q.length - 1) % 2 = 0 by omega] using hqh
  have huo : oddlevel M u = some (p.length + 1) := by
    change tenacity M u = _ at hu
    unfold tenacity at hu
    rw [hue] at hu
    cases ho : oddlevel M u with
    | none => simp only [ho, levelAdd] at hu; contradiction
    | some k =>
      have hk : q.length - 1 + k = p.length + q.length := by
        simpa only [ho, levelAdd, Option.some.injEq] using hu
      exact congrArg some (by omega)
  refine ⟨hue, huo, ?_⟩
  change minlevel M u = some (q.length - 1)
  simp only [minlevel, hue, huo, levelMin]
  exact congrArg some (Nat.min_eq_left (by omega))

/-- An equal-tenacity predecessor occurring on the even shortest path occurs
at its honest evenlevel index. No minimum-tenacity assumption is needed. -/
theorem equal_predecessor_index (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (hu : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) = some (p.length + q.length))
    (i : Fin (p.length + 1))
    (hi : p.vertex i = q.vertex ⟨q.length - 1, by omega⟩) : i.val = q.length - 1 := by
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  obtain ⟨hue, huo, _⟩ := p.equal_predecessor_levels q hp hq hpe hqo hend hinner hu
  have hph := (p.honest_iff_level i).1
    (p.limited_bfs_honesty hp i (by rw [hten, hi, hu]; change _ ≤ _; omega)).1
  rw [hi] at hph
  by_cases hie : i.val % 2 = 0
  · rw [hie] at hph
    exact Option.some.inj (hph.symm.trans hue)
  · have hio : i.val % 2 = 1 := by omega
    rw [hio] at hph
    have he := Option.some.inj (hph.symm.trans huo)
    omega

/-- If the equal-tenacity predecessor is absent, extending the even shortest
path by its edge to the endpoint gives an actual odd shortest path to it. -/
theorem equal_predecessor_extension_shortest (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (hu : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) = some (p.length + q.length))
    (hfresh : ∀ i, p.vertex i ≠ q.vertex ⟨q.length - 1, by omega⟩)
    (ha : G.Adj p.last (q.vertex ⟨q.length - 1, by omega⟩)) :
    (p.append _ hfresh ha (p.inner_predecessor_append_parity q hpe hqo hend)).Shortest := by
  have huo := (p.equal_predecessor_levels q hp hq hpe hqo hend hinner hu).2.1
  unfold Shortest
  rw [append_length, show (p.length + 1) % 2 = 1 by omega, append_last]
  exact (level_eq_some_iff M 1 _ (p.length + 1)).1 huo

/-- The equal-tenacity predecessor transfers its proved common base to both
shortest paths of the inner endpoint, even in the presence of lower blossoms. -/
theorem equal_predecessor_parity_bases_agree (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (hu : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) = some (p.length + q.length))
    (hub : HasUniqueBase M (q.vertex ⟨q.length - 1, by omega⟩) (p.length + q.length))
    (b : V) :
    p.BaseOnPath (p.length + q.length) b ↔ q.BaseOnPath (p.length + q.length) b := by
  classical
  let u := q.vertex ⟨q.length - 1, by omega⟩
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hqten : tenacity M q.last = some (p.length + q.length) := by rw [hend]; exact hten
  obtain ⟨hue, _, _⟩ := p.equal_predecessor_levels q hp hq hpe hqo hend hinner hu
  have hqprefix : (q.take (q.length - 1) (by omega)).Shortest := by
    unfold Shortest
    rw [take_length, take_last, show (q.length - 1) % 2 = 0 by omega]
    exact (level_eq_some_iff M 0 u (q.length - 1)).1 hue
  obtain ⟨c, hc, _⟩ := hub
  have hqc := hc (q.take (q.length - 1) (by omega)) rfl hqprefix
  have hqc' := (q.baseOnPath_take_pred_iff (by omega) _ hqten c).1 hqc
  have hpc : p.BaseOnPath (p.length + q.length) c := by
    by_cases hon : ∃ i : Fin (p.length + 1), p.vertex i = u
    · obtain ⟨i, hi⟩ := hon
      have hid := p.equal_predecessor_index q hp hq hpe hqo hend hinner hu i hi
      have hpu : p.vertex ⟨q.length - 1, by omega⟩ = u := by
        have hie : i = ⟨q.length - 1, by omega⟩ := Fin.ext hid
        simpa only [hie] using hi
      have hpprefix : (p.take (q.length - 1) (by omega)).Shortest := by
        unfold Shortest
        rw [take_length, take_last, show (q.length - 1) % 2 = 0 by omega, hpu]
        exact (level_eq_some_iff M 0 u (q.length - 1)).1 hue
      have hpc := hc (p.take (q.length - 1) (by omega)) hpu hpprefix
      apply ((p.take (q.length - 1) (by omega)).baseOnPath_initial_iff p
        (by simp; omega) (by intro j; rfl) _ ?_ c).1 hpc
      intro j hj
      exact p.suffix_not_high_tenacity q hp hpe hqo hend hinner j (by
        change q.length - 1 < j.val at hj
        omega)
    · have hfresh : ∀ i, p.vertex i ≠ u := by intro i he; exact hon ⟨i, he⟩
      have hqa : G.Adj p.last u := by
        have ha := G.symm (q.adjacent ⟨q.length - 1, by omega⟩)
        have he : q.length - 1 + 1 = q.length := by omega
        rw [← hend]
        simpa only [he, last, u] using ha
      let r := p.append u hfresh hqa (p.inner_predecessor_append_parity q hpe hqo hend)
      have hr : r.Shortest := p.equal_predecessor_extension_shortest q hp hq hpe hqo hend hinner hu hfresh hqa
      have hrc := hc r (append_last _ _ _ _ _) hr
      exact (p.baseOnPath_append_low_iff u hfresh hqa
        (p.inner_predecessor_append_parity q hpe hqo hend) _ hu c).2 hrc
  constructor
  · intro hb
    exact (p.baseOnPath_unique _ b c hb hpc).symm ▸ hqc'
  · intro hb
    exact (q.baseOnPath_unique _ b c hb hqc').symm ▸ hpc


/-- All predecessor cases at or above the current tenacity are discharged.
The induction hypothesis is used only at the predecessor's strictly smaller
minimum level; the strictly higher case needs no induction hypothesis. -/
theorem parity_bases_agree_of_predecessor_ge (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (hge : levelLE (some (p.length + q.length))
      (tenacity M (q.vertex ⟨q.length - 1, by omega⟩)))
    (ih : ∀ (u : V) (k : Nat), minlevel M u = some k → k < q.length →
      tenacity M u = some (p.length + q.length) → HasUniqueBase M u (p.length + q.length))
    (b : V) :
    p.BaseOnPath (p.length + q.length) b ↔ q.BaseOnPath (p.length + q.length) b := by
  by_cases heq : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) = some (p.length + q.length)
  · have hmin := (p.equal_predecessor_levels q hp hq hpe hqo hend hinner heq).2.2
    exact p.equal_predecessor_parity_bases_agree q hp hq hpe hqo hend hinner heq
      (ih _ (q.length - 1) hmin (by omega) heq) b
  · have hhigh : levelLT (some (p.length + q.length))
        (tenacity M (q.vertex ⟨q.length - 1, by omega⟩)) := by
      cases hu : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) with
      | none => trivial
      | some s =>
        have hle : p.length + q.length ≤ s := by simpa only [hu, levelLE] using hge
        have hne : s ≠ p.length + q.length := by
          intro h; exact heq (hu.trans (congrArg some h))
        change p.length + q.length < s
        omega
    obtain ⟨hpb, hqb⟩ := p.high_predecessor_bases q hp hq hpe hqo hend hinner hhigh
    constructor
    · intro hb
      exact (p.baseOnPath_unique _ _ _ hb hpb).symm ▸ hqb
    · intro hb
      exact (q.baseOnPath_unique _ _ _ hb hqb).symm ▸ hpb

end AltPath
end MaximumMatching
