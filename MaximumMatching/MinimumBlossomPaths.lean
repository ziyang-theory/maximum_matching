import MaximumMatching.BlossomLaminar

/-! Path confinement and edge tenacities inside minimum-tenacity blossoms. -/
namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- After a path-relative base, the global minimum-tenacity bound turns the
last-above-threshold condition into equality of tenacity. -/
theorem minimum_after_base_tenacity (p : AltPath M) (t : Nat)
    (hmin : ∀ v : V, levelLE (some t) (tenacity M v)) (b : V)
    (hb : p.BaseOnPath t b) (i j : Fin (p.length + 1))
    (hib : p.vertex i = b) (hij : i.val < j.val) :
    tenacity M (p.vertex j) = some t := by
  obtain ⟨k, hkb, _, hlast⟩ := hb
  have hik : i = k := p.injective _ _ (hib.trans hkb.symm)
  have hj := hlast j (by rw [← hik]; exact hij)
  have hm := hmin (p.vertex j)
  cases ht : tenacity M (p.vertex j) with
  | none => exact False.elim (hj (by rw [ht]; trivial))
  | some s =>
    have hts : t ≤ s := by simpa only [ht, levelLE] using hm
    have hst : ¬t < s := by simpa only [ht, levelLT] using hj
    exact congrArg some (by omega)

/-- Restricting a path after its base preserves that base. -/
theorem baseOnPath_take_after (p : AltPath M) (t : Nat) (b : V)
    (hb : p.BaseOnPath t b) (i j : Fin (p.length + 1))
    (hib : p.vertex i = b) (hij : i.val ≤ j.val) :
    (p.take j.val (by omega)).BaseOnPath t b := by
  obtain ⟨k, hkb, hhigh, hlast⟩ := hb
  have hik : i = k := p.injective _ _ (hib.trans hkb.symm)
  refine ⟨⟨i.val, by change i.val < j.val + 1; omega⟩, hib, hhigh, ?_⟩
  intro a ha
  exact hlast ⟨a.val, by have := a.isLt; change a.val < j.val + 1 at this; omega⟩
    (by
      change i.val < a.val at ha
      change k.val < a.val
      have hki := congrArg Fin.val hik
      omega)

/-- At minimum tenacity every vertex after the base has that same actual common
base, by applying the proved minimum-base theorem to the honest prefix. -/
theorem minimum_suffix_base (p : AltPath M) (hp : p.Shortest) (t : Nat)
    (ht : EligibleTenacity M t) (hpt : tenacity M p.last = some t)
    (hmin : ∀ v : V, levelLE (some t) (tenacity M v)) (b : V)
    (hb : p.BaseOnPath t b) (i j : Fin (p.length + 1))
    (hib : p.vertex i = b) (hij : i.val < j.val) :
    IsBase M (p.vertex j) b := by
  have hjt := p.minimum_after_base_tenacity t hmin b hb i j hib hij
  have hq := p.prefixes_honest_at_minimum hp t hpt hmin j
  have hqshort : (p.take j.val (by omega)).Shortest := by
    unfold Shortest
    rw [take_length, take_last]
    exact (level_eq_some_iff M _ _ _).1 ((p.honest_iff_level j).1 hq)
  have hqb := p.baseOnPath_take_after t b hb i j hib (by omega)
  obtain ⟨c, hc, _⟩ := minimum_unique_base M t ht hmin (p.vertex j) hjt
  have hqc := hc (p.take j.val (by omega)) rfl hqshort
  have hbc := (p.take j.val (by omega)).baseOnPath_unique t b c hqb hqc
  exact ⟨t, hjt, hbc.symm ▸ hc⟩

/-- Every vertex after the base of a minimum-tenacity shortest path belongs to
that source blossom. This proves the path-confinement part of the induction basis. -/
theorem minimum_suffix_in_blossom (p : AltPath M) (hp : p.Shortest) (t : Nat)
    (ht : EligibleTenacity M t) (hpt : tenacity M p.last = some t)
    (hmin : ∀ v : V, levelLE (some t) (tenacity M v)) (b : V)
    (hb : p.BaseOnPath t b) (i j : Fin (p.length + 1))
    (hib : p.vertex i = b) (hij : i.val < j.val) :
    Blossom M t b (p.vertex j) := by
  have hjb := p.minimum_suffix_base hp t ht hpt hmin b hb i j hib hij
  have hjt := p.minimum_after_base_tenacity t hmin b hb i j hib hij
  exact blossom_of_base_le t ht.1 b (p.vertex j) hjb (by rw [hjt]; exact Nat.le_refl t)

/-- Every edge after the base has exactly the minimum tenacity, including the
first unmatched edge leaving the base. This applies to either endpoint parity. -/
theorem minimum_suffix_edge_tenacity (p : AltPath M) (hp : p.Shortest) (t : Nat)
    (hpt : tenacity M p.last = some t)
    (hmin : ∀ v : V, levelLE (some t) (tenacity M v)) (b : V)
    (hb : p.BaseOnPath t b) (i : Fin (p.length + 1)) (hib : p.vertex i = b)
    (k : Fin p.length) (hik : i.val ≤ k.val) :
    edgeTenacity M (p.vertex ⟨k.val, by omega⟩) (p.vertex ⟨k.val + 1, by omega⟩) = some t := by
  let u := p.vertex ⟨k.val, by omega⟩
  let w := p.vertex ⟨k.val + 1, by omega⟩
  have hwt : tenacity M w = some t :=
    p.minimum_after_base_tenacity t hmin b hb i ⟨k.val + 1, by omega⟩ hib (by change i.val < k.val + 1; omega)
  have hm := p.alternating k
  change edgeTenacity M u w = some t
  unfold edgeTenacity
  by_cases hmatch : M.mate u = some w
  · rw [ite_eq_left hmatch, ← (matched_tenacity M hmatch).2, hwt]
  · rw [ite_eq_right hmatch]
    have hke : k.val % 2 = 0 := by
      have hn : ¬ k.val % 2 = 1 := fun h => hmatch (hm.2 h)
      omega
    have hhu := (p.honest_iff_level ⟨k.val, by omega⟩).1
      (p.prefixes_honest_at_minimum hp t hpt hmin _)
    have hhw := (p.honest_iff_level ⟨k.val + 1, by omega⟩).1
      (p.prefixes_honest_at_minimum hp t hpt hmin _)
    have hue : evenlevel M u = some k.val := by simpa only [hke] using hhu
    have hwo : oddlevel M w = some (k.val + 1) := by
      simpa only [show (k.val + 1) % 2 = 1 by omega] using hhw
    obtain ⟨e, o, he, ho, _, _, hsum⟩ := finite_levels_of_tenacity w t hwt
    have hoeq : o = k.val + 1 := Option.some.inj (ho.symm.trans hwo)
    rw [hue, he]
    simp only [levelAdd, Option.map_some]
    exact congrArg some (by omega)

end AltPath
end MaximumMatching
