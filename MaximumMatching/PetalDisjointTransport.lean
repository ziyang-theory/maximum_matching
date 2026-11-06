import MaximumMatching.PetalPathTransport

/-! Contraction preserves disjoint root arms while their target remains
outside the selected petal. Any would-be new intersection would force both
original paths through the old bottleneck. -/
namespace MaximumMatching.Search.PetalRecord
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

theorem selected_path_contains_bottleneck (R : PetalRecord M)
    (p : DDFS.Path (predecessorGraph R.prior R.forest R.invariant))
    (v : Fin n) (hv : p.Contains v) (hsel : R.selected v)
    (hlast : p.last = R.bottleneck ∨ ¬ R.selected p.last) : p.Contains R.bottleneck := by
  apply Classical.byContradiction
  intro havoid
  obtain ⟨i, hi⟩ := hv
  let q := p.drop i.val (by omega)
  have hqf : R.selected q.first := by rw [p.drop_first, hi]; exact hsel
  have hqavoid : ¬ q.Contains R.bottleneck := fun hb => havoid (p.contains_drop _ _ hb)
  have hall := q.stays_in_closed_except R.selected R.bottleneck
    (fun _ _ hw hne he => R.selected_edge_closed hw hne he) hqf hqavoid
  have hslast : R.selected p.last := by
    have hh := hall ⟨q.length, by omega⟩
    change R.selected q.last at hh
    rwa [p.drop_last] at hh
  rcases hlast with he | hn
  · exact havoid (he ▸ p.contains_last)
  · exact hn hslast

theorem selected_bottom_path_contains_bottleneck (R : PetalRecord M)
    (p : DDFS.Path (predecessorGraph R.prior R.forest R.invariant))
    (v : Fin n) (hv : p.Contains v) (hsel : R.selected v)
    (hbottom : (predecessorGraph R.prior R.forest R.invariant).level p.last = 0) :
    p.Contains R.bottleneck := by
  apply R.selected_path_contains_bottleneck p v hv hsel
  by_cases hs : R.selected p.last
  · left
    by_cases he : p.last = R.bottleneck
    · exact he
    · have hh := DDFS.onRootTo_level_gt ((R.region p.last).1 hs) he
      rw [hbottom] at hh
      omega
  · exact Or.inr hs

/-- New equal roots identify precisely equal old fixed roots or two vertices
of the actual selected region. -/
theorem after_root_eq_fixed_iff (R : PetalRecord M) (u v : Fin n)
    (hu : R.forest.root u = u) (hv : R.forest.root v = v) :
    R.after.root u = R.after.root v ↔ u = v ∨ (R.selected u ∧ R.selected v) := by
  have hselected (w : Fin n) (hw : R.forest.root w = w) (hs : R.selected w) :
      R.after.root w = R.bottleneck :=
    R.after_selected w (by change R.selected (R.forest.root w); rwa [hw])
  have houtside (w : Fin n) (hw : R.forest.root w = w) (hs : ¬ R.selected w) :
      R.after.root w = w :=
    (R.after_outside w (by change ¬ R.selected (R.forest.root w); rwa [hw])).trans hw
  constructor
  · intro he
    by_cases hsu : R.selected u
    · by_cases hsv : R.selected v
      · exact Or.inr ⟨hsu, hsv⟩
      · have hbv : R.bottleneck = v := (hselected u hu hsu).symm.trans (he.trans (houtside v hv hsv))
        exact False.elim (hsv (hbv ▸ R.trees.bottleneck_mem))
    · by_cases hsv : R.selected v
      · have hub : u = R.bottleneck := (houtside u hu hsu).symm.trans (he.trans (hselected v hv hsv))
        exact False.elim (hsu (hub.symm ▸ R.trees.bottleneck_mem))
      · exact Or.inl ((houtside u hu hsu).symm.trans (he.trans (houtside v hv hsv)))
  · rintro (rfl | ⟨hsu, hsv⟩)
    · rfl
    · exact (hselected u hu hsu).trans (hselected v hv hsv).symm

/-- Disjointness survives while the first arm's target is outside the petal
and the second arm reaches the bottom. Both resulting paths are constructed
from actual old paths; their endpoints and image sets are retained exactly. -/
theorem transport_disjoint_paths (R : PetalRecord M)
    (p q : DDFS.Path (predecessorGraph R.prior R.forest R.invariant))
    (hpfix : ∀ v, p.Contains v → R.forest.root v = v)
    (hqfix : ∀ v, q.Contains v → R.forest.root v = v)
    (hdis : p.Disjoint q) (hpend : ¬ R.selected p.last)
    (hqbottom : (predecessorGraph R.prior R.forest R.invariant).level q.last = 0) :
    ∃ a b : DDFS.Path (predecessorGraph R.prior R.after R.after_invariant),
      a.first = R.after.root p.first ∧ a.last = p.last ∧
      b.first = R.after.root q.first ∧ b.last = q.last ∧ a.Disjoint b ∧
      (∀ v, a.Contains v ↔ ∃ u, p.Contains u ∧ R.after.root u = v) ∧
      (∀ v, b.Contains v ↔ ∃ u, q.Contains u ∧ R.after.root u = v) := by
  obtain ⟨a, haf, hal, _, ha⟩ := R.transport_path p hpfix
  obtain ⟨b, hbf, hbl, _, hb⟩ := R.transport_path q hqfix
  have hplast : R.after.root p.last = p.last := by
    have hf := hpfix p.last p.contains_last
    exact (R.after_outside p.last (by change ¬ R.selected (R.forest.root p.last); rwa [hf])).trans hf
  have hqlast : R.after.root q.last = q.last := by
    have hf := hqfix q.last q.contains_last
    by_cases hs : R.selected q.last
    · have he : q.last = R.bottleneck := by
        by_cases he : q.last = R.bottleneck
        · exact he
        · have hl := DDFS.onRootTo_level_gt ((R.region q.last).1 hs) he
          rw [hqbottom] at hl
          omega
      exact (R.after_selected q.last (by change R.selected (R.forest.root q.last); rwa [hf])).trans he.symm
    · exact (R.after_outside q.last (by change ¬ R.selected (R.forest.root q.last); rwa [hf])).trans hf
  refine ⟨a, b, haf, hal.trans hplast, hbf, hbl.trans hqlast, ?_, ha, hb⟩
  intro z haz hbz
  obtain ⟨u, hpu, huz⟩ := (ha z).1 haz
  obtain ⟨v, hqv, hvz⟩ := (hb z).1 hbz
  rcases (R.after_root_eq_fixed_iff u v (hpfix u hpu) (hqfix v hqv)).1
      (huz.trans hvz.symm) with he | ⟨hsu, hsv⟩
  · exact hdis v (he ▸ hpu) hqv
  · exact hdis R.bottleneck
      (R.selected_path_contains_bottleneck p u hpu hsu (Or.inr hpend))
      (R.selected_bottom_path_contains_bottleneck q v hqv hsv hqbottom)

end MaximumMatching.Search.PetalRecord
