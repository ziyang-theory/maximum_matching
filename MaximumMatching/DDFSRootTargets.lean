import MaximumMatching.DDFSBud

namespace MaximumMatching.DDFS
variable {n : Nat} {H : LayeredGraph (Fin n)}

/-- Root-valued search edges preserve the root representation along every
actual path whose initial vertex is a fixed forest root. -/
theorem Path.fixed_roots (p : Path H) (F : BudForest (Fin n))
    (hedge : ∀ u v, H.Edge u v → F.parent v = v)
    (hfirst : F.parent p.first = p.first) (j : Fin (p.length + 1)) :
    F.parent (p.vertex j) = p.vertex j := by
  by_cases hj : j.val = 0
  · have hj0 : j = ⟨0, by omega⟩ := Fin.ext hj
    rw [hj0]
    exact hfirst
  · have hh := hedge _ _ (p.adjacent ⟨j.val - 1, by omega⟩)
    have he : (⟨j.val - 1 + 1, by omega⟩ : Fin (p.length + 1)) = j := Fin.ext (by change j.val - 1 + 1 = j.val; omega)
    simpa only [he] using hh

/-- The actual reported region consists of fixed roots whenever its two
starts are fixed and every search edge targets a fixed root. -/
theorem onRootTo_fixed_root (F : BudForest (Fin n))
    (hedge : ∀ u v, H.Edge u v → F.parent v = v)
    (r g b v : Fin n) (hr : F.parent r = r) (hg : F.parent g = g)
    (hv : OnRootTo (H := H) r g b v) : F.parent v = v := by
  obtain ⟨p, hfirst, _, j, hj⟩ := hv
  have hf : F.parent p.first = p.first := by
    rcases hfirst with hpr | hpg
    · rw [hpr]; exact hr
    · rw [hpg]; exact hg
  simpa only [hj] using p.fixed_roots F hedge hf j

namespace Machine

/-- The root-valued graph representation discharges selected-root fixedness
for the actual executable search and contraction, rather than assuming it
separately for the returned support. -/
theorem executeAndContract_root_targets [DecidableRel H.Edge] (hreach : ReachBottom H)
    (r g : Fin n) (F : BudForest (Fin n)) (b : Fin n) (S : Fin n → Prop)
    (trees : ColoredTrees H S r g b) (highest : HighestBottleneck H r g b)
    (region : ∀ v, S v ↔ OnRootTo (H := H) r g b v)
    (hout : executeFull hreach r g = .bottleneck b S trees highest region)
    (hrank : ∀ v, F.rank v = H.level v)
    (hedge : ∀ u v, H.Edge u v → F.parent v = v)
    (hr : F.parent r = r) (hg : F.parent g = g)
    (v : Fin n) (hv : S (F.root v)) :
    (executeAndContract hreach r g F).2.root v = b := by
  exact executeAndContract_bottleneck hreach r g F b S trees highest region hout hrank
    (fun w hw => onRootTo_fixed_root F hedge r g b w hr hg ((region w).1 hw)) v hv

end Machine
end MaximumMatching.DDFS
