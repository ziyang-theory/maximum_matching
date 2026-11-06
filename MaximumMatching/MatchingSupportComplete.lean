import MaximumMatching.SupportBridgeRoots
import MaximumMatching.MatchingSupportSound

/-! Converse support discovery from actual maximum-level matching paths.
Before same-level petals are formed, every semantic support member has
disjoint arms in the actual predecessor/bud graph. Therefore any returned
bottleneck region contains exactly the trigger's support, excluding its bud.
Preservation of the converse through later same-stage contractions is separate. -/
namespace MaximumMatching.DDFS
variable {V : Type} {H : LayeredGraph V}

/-- A graph path to `w` disjoint from another root-to-bottom path places `w`
strictly above every common bottleneck. Extend the first path to the bottom
and cut its actual continuation at the forced bottleneck occurrence. -/
theorem onRootTo_of_disjoint_bottom_path (hreach : ReachBottom H) {r g b w : V}
    (hb : Bottleneck H r g b) (p q : Path H)
    (hpfirst : p.first = r ∨ p.first = g) (hplast : p.last = w)
    (hqfirst : q.first = r ∨ q.first = g) (hqbottom : H.level q.last = 0)
    (hdis : p.Disjoint q) : OnRootTo (H := H) r g b w ∧ w ≠ b := by
  have hqb : q.Contains b := hb q (hqfirst.elim
    (fun h => Or.inl ⟨h, hqbottom⟩) (fun h => Or.inr ⟨h, hqbottom⟩))
  have hnp : ¬p.Contains b := fun hp => hdis b hp hqb
  have hwb : w ≠ b := by
    intro he
    apply hnp
    rw [← he, ← hplast]
    exact p.contains_last
  obtain ⟨d, hdf, hdb⟩ := hreach w
  have hj : p.last = d.first := hplast.trans hdf.symm
  let z := p.append d hj
  have hzfirst : z.first = r ∨ z.first = g := by simpa only [z, Path.append_first] using hpfirst
  have hzbottom : H.level z.last = 0 := by simpa only [z, Path.append_last] using hdb
  have hzb := hb z (hzfirst.elim
    (fun h => Or.inl ⟨h, hzbottom⟩) (fun h => Or.inr ⟨h, hzbottom⟩))
  have hdb' : d.Contains b := ((p.contains_append_iff d hj b).1 hzb).resolve_left hnp
  obtain ⟨K, hKb⟩ := hdb'
  let a := d.take K.val (by omega)
  have hja : p.last = a.first := hj
  let y := p.append a hja
  refine ⟨⟨y, ?_, ?_, ?_⟩, hwb⟩
  · simpa only [y, Path.append_first] using hpfirst
  · exact (p.append_last a hja).trans hKb
  · apply (p.contains_append_iff a hja w).2
    exact Or.inl (hplast ▸ p.contains_last)

end MaximumMatching.DDFS

namespace MaximumMatching.Search.BudGraphInvariant
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}
variable {cap cut : Nat} {s : State V} {F : BudForest V}

/-- Every actual support witness yields a disjoint pair of graph arms.
The arm ending at the supported vertex may start at either bridge bud. -/
theorem support_graph_arms (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1) (hrep : LowerBlossomRepresentation M cut s F)
    (hcap : cut + 2 ≤ 2 * cap + 1) (u v w : V)
    (he : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, s.minLabel u = some k) (hv : ∃ k, s.minLabel v = some k)
    (hsupport : InSupport M u v w) :
    ∃ p q : DDFS.Path (predecessorGraph s F h), p.last = w ∧
      (predecessorGraph s F h).level q.last = 0 ∧ p.Disjoint q ∧
      ((p.first = F.root u ∧ q.first = F.root v) ∨
        (p.first = F.root v ∧ q.first = F.root u)) := by
  obtain ⟨hb, t, ht, het, hwt, z, hzw, hzmax, I, hI⟩ := hsupport
  have hte : t = cut + 2 := Option.some.inj (het.symm.trans he)
  subst t
  have hzt : tenacity M z.last = some (cut + 2) := by rw [hzw]; exact hwt
  have hzm : maxlevel M z.last = some z.length := by rw [hzw]; exact hzmax
  rcases hI with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · have hIb : Bridge M (z.vertex ⟨I.val, by omega⟩) (z.vertex ⟨I.val + 1, by omega⟩) :=
      by rw [hleft, hright]; exact hb
    have hIt : MaximumMatching.edgeTenacity M (z.vertex ⟨I.val, by omega⟩)
        (z.vertex ⟨I.val + 1, by omega⟩) = some (cut + 2) := by rw [hleft, hright]; exact he
    obtain ⟨a, b, haf, _, hbf, hbl, hdis, hbottom⟩ := h.current_bridge_graph_arms hc ht hrep hcap z
      hzt hzm I hIb hIt (by rw [hleft]; exact hu) (by rw [hright]; exact hv)
    exact ⟨b, a, hbl.trans hzw, hbottom, DDFS.Path.disjoint_symm hdis,
      Or.inr ⟨by simpa only [hright] using hbf, by simpa only [hleft] using haf⟩⟩
  · have hIb : Bridge M (z.vertex ⟨I.val, by omega⟩) (z.vertex ⟨I.val + 1, by omega⟩) :=
      by rw [hleft, hright]; exact bridge_symm hb
    have hIt : MaximumMatching.edgeTenacity M (z.vertex ⟨I.val, by omega⟩)
        (z.vertex ⟨I.val + 1, by omega⟩) = some (cut + 2) := by
      rw [hleft, hright, edgeTenacity_symmetric v u]; exact he
    obtain ⟨a, b, haf, _, hbf, hbl, hdis, hbottom⟩ := h.current_bridge_graph_arms hc ht hrep hcap z
      hzt hzm I hIb hIt (by rw [hleft]; exact hv) (by rw [hright]; exact hu)
    exact ⟨b, a, hbl.trans hzw, hbottom, DDFS.Path.disjoint_symm hdis,
      Or.inl ⟨by simpa only [hright] using hbf, by simpa only [hleft] using haf⟩⟩

theorem support_in_bottleneck_region (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1) (hrep : LowerBlossomRepresentation M cut s F)
    (hcap : cut + 2 ≤ 2 * cap + 1) (u v w b : V)
    (he : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, s.minLabel u = some k) (hv : ∃ k, s.minLabel v = some k)
    (hb : DDFS.Bottleneck (predecessorGraph s F h) (F.root u) (F.root v) b)
    (hsupport : InSupport M u v w) :
    DDFS.OnRootTo (H := predecessorGraph s F h) (F.root u) (F.root v) b w ∧ w ≠ b := by
  obtain ⟨p, q, hpw, hqb, hdis, hstarts⟩ := h.support_graph_arms hc hrep hcap u v w he hu hv hsupport
  apply DDFS.onRootTo_of_disjoint_bottom_path h.reachBottom hb p q ?_ hpw ?_ hqb hdis
  · exact hstarts.elim (fun hh => Or.inl hh.1) (fun hh => Or.inr hh.1)
  · exact hstarts.elim (fun hh => Or.inr hh.2) (fun hh => Or.inl hh.2)

end MaximumMatching.Search.BudGraphInvariant
