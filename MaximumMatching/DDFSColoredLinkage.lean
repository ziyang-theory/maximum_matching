import MaximumMatching.DDFSCertificate
import MaximumMatching.DDFSBud
import MaximumMatching.WeightedBridgePath

/-! Per-vertex disjoint linkages in the actual reconstructed colored trees.
The paths follow the recorded parents; a continuation below the bottleneck
can be appended without meeting the opposite, strictly higher endpoint. -/
namespace MaximumMatching.DDFS
variable {V : Type} {H : LayeredGraph V}

namespace RootedTree

theorem path_within {r : V} {S : V → Prop} (T : RootedTree H r S)
    (v : V) (hv : S v) :
    ∃ p : Path H, p.first = r ∧ p.last = v ∧
      (∀ w, p.Contains w → S w) ∧
      ∀ i : Fin p.length, T.parent (p.vertex ⟨i.val + 1, by omega⟩) =
        some (p.vertex ⟨i.val, by omega⟩) := by
  obtain ⟨p, hpf, hpl, hparent⟩ := T.path v hv
  refine ⟨p, hpf, hpl, ?_, hparent⟩
  rintro w ⟨j, rfl⟩
  by_cases hj : j.val < p.length
  · exact (T.edge _ _ (hparent ⟨j.val, hj⟩)).1
  · have hjl : j = ⟨p.length, by omega⟩ := Fin.ext (by change j.val = p.length; have := j.isLt; omega)
    simpa only [hjl, show p.vertex ⟨p.length, by omega⟩ = v from hpl] using hv

/-- Two tree domains that meet only at `b` give disjoint paths to a vertex
above `b` and to `b`, respectively. -/
theorem linkage_above {r g b v : V} {S T : V → Prop}
    (A : RootedTree H r S) (B : RootedTree H g T)
    (hv : S v) (hb : T b) (hoverlap : ∀ w, S w → T w → w = b)
    (hlevel : H.level b < H.level v) : Linkage H r g v b := by
  obtain ⟨p, hpr, hpv, hps, _⟩ := A.path_within v hv
  obtain ⟨q, hqg, hqb, hqt, _⟩ := B.path_within b hb
  refine ⟨p, q, hpr, hpv, hqg, hqb, ?_⟩
  intro w hpw hqw
  have hwb := hoverlap w (hps w hpw) (hqt w hqw)
  have hl := p.last_level_le hpw
  rw [hpv, hwb] at hl
  omega

end RootedTree

namespace ColoredTrees
variable {n : Nat} {H : LayeredGraph (Fin n)} {S : Fin n → Prop} {r g b : Fin n}

/-- The actual color selects which root can be joined to the chosen vertex
while the other is joined disjointly to the reported bottleneck. -/
theorem linkage (T : ColoredTrees H S r g b) (v : Fin n)
    (hv : S v) (hlevel : H.level b < H.level v) :
    (T.color v = some false ∧ Linkage H r g v b) ∨
      (T.color v = some true ∧ Linkage H g r v b) := by
  have hne : v ≠ b := by intro he; rw [he] at hlevel; omega
  obtain ⟨c, hc⟩ := (T.domain v).2 ⟨hv, hne⟩
  cases c
  · exact Or.inl ⟨hc, T.red.linkage_above T.green (Or.inr hc) (Or.inl rfl)
      (fun w hw hw' => (T.overlap w).1 ⟨hw, hw'⟩) hlevel⟩
  · exact Or.inr ⟨hc, T.green.linkage_above T.red (Or.inr hc) (Or.inl rfl)
      (fun w hw hw' => (T.overlap w).1 ⟨hw', hw⟩) hlevel⟩

/-- Continue the opposite tree to a genuine layer-zero vertex. The selected
vertex remains strictly above the continuation, so disjointness is retained. -/
theorem bottom_linkage (T : ColoredTrees H S r g b) (hreach : ReachBottom H)
    (v : Fin n) (hv : S v) (hlevel : H.level b < H.level v) :
    ∃ p q : Path H, p.last = v ∧ H.level q.last = 0 ∧ p.Disjoint q ∧
      ((p.first = r ∧ q.first = g ∧ T.color v = some false) ∨
        (p.first = g ∧ q.first = r ∧ T.color v = some true)) := by
  obtain ⟨d, hdf, hdb⟩ := hreach b
  have extend (a c : Fin n) (hc : Linkage H a c v b) :
      ∃ p q : Path H, p.last = v ∧ H.level q.last = 0 ∧ p.Disjoint q ∧
        p.first = a ∧ q.first = c := by
    obtain ⟨p, q, hpa, hpv, hqc, hqb, hd⟩ := hc
    have hj : q.last = d.first := hqb.trans hdf.symm
    exact ⟨p, q.append d hj, hpv, by simpa only [Path.append_last] using hdb,
      p.disjoint_append_below q d hj hd (by rw [hqb, hpv]; exact hlevel),
      hpa, by simpa only [Path.append_first] using hqc⟩
  rcases T.linkage v hv hlevel with ⟨hc, hl⟩ | ⟨hc, hl⟩
  · obtain ⟨p, q, hpv, hqb, hd, hpr, hqg⟩ := extend r g hl
    exact ⟨p, q, hpv, hqb, hd, Or.inl ⟨hpr, hqg, hc⟩⟩
  · obtain ⟨p, q, hpv, hqb, hd, hpg, hqr⟩ := extend g r hl
    exact ⟨p, q, hpv, hqb, hd, Or.inr ⟨hpg, hqr, hc⟩⟩

end ColoredTrees
end MaximumMatching.DDFS
