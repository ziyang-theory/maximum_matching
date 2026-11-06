import MaximumMatching.PetalDisjointTransport
import MaximumMatching.RecursiveRemoval

/-! Bottom-path contraction and deletion are compatible: every contracted
vertex image on a bottom path already occurred on that same original path.
This retains the avoidance information needed after path deletion. -/
namespace MaximumMatching.Search.PetalRecord
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

/-- If a bottom path visits a selected root, it already visits the bottleneck;
otherwise contraction leaves that root unchanged. -/
theorem after_root_on_bottom_path (R : PetalRecord M)
    (p : DDFS.Path (predecessorGraph R.prior R.forest R.invariant))
    (hpfix : ∀ v, p.Contains v → R.forest.root v = v)
    (hbottom : (predecessorGraph R.prior R.forest R.invariant).level p.last = 0)
    (v : Fin n) (hv : p.Contains v) : p.Contains (R.after.root v) := by
  have hf := hpfix v hv
  by_cases hs : R.selected v
  · rw [R.after_selected v (by change R.selected (R.forest.root v); rwa [hf])]
    exact R.selected_bottom_path_contains_bottleneck p v hv hs hbottom
  · rw [R.after_outside v (by change ¬R.selected (R.forest.root v); rwa [hf]), hf]
    exact hv

/-- Two disjoint bottom arms survive contraction with no new original vertex
on either arm. In particular, both arms retain every previous avoidance
condition on vertices deleted by other augmentations. -/
theorem transport_disjoint_bottom_paths (R : PetalRecord M)
    (p q : DDFS.Path (predecessorGraph R.prior R.forest R.invariant))
    (hpfix : ∀ v, p.Contains v → R.forest.root v = v)
    (hqfix : ∀ v, q.Contains v → R.forest.root v = v)
    (hdis : p.Disjoint q)
    (hpb : (predecessorGraph R.prior R.forest R.invariant).level p.last = 0)
    (hqb : (predecessorGraph R.prior R.forest R.invariant).level q.last = 0) :
    ∃ a b : DDFS.Path (predecessorGraph R.prior R.after R.after_invariant),
      a.first = R.after.root p.first ∧ a.last = p.last ∧
      b.first = R.after.root q.first ∧ b.last = q.last ∧ a.Disjoint b ∧
      (∀ v, a.Contains v → p.Contains v) ∧ (∀ v, b.Contains v → q.Contains v) := by
  have hsurvive : p.last = R.bottleneck ∨ ¬R.selected p.last := by
    by_cases he : p.last = R.bottleneck
    · exact Or.inl he
    · right
      intro hs
      have hh := DDFS.onRootTo_level_gt ((R.region p.last).1 hs) he
      rw [hpb] at hh
      omega
  obtain ⟨a, b, haf, hal, hbf, hbl, hd, ha, hb⟩ :=
    R.transport_disjoint_paths_of_surviving_target p q hpfix hqfix hdis hsurvive hqb
  refine ⟨a, b, haf, hal, hbf, hbl, hd, ?_, ?_⟩
  · intro v hv
    obtain ⟨u, hu, huv⟩ := (ha v).1 hv
    rw [← huv]
    exact R.after_root_on_bottom_path p hpfix hpb u hu
  · intro v hv
    obtain ⟨u, hu, huv⟩ := (hb v).1 hv
    rw [← huv]
    exact R.after_root_on_bottom_path q hqfix hqb u hu

end MaximumMatching.Search.PetalRecord
