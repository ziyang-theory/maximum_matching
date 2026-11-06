import MaximumMatching.PetalRootExpansion
import MaximumMatching.DDFSPathMap

/-! Transport actual old root paths through a recorded petal contraction.
Bottleneck semantics proves the region is closed under edges except at its
boundary. Mapping roots then collapses only zero steps and preserves all images. -/
namespace MaximumMatching.Search.PetalRecord
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

/-- Any outgoing edge from a selected non-bottleneck vertex stays selected.
This follows from the actual all-path bottleneck, not a closure certificate. -/
theorem selected_edge_closed (R : PetalRecord M) {v w : Fin n}
    (hv : R.selected v) (hne : v ≠ R.bottleneck)
    (he : (predecessorGraph R.prior R.forest R.invariant).Edge v w) : R.selected w := by
  have hlevel := DDFS.onRootTo_level_gt ((R.region v).1 hv) hne
  obtain ⟨p, hp, hpb, i, hiv⟩ := (R.region v).1 hv
  let a := p.take i.val (by omega)
  have haf : a.first = p.first := rfl
  have hal : a.last = v := hiv
  obtain ⟨z, hzf, hz0⟩ := R.invariant.reachBottom w
  have hze : (predecessorGraph R.prior R.forest R.invariant).Edge v z.first := by
    rw [hzf]
    exact he
  let q := z.prepend v hze
  have hjoin : a.last = q.first := hal
  have hfull : (a.append q hjoin).ToBottom (R.forest.root R.left) ∨
      (a.append q hjoin).ToBottom (R.forest.root R.right) := by
    rcases hp with hp | hp
    · exact Or.inl ⟨(a.append_first q hjoin).trans (haf.trans hp),
        by rw [a.append_last]; exact hz0⟩
    · exact Or.inr ⟨(a.append_first q hjoin).trans (haf.trans hp),
        by rw [a.append_last]; exact hz0⟩
  have hbfull := R.highest.1 (a.append q hjoin) hfull
  have hbq : q.Contains R.bottleneck := by
    rcases (a.contains_append_iff q hjoin R.bottleneck).1 hbfull with hba | hbq
    · have hlow := a.last_level_le hba
      rw [hal] at hlow
      omega
    · exact hbq
  have hbz : z.Contains R.bottleneck := by
    rcases (z.contains_prepend_iff v hze R.bottleneck).1 hbq with hb | hbz
    · exact False.elim (hne hb.symm)
    · exact hbz
  obtain ⟨j, hj⟩ := hbz
  let tail := z.take j.val (by omega)
  have hte : (predecessorGraph R.prior R.forest R.invariant).Edge v tail.first := hze
  let branch := tail.prepend v hte
  have hjn : a.last = branch.first := hal
  apply (R.region w).2
  refine ⟨a.append branch hjn, ?_, ?_, ?_⟩
  · rw [a.append_first]
    exact hp
  · rw [a.append_last]
    exact (tail.prepend_last v hte).trans hj
  · apply (a.contains_append_iff branch hjn w).2
    right
    apply (tail.contains_prepend_iff v hte w).2
    right
    exact hzf ▸ tail.contains_first

/-- An original predecessor edge continues to point to the new root of its
old target. The source here is the unchanged original vertex. -/
theorem after_edge_target (R : PetalRecord M) {v w : Fin n}
    (he : (predecessorGraph R.prior R.forest R.invariant).Edge v w) :
    (predecessorGraph R.prior R.after R.after_invariant).Edge v (R.after.root w) := by
  obtain ⟨u, hu, huw⟩ := List.mem_map.mp he.2
  refine ⟨he.1, List.mem_map.mpr ⟨u, hu, ?_⟩⟩
  exact R.forest.mergeManyInto_root_congr R.trees.vertices R.bottleneck u w
    (by rw [← huw]; exact (R.forest.root_idempotent u).symm)

/-- An old fixed-root edge either collapses into one new class or remains an
actual edge between its new endpoint roots. -/
theorem after_edge_eq_or_edge (R : PetalRecord M) {v w : Fin n}
    (he : (predecessorGraph R.prior R.forest R.invariant).Edge v w)
    (hvfix : R.forest.root v = v) :
    R.after.root v = R.after.root w ∨
      (predecessorGraph R.prior R.after R.after_invariant).Edge (R.after.root v) (R.after.root w) := by
  by_cases hv : R.selected v
  · by_cases hvb : v = R.bottleneck
    · right
      have hvafter : R.after.root v = v := by
        rw [R.after_selected v (by change R.selected (R.forest.root v); rw [hvfix]; exact hv)]
        exact hvb.symm
      rw [hvafter]
      exact R.after_edge_target he
    · left
      have hw := R.selected_edge_closed hv hvb he
      have hwfix := R.forest.root_of_fixed w (R.selected_fixed w hw)
      rw [R.after_selected v (by change R.selected (R.forest.root v); rw [hvfix]; exact hv),
        R.after_selected w (by change R.selected (R.forest.root w); rw [hwfix]; exact hw)]
  · right
    have hvafter : R.after.root v = v := (R.after_outside v (by change ¬ R.selected (R.forest.root v); rwa [hvfix])).trans hvfix
    rw [hvafter]
    exact R.after_edge_target he

/-- Every actual old root path survives a recorded contraction. The new path
contains exactly the new roots of its original vertices; no disjointness is
asserted, since contracting distinct old paths may make them meet. -/
theorem transport_path (R : PetalRecord M)
    (p : DDFS.Path (predecessorGraph R.prior R.forest R.invariant))
    (hfix : ∀ v, p.Contains v → R.forest.root v = v) :
    ∃ q : DDFS.Path (predecessorGraph R.prior R.after R.after_invariant),
      q.first = R.after.root p.first ∧ q.last = R.after.root p.last ∧
      q.length ≤ p.length ∧
      ∀ w, q.Contains w ↔ ∃ v, p.Contains v ∧ R.after.root v = w := by
  exact p.map_eq_or_edge R.after.root (fun v w he hv _ => R.after_edge_eq_or_edge he (hfix v hv))

end MaximumMatching.Search.PetalRecord
