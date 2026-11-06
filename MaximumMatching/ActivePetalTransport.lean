import MaximumMatching.ActivePetalPaths
import MaximumMatching.AugmentingPathArms

/-! A live petal contraction preserves bottom paths and their original-vertex
containment. Its region closure is used only in the restricted live graph. -/
namespace MaximumMatching.Search.ActivePetalRecord
variable {n i cut : Nat} {G : Graph (Fin n)} {M : Matching G}

abbrev afterGraph (R : ActivePetalRecord M i cut) :=
  DDFS.RecursiveRemoval.restricted
    (predecessorGraph R.prior R.after R.after_invariant) R.afterLive

theorem after_root_old_root (R : ActivePetalRecord M i cut) (v : Fin n) :
    R.after.root (R.forest.root v) = R.after.root v :=
  R.forest.mergeManyInto_root_congr _ _ _ _ (R.forest.root_idempotent v)

/-- The target of an old predecessor edge becomes its new bud root. -/
theorem after_edge_target (R : ActivePetalRecord M i cut) {v w : Fin n}
    (he : (predecessorGraph R.prior R.forest R.invariant).Edge v w) :
    (predecessorGraph R.prior R.after R.after_invariant).Edge v (R.after.root w) := by
  obtain ⟨u, hu, huw⟩ := List.mem_map.mp he.2
  refine ⟨he.1, List.mem_map.mpr ⟨u, hu, ?_⟩⟩
  exact R.forest.mergeManyInto_root_congr _ _ u w
    (by rw [← huw]; exact (R.forest.root_idempotent u).symm)

/-- Each old live edge collapses or survives as an actual new live edge. -/
theorem after_edge_eq_or_edge (R : ActivePetalRecord M i cut) {v w : Fin n}
    (he : R.graph.Edge v w) :
    R.after.root v = R.after.root w ∨ R.afterGraph.Edge (R.after.root v) (R.after.root w) := by
  have hvfix := R.input.live_fixed v he.1
  have hwfix := R.input.live_fixed w he.2.1
  by_cases hv : R.selected v
  · by_cases hvb : v = R.bottleneck
    · right
      refine ⟨R.after_root_live v he.1, R.after_root_live w he.2.1, ?_⟩
      have hvafter : R.after.root v = v := by
        rw [R.after_selected v (by change R.selected (R.forest.root v); rw [hvfix]; exact hv)]
        exact hvb.symm
      rw [hvafter]
      exact R.after_edge_target he.2.2
    · left
      have hw := R.selected_edge_closed hv hvb he
      rw [R.after_selected v (by change R.selected (R.forest.root v); rw [hvfix]; exact hv),
        R.after_selected w (by change R.selected (R.forest.root w); rw [hwfix]; exact hw)]
  · right
    refine ⟨R.after_root_live v he.1, R.after_root_live w he.2.1, ?_⟩
    have hvafter : R.after.root v = v :=
      (R.after_outside v (by change ¬R.selected (R.forest.root v); rwa [hvfix])).trans hvfix
    rw [hvafter]
    exact R.after_edge_target he.2.2

theorem transport_path (R : ActivePetalRecord M i cut) (p : DDFS.Path R.graph) :
    ∃ q : DDFS.Path R.afterGraph,
      q.first = R.after.root p.first ∧ q.last = R.after.root p.last ∧ q.length ≤ p.length ∧
      ∀ w, q.Contains w ↔ ∃ v, p.Contains v ∧ R.after.root v = w := by
  exact p.map_eq_or_edge R.after.root (fun _ _ he _ _ => R.after_edge_eq_or_edge he)

/-- A path reaching bottom after entering the selected region passes through
its bottleneck, including when its endpoint is that bottleneck. -/
theorem selected_bottom_path_contains_bottleneck (R : ActivePetalRecord M i cut)
    (p : DDFS.Path R.graph) (v : Fin n) (hv : p.Contains v) (hsel : R.selected v)
    (hbottom : R.graph.level p.last = 0) : p.Contains R.bottleneck := by
  apply Classical.byContradiction
  intro havoid
  obtain ⟨j, hj⟩ := hv
  let q := p.drop j.val (by omega)
  have hqf : R.selected q.first := by rw [p.drop_first, hj]; exact hsel
  have hqavoid : ¬q.Contains R.bottleneck := fun hb => havoid (p.contains_drop _ _ hb)
  have hall := q.stays_in_closed_except R.selected R.bottleneck
    (fun _ _ hw hne he => R.selected_edge_closed hw hne he) hqf hqavoid
  have hslast : R.selected p.last := by
    have hh := hall ⟨q.length, by omega⟩
    change R.selected q.last at hh
    rwa [p.drop_last] at hh
  have hne : p.last ≠ R.bottleneck := fun he => havoid (he ▸ p.contains_last)
  have hh := DDFS.onRootTo_level_gt ((R.region p.last).1 hslast) hne
  rw [hbottom] at hh
  omega

theorem after_root_on_bottom_path (R : ActivePetalRecord M i cut)
    (p : DDFS.Path R.graph) (hfix : ∀ v, p.Contains v → R.forest.root v = v)
    (hb : R.graph.level p.last = 0) (v : Fin n) (hv : p.Contains v) :
    p.Contains (R.after.root v) := by
  have hf := hfix v hv
  by_cases hs : R.selected v
  · rw [R.after_selected v (by change R.selected (R.forest.root v); rwa [hf])]
    exact R.selected_bottom_path_contains_bottleneck p v hv hs hb
  · rw [R.after_outside v (by change ¬R.selected (R.forest.root v); rwa [hf]), hf]
    exact hv

theorem after_bottom_fixed (R : ActivePetalRecord M i cut) (v : Fin n)
    (hfix : R.forest.root v = v) (hb : R.graph.level v = 0) : R.after.root v = v := by
  by_cases hs : R.selected v
  · have he : v = R.bottleneck := by
      by_cases he : v = R.bottleneck
      · exact he
      · have hh := DDFS.onRootTo_level_gt ((R.region v).1 hs) he
        rw [hb] at hh
        omega
    exact (R.after_selected v (by change R.selected (R.forest.root v); rwa [hfix])).trans he.symm
  · exact (R.after_outside v (by change ¬R.selected (R.forest.root v); rwa [hfix])).trans hfix

theorem after_bottom (R : ActivePetalRecord M i cut) (v : Fin n)
    (hb : R.graph.level v = 0) : R.afterGraph.level v = 0 := by
  by_cases hv : v ∈ R.afterLive
  · have hold := ((R.mem_afterLive v).1 hv).1
    change (if v ∈ R.afterLive then (R.prior.minLabel v).getD 0 else 0) = 0
    rw [ite_eq_left hv]
    exact (R.input.level_live v hold).symm.trans hb
  · change (if v ∈ R.afterLive then _ else 0) = 0
    exact ite_eq_right hv

/-- Contraction adds no original vertex to a bottom path. -/
theorem transport_bottom_path (R : ActivePetalRecord M i cut)
    (p : DDFS.Path R.graph) (hfix : ∀ v, p.Contains v → R.forest.root v = v)
    (hb : R.graph.level p.last = 0) :
    ∃ q : DDFS.Path R.afterGraph,
      q.first = R.after.root p.first ∧ q.last = p.last ∧ R.afterGraph.level q.last = 0 ∧
      ∀ v, q.Contains v → p.Contains v := by
  obtain ⟨q, hqf, hql, _, hqv⟩ := R.transport_path p
  have hlast : q.last = p.last := hql.trans (R.after_bottom_fixed p.last (hfix _ p.contains_last) hb)
  refine ⟨q, hqf, hlast, ?_, ?_⟩
  · rw [hlast]
    exact R.after_bottom p.last hb
  · intro v hv
    obtain ⟨u, hu, huv⟩ := (hqv v).1 hv
    rw [← huv]
    exact R.after_root_on_bottom_path p hfix hb u hu

/-- Every surviving root still reaches a genuine live bottom. Isolated
removed roots retain the restricted graph's conventional zero level. -/
theorem after_reach (R : ActivePetalRecord M i cut) : DDFS.ReachBottom R.afterGraph := by
  intro v
  by_cases hv : v ∈ R.afterLive
  · have hvlive := ((R.mem_afterLive v).1 hv).1
    obtain ⟨p, hpf, hpb⟩ := R.input.reach v
    have hfix : ∀ w, p.Contains w → R.forest.root w = w := by
      intro w hw
      exact R.input.live_fixed w (R.input.path_live p (hpf ▸ hvlive) w hw)
    obtain ⟨q, hqf, _, hqb, _⟩ := R.transport_bottom_path p hfix hpb
    exact ⟨q, hqf.trans ((congrArg R.after.root hpf).trans ((R.mem_afterLive v).1 hv).2), hqb⟩
  · refine ⟨DDFS.Path.trivial R.afterGraph v, rfl, ?_⟩
    change (if v ∈ R.afterLive then _ else 0) = 0
    exact ite_eq_right hv

/-- Vertex-contained disjoint bottom arms remain vertex-contained and
separate after a live petal contraction. -/
theorem transport_bottom_bridge_arms (R : ActivePetalRecord M i cut)
    {u v : Fin n} {Q : Fin n → Prop}
    (ha : BottomBridgeArms R.graph R.forest u v Q) :
    BottomBridgeArms R.afterGraph R.after u v Q := by
  obtain ⟨p, q, hp, hq, hd, hpQ, hqQ⟩ := ha
  have hpf : R.forest.parent (R.input.liftPath p).first = (R.input.liftPath p).first := by
    change R.forest.parent p.first = p.first
    rw [hp.1]
    exact R.forest.root_fixed u
  have hqf : R.forest.parent (R.input.liftPath q).first = (R.input.liftPath q).first := by
    change R.forest.parent q.first = q.first
    rw [hq.1]
    exact R.forest.root_fixed v
  have hpfix : ∀ x, p.Contains x → R.forest.root x = x := by
    rintro x ⟨j, rfl⟩
    exact R.forest.root_of_fixed _ (R.invariant.path_fixed (R.input.liftPath p) hpf j)
  have hqfix : ∀ x, q.Contains x → R.forest.root x = x := by
    rintro x ⟨j, rfl⟩
    exact R.forest.root_of_fixed _ (R.invariant.path_fixed (R.input.liftPath q) hqf j)
  obtain ⟨a, haf, _, hab, hav⟩ := R.transport_bottom_path p hpfix hp.2
  obtain ⟨b, hbf, _, hbb, hbv⟩ := R.transport_bottom_path q hqfix hq.2
  refine ⟨a, b, ⟨?_, hab⟩, ⟨?_, hbb⟩, ?_, ?_, ?_⟩
  · exact haf.trans ((congrArg R.after.root hp.1).trans (R.after_root_old_root u))
  · exact hbf.trans ((congrArg R.after.root hq.1).trans (R.after_root_old_root v))
  · exact fun w ha hb => hd w (hav w ha) (hbv w hb)
  · exact fun w hw => hpQ w (hav w hw)
  · exact fun w hw => hqQ w (hbv w hw)

end MaximumMatching.Search.ActivePetalRecord
