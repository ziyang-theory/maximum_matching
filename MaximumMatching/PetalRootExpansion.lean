import MaximumMatching.MatchingFiberExpansion
import MaximumMatching.PetalRecord

namespace MaximumMatching.DDFS
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

/-- The fixed-root restriction is only for path expansion; it does not alter
the concrete DDFS graph or its execution. -/
def fixedRootGraph (H : LayeredGraph V) (F : BudForest V) : LayeredGraph V where
  Edge u v := H.Edge u v ∧ F.root u = u ∧ F.root v = v
  level := H.level
  decreases h := H.decreases h.1

def Path.restrictRoots {H : LayeredGraph V} (p : Path H) (F : BudForest V)
    (h : ∀ v, p.Contains v → F.root v = v) : Path (fixedRootGraph H F) where
  length := p.length
  vertex := p.vertex
  adjacent i := ⟨p.adjacent i, h _ ⟨⟨i.val, by omega⟩, rfl⟩,
    h _ ⟨⟨i.val + 1, by omega⟩, rfl⟩⟩

noncomputable def FiberWeightedMatching.restrictRoots {H : LayeredGraph V} {F : BudForest V}
    (W : FiberWeightedMatching M H F) : FiberWeightedMatching M (fixedRootGraph H F) F where
  phase := W.phase
  segment he := W.segment he.1
  first he := W.first he.1
  last he := W.last he.1
  start_phase he := W.start_phase he.1
  end_phase he := W.end_phase he.1
  interior he := W.interior he.1

end MaximumMatching.DDFS

namespace MaximumMatching.Search.PetalRecord
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

/-- A surviving root was already a root before the actual petal merge. -/
theorem after_fixed_before (R : PetalRecord M) (v : Fin n)
    (hv : R.after.root v = v) : R.forest.root v = v := by
  have he := R.after_root v
  split at he
  · have hvb : v = R.bottleneck := hv.symm.trans he
    rw [hvb]
    exact R.forest.root_of_fixed _ (R.selected_fixed _ R.trees.bottleneck_mem)
  · exact he.symm.trans hv

/-- Every selected root has an actual old graph path to the bottleneck,
with every vertex still in the recorded selected region. -/
theorem selected_tail (R : PetalRecord M) (v : Fin n) (hv : R.selected v) :
    ∃ q : DDFS.Path (predecessorGraph R.prior R.forest R.invariant),
      q.first = v ∧ q.last = R.bottleneck ∧ ∀ w, q.Contains w → R.selected w := by
  obtain ⟨p, hp, hpb, i, hi⟩ := (R.region v).1 hv
  refine ⟨p.drop i.val (by omega), (p.drop_first _ _).trans hi,
    (p.drop_last _ _).trans hpb, ?_⟩
  intro w hw
  obtain ⟨j, hj⟩ := p.contains_drop _ _ hw
  exact (R.region w).2 ⟨p, hp, hpb, j, hj⟩

/-- Expand the new root of an old fiber by an actual descending old path.
Each old root on this path acquires exactly that same new root. -/
theorem tail_to_after_root (R : PetalRecord M) (v : Fin n) :
    ∃ q : DDFS.Path (predecessorGraph R.prior R.forest R.invariant),
      q.first = R.forest.root v ∧ q.last = R.after.root v ∧
      (∀ w, q.Contains w → R.forest.root w = w) ∧
      (∀ w, q.Contains w → R.after.root w = R.after.root v) := by
  by_cases hv : R.selected (R.forest.root v)
  · obtain ⟨q, hqf, hql, hqS⟩ := R.selected_tail (R.forest.root v) hv
    have hav := R.after_selected v hv
    refine ⟨q, hqf, hql.trans hav.symm, ?_, ?_⟩
    · intro w hw
      exact R.forest.root_of_fixed w (R.selected_fixed w (hqS w hw))
    · intro w hw
      rw [hav]
      apply R.after_selected
      change R.selected (R.forest.root w)
      rw [R.forest.root_of_fixed w (R.selected_fixed w (hqS w hw))]
      exact hqS w hw
  · have hav := R.after_outside v hv
    refine ⟨DDFS.Path.trivial _ (R.forest.root v), rfl, hav.symm, ?_, ?_⟩
    · rintro w ⟨i, hi⟩
      change R.forest.root v = w at hi
      rw [← hi]
      exact R.forest.root_idempotent v
    · rintro w ⟨i, hi⟩
      change R.forest.root v = w at hi
      rw [← hi]
      exact R.forest.mergeManyInto_root_congr R.trees.vertices R.bottleneck _ _
        (R.forest.root_idempotent v)

/-- A new fixed-root edge is an actual old root path. All positions after
its start lie in old classes merged into its new target. -/
theorem lift_after_edge (R : PetalRecord M) {v w : Fin n}
    (he : (DDFS.fixedRootGraph (predecessorGraph R.prior R.after R.after_invariant) R.after).Edge v w) :
    ∃ p : DDFS.Path (DDFS.fixedRootGraph (predecessorGraph R.prior R.forest R.invariant) R.forest),
      p.first = v ∧ p.last = w ∧
      (∀ z, p.Contains z → R.forest.root z = z) ∧
      (∀ j : Fin (p.length + 1), 0 < j.val → R.after.root (p.vertex j) = w) := by
  obtain ⟨u, hu, huw⟩ := List.mem_map.mp he.1.2
  obtain ⟨q, hqf, hql, hqfix, hqafter⟩ := R.tail_to_after_root u
  have hedge : (predecessorGraph R.prior R.forest R.invariant).Edge v q.first := by
    rw [hqf]
    exact ⟨he.1.1, List.mem_map.mpr ⟨u, hu, rfl⟩⟩
  let p := q.prepend v hedge
  have hpf : ∀ z, p.Contains z → R.forest.root z = z := by
    intro z hz
    rcases (q.contains_prepend_iff v hedge z).1 hz with rfl | hz
    · exact R.after_fixed_before z he.2.1
    · exact hqfix z hz
  refine ⟨p.restrictRoots R.forest hpf, rfl,
    (q.prepend_last v hedge).trans (hql.trans huw), hpf, ?_⟩
  intro j hj
  have hcontains : q.Contains (p.vertex j) := by
    refine ⟨⟨j.val - 1, by have := j.isLt; change j.val < q.length + 1 + 1 at this; omega⟩, ?_⟩
    change q.vertex ⟨j.val - 1, _⟩ = if h : j.val = 0 then v else q.vertex ⟨j.val - 1, _⟩
    rw [dite_eq_right (by omega)]
  exact (hqafter (p.vertex j) hcontains).trans huw

/-- Construct an actual new edge segment by expanding its old root path.
Every strict interior vertex is proved to enter the new target fiber. -/
theorem after_edge_expansion (R : PetalRecord M)
    (W : DDFS.FiberWeightedMatching M
      (DDFS.fixedRootGraph (predecessorGraph R.prior R.forest R.invariant) R.forest) R.forest)
    (hphase : ∀ v, W.phase v % 2 = ((R.prior.minLabel v).getD 0 + 1) % 2)
    (hdrop : ∀ {u v} (he : (DDFS.fixedRootGraph
      (predecessorGraph R.prior R.forest R.invariant) R.forest).Edge u v),
      (W.segment he).length + (R.prior.minLabel v).getD 0 = (R.prior.minLabel u).getD 0)
    {v w : Fin n}
    (he : (DDFS.fixedRootGraph (predecessorGraph R.prior R.after R.after_invariant) R.after).Edge v w) :
    ∃ a : ParitySegment M, a.first = v ∧ a.last = w ∧
      a.length + (R.prior.minLabel w).getD 0 = (R.prior.minLabel v).getD 0 ∧
      a.phase % 2 = ((R.prior.minLabel v).getD 0 + 1) % 2 ∧
      (a.phase + a.length) % 2 = ((R.prior.minLabel w).getD 0 + 1) % 2 ∧
      (∀ j : Fin (a.length + 1), 0 < j.val → j.val < a.length →
        R.after.root (a.vertex j) = w) := by
  obtain ⟨p, hpf, hpl, hpfix, hpafter⟩ := R.lift_after_edge he
  obtain ⟨a, haf, hal, han, hap, hae, hah, haavoid⟩ := W.realize p hpfix
  have hweight := W.weight_add_potential (fun x => (R.prior.minLabel x).getD 0) hdrop p
  refine ⟨a, haf.trans hpf, hal.trans hpl, ?_, ?_, ?_, ?_⟩
  · rw [hpf, hpl, ← han] at hweight
    exact hweight
  · exact hap.trans ((hphase p.first).trans (by rw [hpf]))
  · exact hae.trans ((hphase p.last).trans (by rw [hpl]))
  · intro j hj _
    obtain ⟨k, hk⟩ := hah (a.vertex j) ⟨j, rfl⟩
    have hkpos : 0 < k.val := by
      by_cases hk0 : k.val = 0
      · have hkf : R.forest.root (a.vertex j) = p.first := by
          have hkeq : k = ⟨0, by omega⟩ := Fin.ext hk0
          exact hk.symm.trans (congrArg p.vertex hkeq)
        have haj : a.vertex j = a.first := (haavoid (a.vertex j) ⟨j, rfl⟩ hkf).trans haf.symm
        have hjeq := congrArg Fin.val (a.injective j ⟨0, by omega⟩ haj)
        dsimp only at hjeq
        omega
      · omega
    have heq : R.after.root (a.vertex j) = R.after.root (R.forest.root (a.vertex j)) :=
      R.forest.mergeManyInto_root_congr R.trees.vertices R.bottleneck _ _
        (R.forest.root_idempotent (a.vertex j)).symm
    rw [← hk] at heq
    exact heq.trans (hpafter k hkpos)

/-- Preserve the root-edge path representation through the actual petal
merge. Segments are constructed from the previous witnesses and recorded
selected tails; no path or support postcondition is assumed for the result. -/
noncomputable def afterWeightedMatching (R : PetalRecord M)
    (W : DDFS.FiberWeightedMatching M
      (DDFS.fixedRootGraph (predecessorGraph R.prior R.forest R.invariant) R.forest) R.forest)
    (hphase : ∀ v, W.phase v % 2 = ((R.prior.minLabel v).getD 0 + 1) % 2)
    (hdrop : ∀ {u v} (he : (DDFS.fixedRootGraph
      (predecessorGraph R.prior R.forest R.invariant) R.forest).Edge u v),
      (W.segment he).length + (R.prior.minLabel v).getD 0 = (R.prior.minLabel u).getD 0) :
    DDFS.FiberWeightedMatching M
      (DDFS.fixedRootGraph (predecessorGraph R.prior R.after R.after_invariant) R.after) R.after where
  phase v := (R.prior.minLabel v).getD 0 + 1
  segment he := Classical.choose (R.after_edge_expansion W hphase hdrop he)
  first he := (Classical.choose_spec (R.after_edge_expansion W hphase hdrop he)).1
  last he := (Classical.choose_spec (R.after_edge_expansion W hphase hdrop he)).2.1
  start_phase he := (Classical.choose_spec (R.after_edge_expansion W hphase hdrop he)).2.2.2.1
  end_phase he := (Classical.choose_spec (R.after_edge_expansion W hphase hdrop he)).2.2.2.2.1
  interior he := (Classical.choose_spec (R.after_edge_expansion W hphase hdrop he)).2.2.2.2.2

theorem afterWeightedMatching_drop (R : PetalRecord M)
    (W : DDFS.FiberWeightedMatching M
      (DDFS.fixedRootGraph (predecessorGraph R.prior R.forest R.invariant) R.forest) R.forest)
    (hphase : ∀ v, W.phase v % 2 = ((R.prior.minLabel v).getD 0 + 1) % 2)
    (hdrop : ∀ {u v} (he : (DDFS.fixedRootGraph
      (predecessorGraph R.prior R.forest R.invariant) R.forest).Edge u v),
      (W.segment he).length + (R.prior.minLabel v).getD 0 = (R.prior.minLabel u).getD 0)
    {v w : Fin n}
    (he : (DDFS.fixedRootGraph (predecessorGraph R.prior R.after R.after_invariant) R.after).Edge v w) :
    ((R.afterWeightedMatching W hphase hdrop).segment he).length +
      (R.prior.minLabel w).getD 0 = (R.prior.minLabel v).getD 0 :=
  (Classical.choose_spec (R.after_edge_expansion W hphase hdrop he)).2.2.1

/-- Preserve any existing endpoint-to-root arm through the actual merge.
Its original endpoint phase and its endpoint-level budget are unchanged.
This applies independently to either parity arm whenever it is already known. -/
theorem after_arm_expansion (R : PetalRecord M)
    (W : DDFS.FiberWeightedMatching M
      (DDFS.fixedRootGraph (predecessorGraph R.prior R.forest R.invariant) R.forest) R.forest)
    (hphase : ∀ v, W.phase v % 2 = ((R.prior.minLabel v).getD 0 + 1) % 2)
    (hdrop : ∀ {u v} (he : (DDFS.fixedRootGraph
      (predecessorGraph R.prior R.forest R.invariant) R.forest).Edge u v),
      (W.segment he).length + (R.prior.minLabel v).getD 0 = (R.prior.minLabel u).getD 0)
    (v : Fin n) (a : ParitySegment M) (haf : a.first = v) (hal : a.last = R.forest.root v)
    (hae : (a.phase + a.length) % 2 = ((R.prior.minLabel (R.forest.root v)).getD 0 + 1) % 2)
    (hai : ∀ j : Fin (a.length + 1), j.val < a.length →
      R.forest.root (a.vertex j) = R.forest.root v) :
    ∃ c : ParitySegment M, c.first = v ∧ c.last = R.after.root v ∧
      c.length + (R.prior.minLabel (R.after.root v)).getD 0 =
        a.length + (R.prior.minLabel (R.forest.root v)).getD 0 ∧
      c.phase = a.phase ∧
      (c.phase + c.length) % 2 = ((R.prior.minLabel (R.after.root v)).getD 0 + 1) % 2 ∧
      (∀ j : Fin (c.length + 1), R.after.root (c.vertex j) = R.after.root v) := by
  obtain ⟨q, hqf, hql, hqfix, hqafter⟩ := R.tail_to_after_root v
  let p := q.restrictRoots R.forest hqfix
  have hpf : p.first = R.forest.root v := hqf
  have hpl : p.last = R.after.root v := hql
  have hfixed : ∀ z, p.Contains z → R.forest.root z = z := hqfix
  have hap : (a.phase + a.length) % 2 = W.phase p.first % 2 := by
    rw [hphase, hpf]
    exact hae
  obtain ⟨c, hcf, hcl, hcn, hcp, hce, hch⟩ := W.realize_with_start p hfixed a
    (hal.trans hpf.symm) hap (by rw [hpf]; exact hai)
  have hw := W.weight_add_potential (fun x => (R.prior.minLabel x).getD 0) hdrop p
  rw [hpf, hpl] at hw
  refine ⟨c, hcf.trans haf, hcl.trans hpl, by omega, hcp, ?_, ?_⟩
  · exact hce.trans ((hphase p.last).trans (by rw [hpl]))
  · intro j
    have hh := hch (c.vertex j) ⟨j, rfl⟩
    have hh' : q.Contains (R.forest.root (c.vertex j)) := hh
    have he : R.after.root (c.vertex j) = R.after.root (R.forest.root (c.vertex j)) :=
      R.forest.mergeManyInto_root_congr R.trees.vertices R.bottleneck _ _
        (R.forest.root_idempotent (c.vertex j)).symm
    exact he.trans (hqafter _ hh')

end MaximumMatching.Search.PetalRecord
