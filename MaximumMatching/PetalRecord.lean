import MaximumMatching.BudForest
import MaximumMatching.MatchingGraphExpansion
import MaximumMatching.MatchingSearchGraph

section PetalRecord

/-! Operational petal records from actual queued bridge searches. Every record
retains the prior forest, its original fibers, and the computed colored trees.
Newly attached fibers exclude the old bottleneck class. These sets are not
identified with whole mathematical blossoms or semantic bridge supports. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)}

/-- A snapshot of a real bottleneck event, including the original trigger and
the exact prior state needed to interpret its tree edges and bud fibers. -/
structure PetalRecord (M : Matching G) where
  cap : Nat
  prior : State (Fin n)
  forest : BudForest (Fin n)
  invariant : BudGraphInvariant M cap prior forest
  queueSound : BucketsSound M prior
  tenacity : Nat
  left : Fin n
  right : Fin n
  queued : (left, right) ∈ prior.bucket tenacity
  known : edgeTenacity M prior left right = some tenacity
  different : forest.root left ≠ forest.root right
  bottleneck : Fin n
  selected : Fin n → Prop
  trees : DDFS.ColoredTrees (predecessorGraph prior forest invariant) selected
    (forest.root left) (forest.root right) bottleneck
  highest : DDFS.HighestBottleneck (predecessorGraph prior forest invariant)
    (forest.root left) (forest.root right) bottleneck
  region : ∀ v, selected v ↔ DDFS.OnRootTo (H := predecessorGraph prior forest invariant)
    (forest.root left) (forest.root right) bottleneck v
  computed : DDFS.Machine.executeFull invariant.reachBottom (forest.root left) (forest.root right) =
    .bottleneck bottleneck selected trees highest region

variable {M : Matching G}

/-- Run the actual queued bridge search and retain a record exactly when it
reports a nontrivial bottleneck. Equal current roots are skipped explicitly. -/
def recordQueuedPetal {cap : Nat} {s : State (Fin n)} {F : BudForest (Fin n)}
    (h : BudGraphInvariant M cap s F) (hq : BucketsSound M s) (t : Nat) (u v : Fin n)
    (hqueued : (u, v) ∈ s.bucket t) (hknown : edgeTenacity M s u v = some t) :
    Option (PetalRecord M) :=
  if he : F.root u = F.root v then none else
    match hout : DDFS.Machine.executeFull h.reachBottom (F.root u) (F.root v) with
    | .disjoint _ _ _ _ _ => none
    | .bottleneck b S trees highest region => some {
        cap := cap, prior := s, forest := F, invariant := h, queueSound := hq,
        tenacity := t, left := u, right := v, queued := hqueued, known := hknown,
        different := he, bottleneck := b, selected := S, trees := trees,
        highest := highest, region := region, computed := hout }

theorem recordQueuedPetal_same_root {cap : Nat} {s : State (Fin n)} {F : BudForest (Fin n)}
    (h : BudGraphInvariant M cap s F) (hq : BucketsSound M s) (t : Nat) (u v : Fin n)
    (hqueued : (u, v) ∈ s.bucket t) (hknown : edgeTenacity M s u v = some t)
    (he : F.root u = F.root v) : recordQueuedPetal h hq t u v hqueued hknown = none := by
  simp only [recordQueuedPetal, dite_eq_left he]

/-- A returned record is tied to the exact input state, old forest, and
queued trigger, rather than merely carrying an unrelated valid certificate. -/
theorem recordQueuedPetal_origin {cap : Nat} {s : State (Fin n)} {F : BudForest (Fin n)}
    (h : BudGraphInvariant M cap s F) (hq : BucketsSound M s) (t : Nat) (u v : Fin n)
    (hqueued : (u, v) ∈ s.bucket t) (hknown : edgeTenacity M s u v = some t)
    (R : PetalRecord M) (hR : recordQueuedPetal h hq t u v hqueued hknown = some R) :
    R.cap = cap ∧ R.prior = s ∧ R.forest = F ∧ R.tenacity = t ∧ R.left = u ∧ R.right = v := by
  unfold recordQueuedPetal at hR
  split at hR
  · contradiction
  · split at hR
    · contradiction
    · have he := Option.some.inj hR
      rw [← he]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

namespace PetalRecord

theorem trigger (R : PetalRecord M) :
    Bridge M R.left R.right ∧ MaximumMatching.edgeTenacity M R.left R.right = some R.tenacity :=
  R.queueSound R.tenacity R.left R.right R.queued

theorem starts_assigned (R : PetalRecord M) :
    (∃ k, R.prior.minLabel R.left = some k) ∧ (∃ k, R.prior.minLabel R.right = some k) :=
  edgeTenacity_has_minLabels R.prior R.left R.right R.tenacity R.known

/-- The original fiber map is retained, before any new pointer is installed. -/
def selectedFiber (R : PetalRecord M) (v : Fin n) : Prop := R.selected (R.forest.root v)

/-- Newly attached fibers omit the bottleneck's already-existing class. -/
def newFiber (R : PetalRecord M) (v : Fin n) : Prop :=
  R.selectedFiber v ∧ R.forest.root v ≠ R.bottleneck

/-- The actual output forest, computed from the recorded selected-root list. -/
def after (R : PetalRecord M) : BudForest (Fin n) :=
  R.forest.mergeManyInto R.trees.vertices R.bottleneck

theorem selected_fixed (R : PetalRecord M) (v : Fin n) (hv : R.selected v) :
    R.forest.parent v = v :=
  DDFS.onRootTo_fixed_root R.forest (fun _ _ he => R.invariant.edge_target_fixed he)
    (R.forest.root R.left) (R.forest.root R.right) R.bottleneck v
    (R.forest.root_fixed R.left) (R.forest.root_fixed R.right) ((R.region v).1 hv)

theorem selected_assigned (R : PetalRecord M) :
    (∃ k, R.prior.minLabel R.bottleneck = some k) ∧
      ∀ v, R.selected v → (∃ k, R.prior.minLabel v = some k) := by
  have hh := executeBudSearch_vertices R.invariant R.left R.right R.starts_assigned.1 R.starts_assigned.2
  simp only [executeBudSearch, DDFS.Machine.executeAndContract] at hh
  rw [R.computed] at hh
  exact ⟨hh.1, fun v hv => (hh.2 v hv).1⟩

theorem after_invariant (R : PetalRecord M) : BudGraphInvariant M R.cap R.prior R.after := by
  have hh := executeBudSearch_preserves R.invariant R.left R.right R.starts_assigned.1 R.starts_assigned.2
  change BudGraphInvariant M R.cap R.prior
    ((DDFS.Machine.executeFull R.invariant.reachBottom
      (R.forest.root R.left) (R.forest.root R.right)).contract R.forest) at hh
  rw [R.computed] at hh
  exact hh

theorem guards (R : PetalRecord M) (x : Fin n) (hx : x ∈ R.trees.vertices) :
    R.forest.rank (R.forest.root R.bottleneck) < R.forest.rank (R.forest.root x) ∨
      R.forest.root x = R.forest.root R.bottleneck := by
  have hxb := R.selected_fixed x ((R.trees.mem_vertices x).1 hx)
  have hb := R.selected_fixed R.bottleneck R.trees.bottleneck_mem
  rw [R.forest.root_of_fixed x hxb, R.forest.root_of_fixed R.bottleneck hb]
  by_cases he : x = R.bottleneck
  · exact Or.inr he
  · apply Or.inl
    rw [R.invariant.rankLabel, R.invariant.rankLabel]
    exact DDFS.onRootTo_level_gt ((R.region x).1 ((R.trees.mem_vertices x).1 hx)) he

/-- Exact new roots are determined by the old root's membership in the actual
computed list; no other old class is silently absorbed. -/
theorem after_root (R : PetalRecord M) (v : Fin n) :
    R.after.root v = if R.forest.root v ∈ R.trees.vertices then R.bottleneck else R.forest.root v := by
  have hb := R.forest.root_of_fixed R.bottleneck
    (R.selected_fixed R.bottleneck R.trees.bottleneck_mem)
  have hmem : R.forest.root v ∈ R.trees.vertices.map R.forest.root ↔
      R.forest.root v ∈ R.trees.vertices := by
    constructor
    · rintro hm
      obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
      have hr := R.forest.root_of_fixed x (R.selected_fixed x ((R.trees.mem_vertices x).1 hx))
      rw [hr] at he
      exact he ▸ hx
    · intro hv
      exact List.mem_map.mpr ⟨R.forest.root v, hv, R.forest.root_idempotent v⟩
  change (R.forest.mergeManyInto R.trees.vertices R.bottleneck).root v = _
  rw [R.forest.mergeManyInto_root_exact R.trees.vertices R.bottleneck v R.guards, hb]
  simp only [hmem]

theorem after_selected (R : PetalRecord M) (v : Fin n) (hv : R.selectedFiber v) :
    R.after.root v = R.bottleneck := by
  rw [R.after_root, ite_eq_left ((R.trees.mem_vertices _).2 hv)]

theorem after_outside (R : PetalRecord M) (v : Fin n) (hv : ¬R.selectedFiber v) :
    R.after.root v = R.forest.root v := by
  rw [R.after_root, ite_eq_right (fun hm => hv ((R.trees.mem_vertices _).1 hm))]

/-- The computed colors lift to exactly the newly attached old fibers. -/
theorem newFiber_iff_color (R : PetalRecord M) (v : Fin n) :
    R.newFiber v ↔ ∃ c, R.trees.color (R.forest.root v) = some c :=
  (R.trees.domain (R.forest.root v)).symm

/-- Each stored tree edge retains an original MIN predecessor witness and
its prior bud map, so future expansion need not treat a petal as a blossom. -/
theorem red_edge_witness (R : PetalRecord M) (v w : Fin n)
    (he : R.trees.red.parent w = some v) :
    ∃ u k j, R.prior.minLabel v = some k ∧ R.prior.minLabel u = some j ∧
      Predecessor M u v ∧ R.forest.root u = w ∧ j < k :=
  R.invariant.edge_witness (R.trees.red.edge v w he).2.2

theorem green_edge_witness (R : PetalRecord M) (v w : Fin n)
    (he : R.trees.green.parent w = some v) :
    ∃ u k j, R.prior.minLabel v = some k ∧ R.prior.minLabel u = some j ∧
      Predecessor M u v ∧ R.forest.root u = w ∧ j < k :=
  R.invariant.edge_witness (R.trees.green.edge v w he).2.2

end PetalRecord
end MaximumMatching.Search

end PetalRecord

section PetalRootExpansion

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

end PetalRootExpansion
