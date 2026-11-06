import MaximumMatching.MatchingDDFSBud
import MaximumMatching.BudLinkExact

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
