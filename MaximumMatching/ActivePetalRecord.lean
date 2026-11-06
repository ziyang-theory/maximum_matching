import MaximumMatching.ActiveSearchGraph

/-! Records of actual DDFS bottleneck events on the live graph. Their highest
bottleneck and region certificates refer to that restricted graph, never to
paths through vertices deleted by earlier augmentations. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)}

structure ActivePetalRecord (M : Matching G) (i cut : Nat) where
  input : ActiveSearchState M i cut
  left : Fin n
  right : Fin n
  queued : (left, right) ∈ input.B.state.bucket (2 * i + 1)
  left_live : input.B.forest.root left ∈ input.live
  right_live : input.B.forest.root right ∈ input.live
  different : input.B.forest.root left ≠ input.B.forest.root right
  bottleneck : Fin n
  selected : Fin n → Prop
  trees : DDFS.ColoredTrees input.graph selected
    (input.B.forest.root left) (input.B.forest.root right) bottleneck
  highest : DDFS.HighestBottleneck input.graph
    (input.B.forest.root left) (input.B.forest.root right) bottleneck
  region : ∀ v, selected v ↔ DDFS.OnRootTo (H := input.graph)
    (input.B.forest.root left) (input.B.forest.root right) bottleneck v
  computed : DDFS.Machine.executeFull input.reach (input.B.forest.root left) (input.B.forest.root right) =
    .bottleneck bottleneck selected trees highest region

namespace ActivePetalRecord
variable {M : Matching G} {i cut : Nat}

abbrev prior (R : ActivePetalRecord M i cut) := R.input.B.state
abbrev forest (R : ActivePetalRecord M i cut) := R.input.B.forest
abbrev invariant (R : ActivePetalRecord M i cut) := R.input.B.bud
abbrev graph (R : ActivePetalRecord M i cut) := R.input.graph

/-- The actual merge uses the selected roots computed in the live run. -/
def after (R : ActivePetalRecord M i cut) : BudForest (Fin n) :=
  R.forest.mergeManyInto R.trees.vertices R.bottleneck

def selectedFiber (R : ActivePetalRecord M i cut) (v : Fin n) : Prop := R.selected (R.forest.root v)
def newRoots (R : ActivePetalRecord M i cut) : List (Fin n) :=
  R.trees.vertices.filter fun v => decide (v ≠ R.bottleneck)

theorem mem_newRoots (R : ActivePetalRecord M i cut) (v : Fin n) :
    v ∈ R.newRoots ↔ R.selected v ∧ v ≠ R.bottleneck := by
  simp only [newRoots, List.mem_filter, decide_eq_true_eq, R.trees.mem_vertices]

theorem trigger (R : ActivePetalRecord M i cut) :
    Bridge M R.left R.right ∧ MaximumMatching.edgeTenacity M R.left R.right = some (2 * i + 1) :=
  R.input.B.stage.classification.2.2 _ _ _ R.queued

theorem known (R : ActivePetalRecord M i cut) : edgeTenacity M R.prior R.left R.right = some (2 * i + 1) :=
  R.input.B.stage.current_bridge_known _ _ R.trigger.1 R.trigger.2

theorem starts_assigned (R : ActivePetalRecord M i cut) :
    (∃ k, R.prior.minLabel R.left = some k) ∧ (∃ k, R.prior.minLabel R.right = some k) :=
  edgeTenacity_has_minLabels R.prior R.left R.right (2 * i + 1) R.known

theorem path_live (R : ActivePetalRecord M i cut) (p : DDFS.Path R.graph)
    (hp : p.first = R.forest.root R.left ∨ p.first = R.forest.root R.right)
    (v : Fin n) (hv : p.Contains v) : v ∈ R.input.live := by
  apply R.input.path_live p _ v hv
  exact hp.elim (fun hh => hh ▸ R.left_live) (fun hh => hh ▸ R.right_live)

theorem selected_live (R : ActivePetalRecord M i cut) (v : Fin n) (hv : R.selected v) :
    v ∈ R.input.live := by
  obtain ⟨p, hp, _, j, hj⟩ := (R.region v).1 hv
  exact R.path_live p hp v ⟨j, hj⟩

theorem selected_root (R : ActivePetalRecord M i cut) (v : Fin n) (hv : R.selected v) :
    R.forest.root v = v := R.input.live_fixed v (R.selected_live v hv)

theorem selected_fixed (R : ActivePetalRecord M i cut) (v : Fin n) (hv : R.selected v) :
    R.forest.parent v = v := by
  rw [← R.selected_root v hv]
  exact R.forest.root_fixed v

theorem selected_assigned (R : ActivePetalRecord M i cut) (v : Fin n) (hv : R.selected v) :
    ∃ k, R.prior.minLabel v = some k := by
  obtain ⟨p, hp, _, j, hj⟩ := (R.region v).1 hv
  have hfirst : ∃ k, R.prior.minLabel (R.input.liftPath p).first = some k := by
    rcases hp with hp | hp
    · obtain ⟨k, hk⟩ := R.starts_assigned.1
      change ∃ k, R.prior.minLabel p.first = some k
      rw [hp]
      exact R.invariant.rootAssigned R.left k hk
    · obtain ⟨k, hk⟩ := R.starts_assigned.2
      change ∃ k, R.prior.minLabel p.first = some k
      rw [hp]
      exact R.invariant.rootAssigned R.right k hk
  have hh := R.invariant.path_assigned (R.input.liftPath p) hfirst j
  simpa only [ActiveSearchState.liftPath, hj] using hh

/-- Live levels agree with original stored minlevels throughout the region. -/
theorem selected_rank (R : ActivePetalRecord M i cut) (v : Fin n) (hv : R.selected v) :
    R.forest.rank v = R.graph.level v :=
  (R.invariant.rankLabel v).trans (R.input.level_live v (R.selected_live v hv)).symm

theorem guards (R : ActivePetalRecord M i cut) (x : Fin n) (hx : x ∈ R.trees.vertices) :
    R.forest.rank (R.forest.root R.bottleneck) < R.forest.rank (R.forest.root x) ∨
      R.forest.root x = R.forest.root R.bottleneck := by
  have hs := (R.trees.mem_vertices x).1 hx
  rw [R.selected_root x hs, R.selected_root R.bottleneck R.trees.bottleneck_mem]
  by_cases he : x = R.bottleneck
  · exact Or.inr he
  · left
    rw [R.selected_rank x hs, R.selected_rank R.bottleneck R.trees.bottleneck_mem]
    exact DDFS.onRootTo_level_gt ((R.region x).1 hs) he

theorem after_root (R : ActivePetalRecord M i cut) (v : Fin n) :
    R.after.root v = if R.forest.root v ∈ R.trees.vertices then R.bottleneck else R.forest.root v := by
  have hmem : R.forest.root v ∈ R.trees.vertices.map R.forest.root ↔
      R.forest.root v ∈ R.trees.vertices := by
    constructor
    · rintro hm
      obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
      rw [R.selected_root x ((R.trees.mem_vertices x).1 hx)] at he
      exact he ▸ hx
    · intro hv
      exact List.mem_map.mpr ⟨R.forest.root v, hv, R.forest.root_idempotent v⟩
  change (R.forest.mergeManyInto R.trees.vertices R.bottleneck).root v = _
  rw [R.forest.mergeManyInto_root_exact _ _ v R.guards,
    R.selected_root R.bottleneck R.trees.bottleneck_mem]
  simp only [hmem]

theorem after_selected (R : ActivePetalRecord M i cut) (v : Fin n) (hv : R.selectedFiber v) :
    R.after.root v = R.bottleneck := by
  rw [R.after_root, ite_eq_left ((R.trees.mem_vertices _).2 hv)]

theorem after_outside (R : ActivePetalRecord M i cut) (v : Fin n) (hv : ¬R.selectedFiber v) :
    R.after.root v = R.forest.root v := by
  rw [R.after_root, ite_eq_right (fun hm => hv ((R.trees.mem_vertices _).1 hm))]

theorem after_invariant (R : ActivePetalRecord M i cut) :
    BudGraphInvariant M (i + 1) R.prior R.after := by
  refine ⟨R.invariant.minInvariant, R.invariant.labelsBounded, ?_, ?_⟩
  · intro v k hv
    apply R.forest.mergeManyInto_root_predicate (fun w => ∃ j, R.prior.minLabel w = some j) ?_
      R.trees.vertices R.bottleneck (R.selected_assigned _ R.trees.bottleneck_mem) v ⟨k, hv⟩
    rintro w ⟨j, hj⟩
    exact R.invariant.rootAssigned w j hj
  · intro v
    exact (R.forest.mergeManyInto_rank R.trees.vertices R.bottleneck v).trans (R.invariant.rankLabel v)

/-- Deleted old root classes remain outside the computed region and never
become active by a later merge. -/
theorem after_inactive (R : ActivePetalRecord M i cut) (v : Fin n)
    (hv : R.forest.root v ∉ R.input.live) : R.after.root v = R.forest.root v :=
  R.after_outside v (fun hs => hv (R.selected_live _ hs))

/-- Retain precisely the old live vertices that are still current roots. -/
def afterLive (R : ActivePetalRecord M i cut) : List (Fin n) :=
  R.input.live.filter fun v => decide (R.after.root v = v)

theorem mem_afterLive (R : ActivePetalRecord M i cut) (v : Fin n) :
    v ∈ R.afterLive ↔ v ∈ R.input.live ∧ R.after.root v = v := by
  simp only [afterLive, List.mem_filter, decide_eq_true_eq]

theorem after_root_live (R : ActivePetalRecord M i cut) (v : Fin n) (hv : v ∈ R.input.live) :
    R.after.root v ∈ R.afterLive := by
  apply (R.mem_afterLive _).2
  refine ⟨?_, R.after.root_idempotent v⟩
  rw [R.after_root]
  split
  · exact R.selected_live _ R.trees.bottleneck_mem
  · rwa [R.input.live_fixed v hv]

theorem after_root_inactive (R : ActivePetalRecord M i cut) (v : Fin n)
    (hv : R.forest.root v ∉ R.input.live) : R.after.root v ∉ R.afterLive := by
  rw [R.after_inactive v hv]
  exact fun hh => hv ((R.mem_afterLive _).1 hh).1

theorem starts_selected (R : ActivePetalRecord M i cut) :
    R.selected (R.forest.root R.left) ∧ R.selected (R.forest.root R.right) := by
  obtain ⟨p, hpf, hpb, _⟩ := R.trees.red.path R.bottleneck (Or.inl rfl)
  obtain ⟨q, hqf, hqb, _⟩ := R.trees.green.path R.bottleneck (Or.inl rfl)
  exact ⟨(R.region _).2 ⟨p, Or.inl hpf, hpb, ⟨0, by omega⟩, hpf⟩,
    (R.region _).2 ⟨q, Or.inr hqf, hqb, ⟨0, by omega⟩, hqf⟩⟩

theorem after_trigger_equal (R : ActivePetalRecord M i cut) :
    R.after.root R.left = R.after.root R.right :=
  (R.after_selected R.left R.starts_selected.1).trans (R.after_selected R.right R.starts_selected.2).symm

theorem after_root_congr (R : ActivePetalRecord M i cut) (u v : Fin n)
    (he : R.forest.root u = R.forest.root v) : R.after.root u = R.after.root v :=
  R.forest.mergeManyInto_root_congr R.trees.vertices R.bottleneck u v he

end ActivePetalRecord
end MaximumMatching.Search
