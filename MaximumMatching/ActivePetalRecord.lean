import MaximumMatching.ActiveSearch
import MaximumMatching.PetalPathTransport

section ActivePetalRecord

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

end ActivePetalRecord

section ActivePetalPaths

/-! Computed tails in the live petal region. Every successor is selected from
an actual live edge, so removal cannot invalidate the recovered tail. -/
namespace MaximumMatching.Search.ActivePetalRecord
variable {n i cut : Nat} {G : Graph (Fin n)} {M : Matching G}

theorem selected_edge_closed (R : ActivePetalRecord M i cut) {v w : Fin n}
    (hv : R.selected v) (hne : v ≠ R.bottleneck)
    (he : R.graph.Edge v w) : R.selected w := by
  have hlevel := DDFS.onRootTo_level_gt ((R.region v).1 hv) hne
  obtain ⟨p, hp, hpb, i, hiv⟩ := (R.region v).1 hv
  let a := p.take i.val (by omega)
  have haf : a.first = p.first := rfl
  have hal : a.last = v := hiv
  obtain ⟨z, hzf, hz0⟩ := R.input.reach w
  have hze : R.graph.Edge v z.first := by
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
  have hte : R.graph.Edge v tail.first := hze
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

/-- Select the first live outgoing edge; bottom reachability excludes an
empty scan at every positive layer. -/
def firstSuccessor (R : ActivePetalRecord M i cut) (v : Fin n)
    (hpos : 0 < R.graph.level v) : { w : Fin n // R.graph.Edge v w } :=
  match hh : R.input.live.find? (fun w => decide (R.graph.Edge v w)) with
  | some w => ⟨w, of_decide_eq_true (List.find?_some (p := fun w => decide (R.graph.Edge v w)) hh)⟩
  | none => False.elim (by
      obtain ⟨p, hpf, hpb⟩ := R.input.reach v
      change R.graph.level p.last = 0 at hpb
      have hlen : 0 < p.length := by
        by_cases hl : p.length = 0
        · have hfl : p.first = p.last := congrArg p.vertex (Fin.ext (by exact hl.symm))
          rw [← hfl, hpf] at hpb
          omega
        · omega
      have he := p.adjacent ⟨0, hlen⟩
      change R.graph.Edge p.first (p.vertex ⟨1, by omega⟩) at he
      rw [hpf] at he
      have hn := List.find?_eq_none.mp hh _ he.2.1
      simp only [decide_eq_true_eq] at hn
      exact hn he)

/-- Recover the actual descending live path from a selected root to its
recorded bottleneck, scanning only live outgoing edges. -/
def recoverTail (R : ActivePetalRecord M i cut) (v : Fin n) (hv : R.selected v) :
    { p : DDFS.Path R.graph //
      p.first = v ∧ p.last = R.bottleneck ∧ ∀ w, p.Contains w → R.selected w } :=
  if he : v = R.bottleneck then
    ⟨DDFS.Path.trivial _ v, rfl, he, by
      rintro w ⟨j, hj⟩
      change v = w at hj
      exact hj ▸ hv⟩
  else
    have hpos : 0 < R.graph.level v :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) (DDFS.onRootTo_level_gt ((R.region v).1 hv) he)
    let u := R.firstSuccessor v hpos
    let q := R.recoverTail u.val (R.selected_edge_closed hv he u.property)
    have hedge : R.graph.Edge v q.val.first := q.property.1.symm ▸ u.property
    ⟨q.val.prepend v hedge, rfl, (q.val.prepend_last v hedge).trans q.property.2.1, by
      intro w hw
      rcases (q.val.contains_prepend_iff v hedge w).1 hw with hw | hw
      · exact hw.symm ▸ hv
      · exact q.property.2.2 w hw⟩
termination_by R.graph.level v
decreasing_by exact R.graph.decreases u.property

end MaximumMatching.Search.ActivePetalRecord

end ActivePetalPaths

section ActivePetalMax

/-! Sound current-level assignments from trees computed on the live graph.
The colored trees lift to original predecessor edges; no assertion that the
live region equals the region of the undeleted graph is required. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}
namespace CurrentBridgeRepresentation
variable {cap cut : Nat} {s : State (Fin n)} {F : BudForest (Fin n)}
    {h : BudGraphInvariant M cap s F}

theorem colored_linkage_support (P : CurrentBridgeRepresentation M cut h)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (u v : Fin n) (hbridge : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, s.minLabel u = some k) (hv : ∃ k, s.minLabel v = some k)
    (b : Fin n) (S : Fin n → Prop)
    (T : DDFS.ColoredTrees (predecessorGraph s F h) S (F.root u) (F.root v) b)
    (w : Fin n) (hw : S w)
    (hlevel : (predecessorGraph s F h).level b < (predecessorGraph s F h).level w) :
    tenacity M w = some (cut + 2) ∧ InSupport M u v w := by
  obtain ⟨p, q, hpw, hqb, hdis, hstart⟩ := T.bottom_linkage h.reachBottom w hw hlevel
  have hrootu : ∃ k, s.minLabel (F.root u) = some k := by
    obtain ⟨k, hk⟩ := hu
    exact h.rootAssigned u k hk
  have hrootv : ∃ k, s.minLabel (F.root v) = some k := by
    obtain ⟨k, hk⟩ := hv
    exact h.rootAssigned v k hk
  have hpa : ∃ k, s.minLabel p.first = some k := by
    rcases hstart with ⟨hpu, _, _⟩ | ⟨hpv, _, _⟩
    · rw [hpu]; exact hrootu
    · rw [hpv]; exact hrootv
  have hpf : F.parent p.first = p.first := by
    rcases hstart with ⟨hpu, _, _⟩ | ⟨hpv, _, _⟩
    · rw [hpu]; exact F.root_fixed u
    · rw [hpv]; exact F.root_fixed v
  have hwfixed : F.parent w = w := by
    have hh := h.path_fixed p hpf ⟨p.length, by omega⟩
    simpa only [show p.vertex ⟨p.length, by omega⟩ = w from hpw] using hh
  have hwassigned : ∃ k, s.minLabel w = some k := by
    have hh := h.path_assigned p hpa ⟨p.length, by omega⟩
    simpa only [show p.vertex ⟨p.length, by omega⟩ = w from hpw] using hh
  obtain ⟨k, hk⟩ := hwassigned
  have hwhigh : levelLT (some cut) (tenacity M w) := by
    have hh := P.high w k hk
    rwa [F.root_of_fixed w hwfixed] at hh
  have hex : ∃ z : AltPath M, z.last = w ∧ z.length + k = cut + 2 ∧ z.ContainsEdge u v := by
    rcases hstart with ⟨hpu, hqv, _⟩ | ⟨hpv, hqu, _⟩
    · obtain ⟨z, _, hzw, hlen, he⟩ := P.bridge_linkage_path u v
        hbridge ht hu hv p q hpu hqv hqb hdis
      rw [hpw, hk] at hlen
      exact ⟨z, hzw.trans hpw, hlen, he⟩
    · obtain ⟨z, _, hzw, hlen, he⟩ := P.bridge_linkage_path v u
        (bridge_symm hbridge) ((edgeTenacity_symmetric v u).trans ht) hv hu p q hpv hqu hqb hdis
      rw [hpw, hk] at hlen
      exact ⟨z, hzw.trans hpw, hlen, (z.containsEdge_symm v u).1 he⟩
  obtain ⟨z, hzw, hlen, he⟩ := hex
  have hmin : minlevel M z.last = some k := by rw [hzw]; exact h.minInvariant.1.1 w k hk
  obtain ⟨hzt, hmax⟩ := z.maxlevel_of_complementary_length cut k hc hmin
    (by rw [hzw]; exact hwhigh) hlen
  have hwt : tenacity M w = some (cut + 2) := by rwa [hzw] at hzt
  exact ⟨hwt, hbridge, cut + 2, htop, ht, hwt, z, hzw,
    by rwa [hzw] at hmax, he⟩

end CurrentBridgeRepresentation

namespace ActivePetalRecord
variable {i cut : Nat}

/-- Retain the stored parent maps while viewing each live edge as an original
predecessor edge. This does not lift the all-path bottleneck assertion. -/
def ambientTrees (R : ActivePetalRecord M i cut) :
    DDFS.ColoredTrees (predecessorGraph R.prior R.forest R.invariant)
      R.selected (R.forest.root R.left) (R.forest.root R.right) R.bottleneck where
  color := R.trees.color
  bottleneck_mem := R.trees.bottleneck_mem
  domain := R.trees.domain
  red := {
    parent := R.trees.red.parent
    root_none := R.trees.red.root_none
    edge := fun u v he => ⟨(R.trees.red.edge u v he).1,
      (R.trees.red.edge u v he).2.1, (R.trees.red.edge u v he).2.2.2.2⟩
    spanning := R.trees.red.spanning }
  green := {
    parent := R.trees.green.parent
    root_none := R.trees.green.root_none
    edge := fun u v he => ⟨(R.trees.green.edge u v he).1,
      (R.trees.green.edge u v he).2.1, (R.trees.green.edge u v he).2.2.2.2⟩
    spanning := R.trees.green.spanning }

/-- Every newly merged live root has exactly the current tenacity and belongs
to the triggering bridge's semantic support in the original matching. -/
theorem newRoots_support_of_current (R : ActivePetalRecord M i cut)
    (P : CurrentBridgeRepresentation M cut R.invariant)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) (v : Fin n) (hv : v ∈ R.newRoots) :
    MaximumMatching.tenacity M v = some (2 * i + 1) ∧ InSupport M R.left R.right v := by
  obtain ⟨hs, hn⟩ := (R.mem_newRoots v).1 hv
  have hl := DDFS.onRootTo_level_gt ((R.region v).1 hs) hn
  have hlevel : (predecessorGraph R.prior R.forest R.invariant).level R.bottleneck <
      (predecessorGraph R.prior R.forest R.invariant).level v := by
    change (R.prior.minLabel R.bottleneck).getD 0 < (R.prior.minLabel v).getD 0
    simpa only [R.input.level_live v (R.selected_live v hs),
      R.input.level_live R.bottleneck (R.selected_live _ R.trees.bottleneck_mem)] using hl
  have hh := P.colored_linkage_support hc htop R.left R.right R.trigger.1
    (by rw [hstageTen]; exact R.trigger.2) R.starts_assigned.1 R.starts_assigned.2
    R.bottleneck R.selected R.ambientTrees v hs hlevel
  exact ⟨by simpa only [hstageTen] using hh.1, hh.2⟩

section
variable [DecidableRel G.Adj]

def maxEvent (R : ActivePetalRecord M i cut) : State (Fin n) × BudForest (Fin n) :=
  (maxProcessVertices M i R.newRoots R.prior, R.after)

theorem maxEvent_minLabel (R : ActivePetalRecord M i cut) (v : Fin n) :
    R.maxEvent.1.minLabel v = R.prior.minLabel v :=
  maxProcessVertices_minLabel M i R.newRoots R.prior v

theorem maxEvent_outside (R : ActivePetalRecord M i cut) (v : Fin n) (hv : v ∉ R.newRoots) :
    R.maxEvent.1.maxLabel v = R.prior.maxLabel v :=
  maxProcessVertices_outside_maxLabel M i R.newRoots R.prior v hv

theorem maxEvent_bucket_mono (R : ActivePetalRecord M i cut)
    (u v : Fin n) (t : Nat) (h : (u, v) ∈ R.prior.bucket t) :
    (u, v) ∈ R.maxEvent.1.bucket t :=
  maxProcessVertices_bucket_mono M i R.prior R.newRoots u v t h

/-- The lower-cutoff root bound survives because every new root was already
an assigned old root; it is independent of deletion completeness. -/
theorem maxEvent_high (R : ActivePetalRecord M i cut)
    (P : CurrentBridgeRepresentation M cut R.invariant) :
    ∀ v k, R.maxEvent.1.minLabel v = some k →
      levelLT (some cut) (tenacity M (R.after.root v)) := by
  intro v k hv
  have hold : R.prior.minLabel v = some k := (R.maxEvent_minLabel v).symm.trans hv
  rw [R.after_root]
  split
  · obtain ⟨j, hj⟩ := R.selected_assigned R.bottleneck R.trees.bottleneck_mem
    have hh := P.high R.bottleneck j hj
    rwa [R.selected_root R.bottleneck R.trees.bottleneck_mem] at hh
  · exact P.high v k hold

/-- MAX keeps the full semantic stage state and bud invariant after an active
petal contraction, despite computing its region in the restricted graph. -/
theorem maxEvent_correct_of_current (R : ActivePetalRecord M i cut)
    (P : CurrentBridgeRepresentation M cut R.invariant)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) :
    StageState M (i + 1) (2 * i + 1) R.maxEvent.1 ∧
      BudGraphInvariant M (i + 1) R.maxEvent.1 R.maxEvent.2 ∧
      (∀ v, v ∈ R.newRoots → R.maxEvent.1.maxLabel v = maxlevel M v) ∧
      (∀ v k, R.prior.maxLabel v = some k → R.maxEvent.1.maxLabel v = some k) := by
  have hroots : ∀ v, v ∈ R.newRoots → MaximumMatching.tenacity M v = some (2 * i + 1) :=
    fun v hv => (R.newRoots_support_of_current P hc htop hstageTen v hv).1
  have hs := maxProcessVertices_stageState M i (2 * i + 1) R.newRoots R.prior R.input.B.stage hroots
  refine ⟨hs, ?_, ?_, ?_⟩
  · refine ⟨hs.min, hs.minBound, ?_, ?_⟩
    · intro v k hv
      have hold : R.prior.minLabel v = some k := (R.maxEvent_minLabel v).symm.trans hv
      obtain ⟨j, hj⟩ := R.after_invariant.rootAssigned v k hold
      exact ⟨j, (R.maxEvent_minLabel (R.after.root v)).trans hj⟩
    · intro v
      exact (R.after_invariant.rankLabel v).trans (congrArg (fun x : Option Nat => x.getD 0)
        (R.maxEvent_minLabel v).symm)
  · intro v hv
    exact maxProcessVertices_member_correct M i (2 * i + 1) R.newRoots R.prior R.input.B.stage hroots v hv
  · intro v k hv
    exact maxProcessVertices_preserves_known_maxLabel M i (2 * i + 1) R.newRoots R.prior R.input.B.stage hroots v k hv

end
end ActivePetalRecord
end MaximumMatching.Search

end ActivePetalMax
