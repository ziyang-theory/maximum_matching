import MaximumMatching.BudForest
import MaximumMatching.DDFSBud
import MaximumMatching.DDFSPaths
import MaximumMatching.MaxBridgeRefresh

section MatchingSearchGraph

/-! The matching-derived layered graph of source §4.3 (p.16). Its edges are
computed from the actual MIN predecessor lists and current bud roots. The
whole vertex type is retained; unlabeled vertices are isolated at layer zero.
Paths from labeled roots remain labeled, so their bottom vertices are free.
No matching-support conclusion is included in the representation invariant. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

/-- The structural data needed to turn actual MIN lists into a DDFS graph.
Ranks represent assigned minimum labels; contractions preserve assignment of
the represented root. List correctness is supplied by the existing MIN
invariant, rather than a DDFS or support oracle. -/
structure BudGraphInvariant (M : Matching G) (i : Nat) (s : State V)
    (F : BudForest V) : Prop where
  minInvariant : MinInvariant M i s
  labelsBounded : MinLabelsBound i s
  rootAssigned : ∀ v k, s.minLabel v = some k → ∃ j, s.minLabel (F.root v) = some j
  rankLabel : ∀ v, F.rank v = (s.minLabel v).getD 0

/-- The executable edge test: follow a recorded predecessor to its current bud. -/
def budEdge (s : State V) (F : BudForest V) (v w : V) : Prop :=
  (s.minLabel v).isSome = true ∧ w ∈ (s.predecessors v).map F.root

instance (s : State V) (F : BudForest V) : DecidableRel (budEdge s F) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

namespace BudGraphInvariant
variable {i : Nat} {s : State V} {F : BudForest V}

theorem unknown_fixed (h : BudGraphInvariant M i s F) (v : V)
    (hv : s.minLabel v = none) : F.parent v = v := by
  by_cases hp : F.parent v = v
  · exact hp
  · have hd := F.decreases v hp
    have hr : F.rank v = 0 := by simp only [h.rankLabel, hv, Option.getD_none]
    omega

theorem parent_assigned (h : BudGraphInvariant M i s F) (v : V) (k : Nat)
    (hv : s.minLabel v = some k) : ∃ j, s.minLabel (F.parent v) = some j := by
  cases hp : s.minLabel (F.parent v) with
  | some j => exact ⟨j, rfl⟩
  | none =>
    have he : F.root v = F.parent v :=
      (F.root_parent v).symm.trans (F.root_of_fixed _ (h.unknown_fixed _ hp))
    obtain ⟨j, hj⟩ := h.rootAssigned v k hv
    rw [he, hp] at hj
    contradiction

theorem listed_iff (h : BudGraphInvariant M i s F) (u v : V) (k : Nat)
    (hv : s.minLabel v = some k) : u ∈ s.predecessors v ↔ Predecessor M u v := by
  constructor
  · exact h.minInvariant.2.2.2.2 u v
  · intro hp
    exact (h.minInvariant.2.2.2.1 u v
      (h.minInvariant.2.2.1 u v k hp (h.minInvariant.1.1 v k hv)
        (h.labelsBounded v k hv)) hp).1

theorem predecessor_assigned (h : BudGraphInvariant M i s F) (u v : V)
    (k : Nat) (hv : s.minLabel v = some k) (hp : Predecessor M u v) :
    ∃ j, s.minLabel u = some j ∧ j < k := by
  obtain ⟨p, hpv, hpm, hpos, hpu⟩ := hp
  obtain ⟨j, hj, hjp⟩ := minlevel_finite_of_path (p.take (p.length - 1) (by omega))
  have hju : minlevel M u = some j := by simpa only [AltPath.take_last, hpu] using hj
  have hpk : p.length = k := Option.some.inj
    (hpm.symm.trans (h.minInvariant.1.1 v k hv))
  have hjk : j < k := by simp only [AltPath.take_length] at hjp; omega
  exact ⟨j, h.minInvariant.2.1 u j hju (by have := h.labelsBounded v k hv; omega), hjk⟩

theorem edge_witness (h : BudGraphInvariant M i s F) {v w : V}
    (he : budEdge s F v w) :
    ∃ u k j, s.minLabel v = some k ∧ s.minLabel u = some j ∧
      Predecessor M u v ∧ F.root u = w ∧ j < k := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp he.1
  obtain ⟨u, hu, huw⟩ := List.mem_map.mp he.2
  have hp := (h.listed_iff u v k hk).1 hu
  obtain ⟨j, hj, hjk⟩ := h.predecessor_assigned u v k hk hp
  exact ⟨u, k, j, hk, hj, hp, huw, hjk⟩

theorem edge_target_assigned (h : BudGraphInvariant M i s F) {v w : V}
    (he : budEdge s F v w) : ∃ k, s.minLabel w = some k := by
  obtain ⟨u, _, j, _, hu, _, rfl, _⟩ := h.edge_witness he
  exact h.rootAssigned u j hu

theorem edge_decreases (h : BudGraphInvariant M i s F) {v w : V}
    (he : budEdge s F v w) : (s.minLabel w).getD 0 < (s.minLabel v).getD 0 := by
  obtain ⟨u, k, j, hv, hu, _, rfl, hjk⟩ := h.edge_witness he
  have hh := F.root_rank_le u
  rw [h.rankLabel, h.rankLabel, hu] at hh
  simpa only [hv, Option.getD_some] using Nat.lt_of_le_of_lt hh hjk

/-- Every assigned nonzero vertex has an actual outgoing predecessor edge. -/
theorem outgoing (h : BudGraphInvariant M i s F) (v : V)
    (hpos : 0 < (s.minLabel v).getD 0) : ∃ w, budEdge s F v w := by
  cases hv : s.minLabel v with
  | none => simp only [hv, Option.getD_none] at hpos; omega
  | some k =>
    have hk : 0 < k := by simpa only [hv, Option.getD_some] using hpos
    obtain ⟨u, hu⟩ := minlevel_succ_has_predecessor v (k - 1)
      (by simpa only [Nat.sub_add_cancel hk] using h.minInvariant.1.1 v k hv)
    refine ⟨F.root u, ?_, List.mem_map.mpr ⟨u, (h.listed_iff u v k hv).2 hu, rfl⟩⟩
    simp only [hv, Option.isSome_some]

end BudGraphInvariant

/-- A finite executable DDFS graph when `V = Fin n`; the definition also works
on any decidable vertex type. Its layer is the actual stored minimum label. -/
def predecessorGraph (s : State V) (F : BudForest V)
    (h : BudGraphInvariant M i s F) : DDFS.LayeredGraph V where
  Edge := budEdge s F
  level v := (s.minLabel v).getD 0
  decreases := h.edge_decreases

instance (s : State V) (F : BudForest V) (h : BudGraphInvariant M i s F) :
    DecidableRel (predecessorGraph s F h).Edge := inferInstanceAs (DecidableRel (budEdge s F))

namespace BudGraphInvariant
variable {i : Nat} {s : State V} {F : BudForest V}

theorem reachBottom (h : BudGraphInvariant M i s F) :
    DDFS.ReachBottom (predecessorGraph s F h) := by
  intro v
  generalize he : (s.minLabel v).getD 0 = k
  induction k using Nat.strongRecOn generalizing v with
  | ind k ih =>
    by_cases hk : k = 0
    · exact ⟨DDFS.Path.trivial _ v, rfl, he.trans hk⟩
    · obtain ⟨w, hw⟩ := h.outgoing v (by omega)
      have hlt := h.edge_decreases hw
      obtain ⟨p, hp, hb⟩ := ih _ (by omega) w rfl
      have hedge : (predecessorGraph s F h).Edge v p.first := by rw [hp]; exact hw
      exact ⟨p.prepend v hedge, DDFS.Path.prepend_first _ _ _,
        by simpa only [DDFS.Path.prepend_last] using hb⟩

theorem edge_target_fixed (h : BudGraphInvariant M i s F) {v w : V}
    (he : (predecessorGraph s F h).Edge v w) : F.parent w = w := by
  obtain ⟨u, _, huw⟩ := List.mem_map.mp he.2
  rw [← huw]
  exact F.root_fixed u

theorem path_fixed (h : BudGraphInvariant M i s F)
    (p : DDFS.Path (predecessorGraph s F h)) (hfirst : F.parent p.first = p.first)
    (j : Fin (p.length + 1)) : F.parent (p.vertex j) = p.vertex j := by
  by_cases hj : j.val = 0
  · have he : j = ⟨0, by omega⟩ := Fin.ext hj
    simpa only [he, DDFS.Path.first] using hfirst
  · have he := h.edge_target_fixed (p.adjacent ⟨j.val - 1, by omega⟩)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j.val), Fin.eta] using he

theorem path_assigned (h : BudGraphInvariant M i s F)
    (p : DDFS.Path (predecessorGraph s F h))
    (hfirst : ∃ k, s.minLabel p.first = some k) (j : Fin (p.length + 1)) :
    ∃ k, s.minLabel (p.vertex j) = some k := by
  by_cases hj : j.val = 0
  · have he : j = ⟨0, by omega⟩ := Fin.ext hj
    simpa only [he, DDFS.Path.first] using hfirst
  · have he := h.edge_target_assigned (p.adjacent ⟨j.val - 1, by omega⟩)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j.val), Fin.eta] using he

/-- Layer zero along an active path is a genuine free matching vertex. The
claim deliberately requires assignment at the start, excluding isolated
unlabeled vertices introduced by the whole-universe representation. -/
theorem path_bottom_free (h : BudGraphInvariant M i s F)
    (p : DDFS.Path (predecessorGraph s F h))
    (hfirst : ∃ k, s.minLabel p.first = some k)
    (hbottom : (predecessorGraph s F h).level p.last = 0) : M.Free p.last := by
  obtain ⟨k, hk⟩ := h.path_assigned p hfirst ⟨p.length, by omega⟩
  change s.minLabel p.last = some k at hk
  change (s.minLabel p.last).getD 0 = 0 at hbottom
  have hk0 : k = 0 := by simpa only [hk, Option.getD_some] using hbottom
  exact (minlevel_zero_iff_free p.last).1 (h.minInvariant.1.1 p.last 0 (hk0 ▸ hk))

theorem root_reaches_free (h : BudGraphInvariant M i s F) (v : V) (k : Nat)
    (hv : s.minLabel v = some k) :
    ∃ p : DDFS.Path (predecessorGraph s F h), p.first = F.root v ∧ M.Free p.last ∧
      (∀ j, F.parent (p.vertex j) = p.vertex j) := by
  obtain ⟨p, hp, hb⟩ := h.reachBottom (F.root v)
  have ha : ∃ j, s.minLabel p.first = some j := by rw [hp]; exact h.rootAssigned v k hv
  exact ⟨p, hp, h.path_bottom_free p ha hb,
    h.path_fixed p (by rw [hp]; exact F.root_fixed v)⟩

end BudGraphInvariant
/-- Before contraction the bud forest has only singleton classes and uses
the actual stored minimum labels as ranks. -/
def uncontractedForest (s : State V) : BudForest V where
  parent v := v
  rank v := (s.minLabel v).getD 0
  decreases := by intro v hv; exact False.elim (hv rfl)

theorem uncontractedForest_invariant (s : State V) (i : Nat)
    (hs : MinInvariant M i s) (hb : MinLabelsBound i s) :
    BudGraphInvariant M i s (uncontractedForest s) where
  minInvariant := hs
  labelsBounded := hb
  rootAssigned v k hv := ⟨k, by
    rw [(uncontractedForest s).root_of_fixed v rfl]
    exact hv⟩
  rankLabel _ := rfl

theorem initial_budGraphInvariant (M : Matching G) :
    BudGraphInvariant M 0 (initial M) (uncontractedForest (initial M)) :=
  uncontractedForest_invariant _ _ (initial_minInvariant M) (initial_minLabelsBound M)

end MaximumMatching.Search

end MatchingSearchGraph

section MatchingBudStage

/-! Bud initialization and actual MIN-stage rank updates. The current forest
keeps all its pointers while MIN assigns new labels; the resulting predecessor
and bud data again define the source's layered DDFS graph. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

theorem scanCandidates_preserves_assigned_minLabel [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (i : Nat) (hi : MinInvariant M i s)
    (v : V) (k : Nat) (hk : s.minLabel v = some k) :
    (scanCandidates M i xs s).minLabel v = some k := by
  induction xs generalizing s with
  | nil => exact hk
  | cons e es ih =>
    exact ih _ (scanCandidate_minInvariant s i e.1 e.2 hi)
      (scanCandidate_preserves_minLabel s i e.1 e.2 v k hi.1 hi.2.1 hk)

namespace BudGraphInvariant
variable {i : Nat} {s : State V} {F : BudForest V}

theorem assignedRoots (h : BudGraphInvariant M i s F) (v : V)
    (hv : (s.minLabel v).isSome) : (s.minLabel (F.root v)).isSome := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hv
  obtain ⟨j, hj⟩ := h.rootAssigned v k hk
  rw [hj]
  rfl

end BudGraphInvariant

section Finite
variable {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (s : State (Fin n)) (F : BudForest (Fin n))
    (h : BudGraphInvariant M i s F)

/-- Execute finite MIN and update the actual forest ranks to its labels.
Proof inputs certify the input representation; they do not prescribe output. -/
def scanLevelWithBuds : State (Fin n) × BudForest (Fin n) :=
  let next := scanLevel M i s
  (next, F.withLabels s.minLabel next.minLabel h.rankLabel h.assignedRoots
    (scanCandidates_preserves_assigned_minLabel (allCandidates n) s i h.minInvariant))

theorem scanLevelWithBuds_state : (scanLevelWithBuds M i s F h).1 = scanLevel M i s := rfl

theorem scanLevelWithBuds_root (v : Fin n) :
    (scanLevelWithBuds M i s F h).2.root v = F.root v :=
  F.withLabels_root s.minLabel (scanLevel M i s).minLabel h.rankLabel h.assignedRoots
    (scanCandidates_preserves_assigned_minLabel (allCandidates n) s i h.minInvariant) v

/-- Prior MAX labels supply the frontier needed for MIN completeness. All
forest representation clauses are derived for the actual resulting state. -/
theorem scanLevelWithBuds_invariant (hx : MaxCompleteBelowTenacity M (2 * i + 1) s) :
    BudGraphInvariant M (i + 1) (scanLevelWithBuds M i s F h).1
      (scanLevelWithBuds M i s F h).2 := by
  refine ⟨(scanLevel_complete M i s h.minInvariant
    (frontierAvailable_of_prior_levels s i h.minInvariant.2.1 hx)).1,
    scanCandidates_minLabelsBound (allCandidates n) s i
      (fun v k hk => Nat.le_trans (h.labelsBounded v k hk) (by omega)), ?_, ?_⟩
  · intro v k hk
    change (scanLevel M i s).minLabel v = some k at hk
    have hs : ((scanLevel M i s).minLabel v).isSome := by rw [hk]; rfl
    exact Option.isSome_iff_exists.mp (F.withLabels_assignedRoots s.minLabel
      (scanLevel M i s).minLabel h.rankLabel h.assignedRoots
      (scanCandidates_preserves_assigned_minLabel (allCandidates n) s i h.minInvariant) v hs)
  · intro v
    rfl

end Finite
end MaximumMatching.Search

end MatchingBudStage

section MatchingDDFSBud

/-! A concrete matching-state DDFS event. Its graph comes from recorded MIN
predecessors and current bud roots. The event retains the computed outcome,
contracts its actual bottleneck region, and preserves the graph invariant.
Identifying the region with matching bridge support remains separate. -/
namespace MaximumMatching.BudForest
variable {V : Type} [DecidableEq V]

theorem mergeInto_root_predicate (F : BudForest V) (A : V → Prop)
    (hA : ∀ v, A v → A (F.root v)) (x b : V) (hb : A b) :
    ∀ v, A v → A ((F.mergeInto x b).root v) := by
  intro v hv
  rw [F.mergeInto_root]
  split
  · exact hA b hb
  · exact hA v hv

theorem mergeManyInto_root_predicate (F : BudForest V) (A : V → Prop)
    (hA : ∀ v, A v → A (F.root v)) (xs : List V) (b : V) (hb : A b) :
    ∀ v, A v → A ((F.mergeManyInto xs b).root v) := by
  induction xs generalizing F with
  | nil => exact hA
  | cons x xs ih => exact ih (F.mergeInto x b) (F.mergeInto_root_predicate A hA x b hb)

end MaximumMatching.BudForest

namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}
variable {i : Nat} {s : State (Fin n)} {F : BudForest (Fin n)}

/-- Execute the finite search graph computed from actual MIN lists, starting
at the current buds of the supplied matching vertices, then contract its
actual bottleneck region. The full certified DDFS output is retained. -/
def executeBudSearch (h : BudGraphInvariant M i s F) (r g : Fin n) :
    DDFS.Machine.FullOutput (predecessorGraph s F h) (F.root r) (F.root g) × BudForest (Fin n) :=
  DDFS.Machine.executeAndContract h.reachBottom (F.root r) (F.root g) F

theorem executeBudSearch_rank (h : BudGraphInvariant M i s F) (r g v : Fin n) :
    (executeBudSearch h r g).2.rank v = F.rank v :=
  DDFS.Machine.executeAndContract_rank h.reachBottom (F.root r) (F.root g) F v

/-- Active matching starts ensure that all returned search vertices are
assigned fixed bud roots. In the disjoint case both bottom vertices are
genuinely free in the original matching. -/
theorem executeBudSearch_vertices (h : BudGraphInvariant M i s F) (r g : Fin n)
    (hr : ∃ k, s.minLabel r = some k) (hg : ∃ k, s.minLabel g = some k) :
    match (executeBudSearch h r g).1 with
    | .disjoint p q _ _ _ => M.Free p.last ∧ M.Free q.last ∧
        (∀ j, (∃ k, s.minLabel (p.vertex j) = some k) ∧ F.parent (p.vertex j) = p.vertex j) ∧
        (∀ j, (∃ k, s.minLabel (q.vertex j) = some k) ∧ F.parent (q.vertex j) = q.vertex j)
    | .bottleneck b S _ _ _ => (∃ k, s.minLabel b = some k) ∧
        ∀ v, S v → (∃ k, s.minLabel v = some k) ∧ F.parent v = v := by
  have hrootr : ∃ k, s.minLabel (F.root r) = some k := by
    obtain ⟨k, hk⟩ := hr
    exact h.rootAssigned r k hk
  have hrootg : ∃ k, s.minLabel (F.root g) = some k := by
    obtain ⟨k, hk⟩ := hg
    exact h.rootAssigned g k hk
  have paths (p : DDFS.Path (predecessorGraph s F h))
      (hp : p.first = F.root r ∨ p.first = F.root g) :
      ∀ j, (∃ k, s.minLabel (p.vertex j) = some k) ∧ F.parent (p.vertex j) = p.vertex j := by
    have ha : ∃ k, s.minLabel p.first = some k := by
      rcases hp with hp | hp
      · rw [hp]; exact hrootr
      · rw [hp]; exact hrootg
    have hf : F.parent p.first = p.first := by
      rcases hp with hp | hp
      · rw [hp]; exact F.root_fixed r
      · rw [hp]; exact F.root_fixed g
    intro j
    exact ⟨h.path_assigned p ha j, h.path_fixed p hf j⟩
  change match DDFS.Machine.executeFull h.reachBottom (F.root r) (F.root g) with
    | .disjoint p q _ _ _ => _
    | .bottleneck b S _ _ _ => _
  cases hout : DDFS.Machine.executeFull h.reachBottom (F.root r) (F.root g) with
  | disjoint p q hp hq hd =>
    exact ⟨h.path_bottom_free p (by rw [hp.1]; exact hrootr) hp.2,
      h.path_bottom_free q (by rw [hq.1]; exact hrootg) hq.2,
      paths p (Or.inl hp.1), paths q (Or.inr hq.1)⟩
  | bottleneck b S trees highest region =>
    have hvertices : ∀ v, S v → (∃ k, s.minLabel v = some k) ∧ F.parent v = v := by
      intro v hv
      obtain ⟨p, hp, _, j, hj⟩ := (region v).1 hv
      simpa only [hj] using paths p hp j
    exact ⟨(hvertices b trees.bottleneck_mem).1, hvertices⟩

/-- The actual finite contraction preserves every field needed to run the
next matching-derived DDFS graph. Its target is assigned by the actual
searched paths, rather than an assumed support invariant. -/
theorem executeBudSearch_preserves (h : BudGraphInvariant M i s F) (r g : Fin n)
    (hr : ∃ k, s.minLabel r = some k) (hg : ∃ k, s.minLabel g = some k) :
    BudGraphInvariant M i s (executeBudSearch h r g).2 := by
  have hvertices := executeBudSearch_vertices h r g hr hg
  change BudGraphInvariant M i s
    ((DDFS.Machine.executeFull h.reachBottom (F.root r) (F.root g)).contract F)
  change (match DDFS.Machine.executeFull h.reachBottom (F.root r) (F.root g) with
    | .disjoint p q _ _ _ => _
    | .bottleneck b S _ _ _ => _) at hvertices
  cases hout : DDFS.Machine.executeFull h.reachBottom (F.root r) (F.root g) with
  | disjoint p q hp hq hd => exact h
  | bottleneck b S trees highest region =>
    rw [hout] at hvertices
    refine ⟨h.minInvariant, h.labelsBounded, ?_, ?_⟩
    · intro v k hv
      apply F.mergeManyInto_root_predicate (fun w => ∃ j, s.minLabel w = some j) ?_
        trees.vertices b hvertices.1 v ⟨k, hv⟩
      intro w hw
      obtain ⟨j, hj⟩ := hw
      exact h.rootAssigned w j hj
    · intro v
      exact (F.mergeManyInto_rank trees.vertices b v).trans (h.rankLabel v)

/-- Every selected old bud class collapses to the actual reported
bottleneck. Root representation is derived from the matching graph itself. -/
theorem executeBudSearch_contracts (h : BudGraphInvariant M i s F) (r g b : Fin n)
    (S : Fin n → Prop) (trees : DDFS.ColoredTrees (predecessorGraph s F h) S (F.root r) (F.root g) b)
    (highest : DDFS.HighestBottleneck (predecessorGraph s F h) (F.root r) (F.root g) b)
    (region : ∀ v, S v ↔ DDFS.OnRootTo (H := predecessorGraph s F h) (F.root r) (F.root g) b v)
    (hout : DDFS.Machine.executeFull h.reachBottom (F.root r) (F.root g) =
      .bottleneck b S trees highest region)
    (v : Fin n) (hv : S (F.root v)) : (executeBudSearch h r g).2.root v = b := by
  exact DDFS.Machine.executeAndContract_root_targets h.reachBottom (F.root r) (F.root g) F
    b S trees highest region hout h.rankLabel (fun _ _ he => h.edge_target_fixed he)
    (F.root_fixed r) (F.root_fixed g) v hv

end MaximumMatching.Search

end MatchingDDFSBud
