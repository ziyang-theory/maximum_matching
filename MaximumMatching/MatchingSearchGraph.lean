import MaximumMatching.MaxBridgeRefresh
import MaximumMatching.Bud
import MaximumMatching.DDFSPaths

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
