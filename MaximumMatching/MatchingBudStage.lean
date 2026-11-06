import MaximumMatching.MatchingSearchGraph
import MaximumMatching.BudLabels

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
