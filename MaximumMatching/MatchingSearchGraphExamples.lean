import MaximumMatching.MatchingSearchGraph
import MaximumMatching.MinMaxExamples

/-! Kernel-checked execution of the matching-derived predecessor graph. -/
namespace MaximumMatching.Examples.MatchingSearch
open Search

theorem firstMin_invariant : BudGraphInvariant middleMatching 1 MinMax.firstMin
    (uncontractedForest MinMax.firstMin) := by
  apply uncontractedForest_invariant _ _ MinMax.firstMin_correct
  exact scanCandidates_minLabelsBound _ _ 0
    (fun v k hk => Nat.le_trans (initial_minLabelsBound middleMatching v k hk) (by omega))

def firstGraph : DDFS.LayeredGraph (Fin 4) :=
  predecessorGraph MinMax.firstMin (uncontractedForest MinMax.firstMin) firstMin_invariant

instance : DecidableRel firstGraph.Edge :=
  inferInstanceAs (DecidableRel (predecessorGraph _ _ firstMin_invariant).Edge)

theorem firstGraph_layers : (List.finRange 4).map firstGraph.level = [0, 1, 1, 0] := by decide

theorem firstGraph_edges : ∀ u v : Fin 4,
    firstGraph.Edge u v ↔ (u = 1 ∧ v = 0) ∨ (u = 2 ∧ v = 3) := by
  change ∀ u v : Fin 4, ((MinMax.firstMin.minLabel u).isSome = true ∧
    v ∈ (MinMax.firstMin.predecessors u).map (uncontractedForest MinMax.firstMin).root) ↔ _
  have hr : (uncontractedForest MinMax.firstMin).root = id :=
    funext fun v => (uncontractedForest MinMax.firstMin).root_of_fixed v rfl
  rw [hr]
  decide

/- The graph is computed from the actual first MIN pass, including both
predecessor branches of the matched-edge bridge. -/
/-- info: true -/
#guard_msgs in
#eval (allCandidates 4).filter (fun e => decide (firstGraph.Edge e.1 e.2)) == [(1, 0), (2, 3)]

/-- Initially an unmatched-search label may still be unknown at a matched
vertex. Its artificial layer-zero representation never asserts it is free. -/
theorem inactive_is_not_free :
    (predecessorGraph (initial middleMatching) (uncontractedForest (initial middleMatching))
      (initial_budGraphInvariant middleMatching)).level 1 = 0 ∧
      ¬ middleMatching.Free 1 ∧
      ∀ w, ¬ budEdge (initial middleMatching) (uncontractedForest (initial middleMatching)) 1 w := by
  refine ⟨by decide, ?_, ?_⟩
  · change ¬ middleMatching.mate 1 = none
    decide
  · intro w he
    have hz : (initial middleMatching).minLabel 1 = none := by decide
    have hsome := he.1
    simp only [hz, Option.isSome_none, Bool.false_eq_true] at hsome

end MaximumMatching.Examples.MatchingSearch
