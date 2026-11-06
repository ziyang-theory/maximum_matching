import MaximumMatching.DDFSWork

/-! Zero-edge boundary executions for the abstract work bound. -/
namespace MaximumMatching.DDFS.WorkExamples
open Machine

abbrev edgeless : LayeredGraph (Fin 2) where
  Edge := fun _ _ => False
  level := fun _ => 0
  decreases := by intro u v h; exact False.elim h

theorem edgeless_reaches : ReachBottom edgeless := by
  intro v
  exact ⟨Path.trivial edgeless v, rfl, rfl⟩

theorem edgeless_edgeCount : edgeCount edgeless = 0 := by
  classical
  simp [edgeCount]

abbrev equalDone : State edgeless :=
  { initial edgeless 0 0 with mode := .bottleneck 0 (Path.trivial edgeless 0) (Path.trivial edgeless 0) }

/-- Equal roots terminate in exactly the displayed one-step execution, with
no collision-recovery or graph scan. -/
theorem equalRoot_trace : Trace 1 (initial edgeless 0 0) equalDone :=
  .cons (.sameRoot _ rfl rfl rfl rfl) (.refl _)

theorem equalRoot_correct : CorrectOutcome 0 0 equalDone :=
  reachable_terminal_correct edgeless_reaches (equalRoot_trace.reachable .initial)
    (Or.inr ⟨0, Path.trivial edgeless 0, Path.trivial edgeless 0, rfl⟩)

abbrev distinctDone : State edgeless :=
  { initial edgeless 0 1 with mode := .disjoint }

/-- Distinct roots already in the bottom layer also terminate after one
transition, returning their disjoint zero-edge paths. -/
theorem distinctRoot_trace : Trace 1 (initial edgeless 0 1) distinctDone :=
  .cons (.bottom _ rfl (by decide) rfl rfl) (.refl _)

theorem distinctRoot_correct : CorrectOutcome 0 1 distinctDone :=
  reachable_terminal_correct edgeless_reaches (distinctRoot_trace.reachable .initial) (Or.inl rfl)

theorem boundary_zero_scans : scannedEdges equalDone.frame = 0 ∧
    scannedEdges distinctDone.frame = 0 := by
  classical
  simp [scannedEdges, edgeless]

/-- Applying the general work theorem to both actual zero-edge traces retains
the additive control allowance; an O(m)-only inequality would fail at m = 0. -/
theorem boundary_work_bounds :
    1 + workLocal equalDone ≤ 3 ∧ 1 + workLocal distinctDone ≤ 3 := by
  have he := trace_scanned_bound edgeless_reaches 0 0 equalRoot_trace
  have hd := trace_scanned_bound edgeless_reaches 0 1 distinctRoot_trace
  rw [boundary_zero_scans.1] at he
  rw [boundary_zero_scans.2] at hd
  exact ⟨he, hd⟩

end MaximumMatching.DDFS.WorkExamples
