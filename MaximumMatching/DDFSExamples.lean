import MaximumMatching.DDFSMachine

/-! Kernel-checked executions of the actual DDFS transitions. These fixtures
exercise collision recovery, red escape, restoration of the collision stack,
Barrier updates and termination before exploring below a bottleneck. They do
not replace the general invariant and correctness proofs. -/
namespace MaximumMatching.DDFS

namespace OwnershipExecution
open OwnershipExample
open OwnershipExample.Vertex
open Machine

private abbrev start : State graph := Machine.initial graph red green
private abbrev redShared : State graph :=
  ⟨start.frame.advanceRed shared (by change edge red shared; simp [edge]), .normal⟩
private abbrev meeting : State graph :=
  ⟨redShared.frame.advanceGreen shared (by change edge green shared; simp [edge]), .normal⟩
private abbrev recovering : State graph :=
  { meeting with mode := .redRecovery shared meeting.frame.red meeting.frame.green }
private abbrev popped : State graph :=
  ⟨recovering.frame.backtrackRed (by decide), recovering.mode⟩
private abbrev escaped : State graph :=
  ⟨popped.frame.advanceRed redBottom (by change edge red redBottom; simp [edge]), .normal⟩
private abbrev bottoms : State graph :=
  ⟨escaped.frame.advanceGreen greenBottom (by change edge shared greenBottom; simp [edge]), .normal⟩
abbrev finished : State graph := { bottoms with mode := .disjoint }

/-- Fully unfold these concrete updates and check the finite proposition in Lean's kernel. -/
macro "ownership_check" : tactic => `(tactic|
  (dsimp [start, redShared, meeting, recovering, popped, escaped, bottoms, finished,
    Machine.initial, SearchFrame.initial, SearchFrame.advanceRed,
    SearchFrame.advanceGreen, SearchFrame.swap, SearchFrame.backtrackRed,
    SearchFrame.backtrackGreen, SearchFrame.restoreRed, Path.pop, Path.take,
    Path.snoc, Path.first, Path.last, Path.trivial, Path.Contains, OwnershipExample.graph, OwnershipExample.edge, OwnershipExample.layer]
   decide))

private theorem step_red : Step start redShared :=
  .redMove start rfl (by ownership_check) (by ownership_check) shared (by ownership_check) (by ownership_check) (Or.inl (by ownership_check))
private theorem step_green : Step redShared meeting :=
  .greenMove redShared rfl (by ownership_check) (by ownership_check) shared (by ownership_check) (by ownership_check) (Or.inr (by rfl))
private theorem step_collision : Step meeting recovering :=
  .collision meeting rfl (by rfl) (by ownership_check)
private theorem step_pop : Step recovering popped :=
  .redPop recovering shared meeting.frame.red meeting.frame.green rfl (by ownership_check)
    (by ownership_check) (Or.inl rfl)
private theorem step_escape : Step popped escaped :=
  .redEscape popped shared meeting.frame.red meeting.frame.green rfl (by ownership_check)
    redBottom (by ownership_check) (by ownership_check) (by ownership_check) (by ownership_check)
private theorem step_bottoms : Step escaped bottoms :=
  .greenMove escaped rfl (by ownership_check) (by ownership_check) greenBottom (by ownership_check) (by ownership_check)
    (Or.inl (by ownership_check))
private theorem step_finish : Step bottoms finished :=
  .bottom bottoms rfl (by ownership_check) (by rfl) (by rfl)

/-- The ownership counterexample is resolved by the machine's red backtrack
and alternate escape, followed by two distinct bottom endpoints. -/
theorem reachable_finished : Reachable red green finished :=
  .step (.step (.step (.step (.step (.step (.step .initial step_red) step_green)
    step_collision) step_pop) step_escape) step_bottoms) step_finish

theorem finished_disjoint : finished.mode = .disjoint ∧
    finished.frame.red.ToBottom red ∧ finished.frame.green.ToBottom green ∧
    finished.frame.red.Disjoint finished.frame.green := by
  refine ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ?_⟩
  intro v hred hgreen
  cases v <;> revert hred hgreen <;> ownership_check

/-- The collision vertex remains on green's path; red uses its alternate edge. -/
theorem expected_paths :
    finished.frame.red.length = 1 ∧ finished.frame.red.last = redBottom ∧
    finished.frame.green.length = 2 ∧ finished.frame.green.last = greenBottom ∧
    finished.frame.green.Contains shared ∧ ¬ finished.frame.red.Contains shared ∧
    finished.frame.barrier = red := by ownership_check

end OwnershipExecution

namespace BottleneckExecution
open Machine

inductive Vertex where
  | red | green | candidate | below
  deriving DecidableEq, Repr
open Vertex

abbrev edge (u v : Vertex) : Prop :=
  (u = red ∧ v = candidate) ∨ (u = green ∧ v = candidate) ∨
    (u = candidate ∧ v = below)

abbrev layer : Vertex → Nat
  | red | green => 2
  | candidate => 1
  | below => 0

abbrev graph : LayeredGraph Vertex where
  Edge := edge
  level := layer
  decreases := by intro u v h; cases u <;> cases v <;> simp_all [edge, layer]

private abbrev start : State graph := Machine.initial graph red green
private abbrev redCandidate : State graph :=
  ⟨start.frame.advanceRed candidate (by change edge red candidate; simp [edge]), .normal⟩
private abbrev meeting : State graph :=
  ⟨redCandidate.frame.advanceGreen candidate (by change edge green candidate; simp [edge]), .normal⟩
private abbrev recovering : State graph :=
  { meeting with mode := .redRecovery candidate meeting.frame.red meeting.frame.green }
private abbrev redAtRoot : State graph :=
  ⟨recovering.frame.backtrackRed (by decide), recovering.mode⟩
abbrev restored : State graph :=
  ⟨redAtRoot.frame.restoreRed meeting.frame.red candidate,
    .greenRecovery candidate meeting.frame.red meeting.frame.green⟩
private abbrev greenAtRoot : State graph :=
  ⟨restored.frame.backtrackGreen (by decide), restored.mode⟩
abbrev finished : State graph :=
  { greenAtRoot with mode := .bottleneck candidate meeting.frame.red meeting.frame.green }

macro "bottleneck_check" : tactic => `(tactic|
  (dsimp [start, redCandidate, meeting, recovering, redAtRoot, restored, greenAtRoot, finished,
    Machine.initial, SearchFrame.initial, SearchFrame.advanceRed,
    SearchFrame.advanceGreen, SearchFrame.swap, SearchFrame.backtrackRed,
    SearchFrame.backtrackGreen, SearchFrame.restoreRed, Path.pop, Path.take,
    Path.snoc, Path.first, Path.last, Path.trivial, Path.Contains, graph, edge, layer]
   decide))

private theorem red_exhausted : redAtRoot.frame.Exhausted redAtRoot.frame.red.last := by
  intro v hv
  cases v <;> revert hv <;> bottleneck_check

private theorem green_exhausted : greenAtRoot.frame.Exhausted greenAtRoot.frame.green.last := by
  intro v hv
  cases v <;> revert hv <;> bottleneck_check

private theorem step_red : Step start redCandidate :=
  .redMove start rfl (by bottleneck_check) (by bottleneck_check) candidate (by bottleneck_check) (by bottleneck_check) (Or.inl (by bottleneck_check))
private theorem step_green : Step redCandidate meeting :=
  .greenMove redCandidate rfl (by bottleneck_check) (by bottleneck_check) candidate (by bottleneck_check) (by bottleneck_check) (Or.inr rfl)
private theorem step_collision : Step meeting recovering :=
  .collision meeting rfl rfl (by bottleneck_check)
private theorem step_red_pop : Step recovering redAtRoot :=
  .redPop recovering candidate meeting.frame.red meeting.frame.green rfl (by bottleneck_check)
    (by bottleneck_check) (Or.inl rfl)
private theorem step_red_fail : Step redAtRoot restored :=
  .redFail redAtRoot candidate meeting.frame.red meeting.frame.green rfl rfl (Or.inr red_exhausted)
private theorem step_green_pop : Step restored greenAtRoot :=
  .greenPop restored candidate meeting.frame.red meeting.frame.green rfl (by bottleneck_check) (Or.inl rfl)
private theorem step_green_fail : Step greenAtRoot finished :=
  .greenFail greenAtRoot candidate meeting.frame.red meeting.frame.green rfl rfl (Or.inr green_exhausted)

/-- Double exhaustion follows actual recorded scans and restores the suspended
red path before green backtracks and fails. -/
theorem reachable_finished : Reachable red green finished :=
  .step (.step (.step (.step (.step (.step (.step .initial step_red) step_green)
    step_collision) step_red_pop) step_red_fail) step_green_pop) step_green_fail

theorem restored_barrier : restored.frame.barrier = candidate ∧
    restored.frame.red.last = candidate ∧ restored.frame.red.length = 1 := by bottleneck_check

theorem stopped_before_below :
    finished.mode = .bottleneck candidate meeting.frame.red meeting.frame.green ∧
    ¬ finished.frame.visited below ∧ ¬ finished.frame.explored candidate below :=
  ⟨rfl, by bottleneck_check, by bottleneck_check⟩

/-- The candidate in the actual terminal mode is indeed the highest bottleneck
of this graph. Its lower neighbor is reached only by the semantic witness,
not explored in the execution. -/
theorem candidate_highest : HighestBottleneck graph red green candidate := by
  refine highestBottleneck_of_closed_region red green candidate finished.frame.visited
    ?_ ?_ ?_ ?_ ?_ meeting.frame.red meeting.frame.green ?_ ?_ ?_ ?_ ?_
  · bottleneck_check
  · bottleneck_check
  · intro u v hu hne he
    cases u <;> cases v <;> revert hu hne he <;> bottleneck_check
  · intro v hv hz
    cases v <;> revert hv hz <;> bottleneck_check
  · let p := (Path.trivial graph candidate).snoc below (by bottleneck_check)
    exact ⟨p, rfl, rfl⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · intro v hred hgreen
    cases v <;> revert hred hgreen <;> bottleneck_check

end BottleneckExecution
end MaximumMatching.DDFS
