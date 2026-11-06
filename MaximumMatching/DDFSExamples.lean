import MaximumMatching.DDFSBud
import MaximumMatching.DDFSMachine
import MaximumMatching.DDFSTrees
import MaximumMatching.RecursiveRemoval

section DDFSExamples

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

end DDFSExamples

section DDFSExecutableExamples

/-! Executable regression checks for collision restoration, abandoned branches,
and a root equal to the bottleneck. These evaluate the implementation; the
universal correctness statements are kernel-checked in DDFSExecutable and
DDFSTrees. -/
namespace MaximumMatching.DDFS.ExecutableExamples
open Machine

abbrev edgeless : LayeredGraph (Fin 2) where
  Edge := fun _ _ => False
  level := fun _ => 0
  decreases := by intro u v h; exact False.elim h

theorem edgeless_reaches : ReachBottom edgeless := by
  intro v
  exact ⟨Path.trivial edgeless v, rfl, rfl⟩

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

instance : DecidableRel edgeless.Edge := fun _ _ => inferInstanceAs (Decidable False)
def summarize {n : Nat} {H : LayeredGraph (Fin n)} {r g : Fin n} (out : FullOutput H r g) :
    Option Nat × List (Nat × Option Bool × Option Nat × Option Nat) :=
  match out with
  | .disjoint _ _ _ _ _ => (none, [])
  | .bottleneck b _ trees _ _ =>
    (some b.val, (List.finRange n).map fun v =>
      (v.val, trees.color v, (trees.red.parent v).map Fin.val, (trees.green.parent v).map Fin.val))

abbrev edge (u v : Fin 7) : Prop :=
  (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2) ∨ (u = 0 ∧ v = 3) ∨ (u = 3 ∧ v = 2) ∨
  (u = 0 ∧ v = 4) ∨ (u = 2 ∧ v = 5) ∨ (u = 4 ∧ v = 5) ∨ (u = 5 ∧ v = 6)
abbrev fixture : LayeredGraph (Fin 7) where
  Edge := edge
  level v := if v = 0 ∨ v = 1 then 4 else if v = 3 then 3 else
    if v = 2 ∨ v = 4 then 2 else if v = 5 then 1 else 0
  decreases := by
    intro u v h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
instance : DecidableRel fixture.Edge := fun u v => inferInstanceAs (Decidable (edge u v))
def p5 : Path fixture := (Path.trivial fixture 5).snoc 6 (by decide)
def p2 : Path fixture := Path.prepend 2 p5 (by decide)
def p3 : Path fixture := Path.prepend 3 p2 (by decide)
def p4 : Path fixture := Path.prepend 4 p5 (by decide)
def p0 : Path fixture := Path.prepend 0 p2 (by decide)
def p1 : Path fixture := Path.prepend 1 p2 (by decide)
theorem fixture_reaches : ReachBottom fixture := by
  intro v
  have hv : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 ∨ v.val = 3 ∨ v.val = 4 ∨ v.val = 5 ∨ v.val = 6 := by omega
  rcases hv with hv | hv | hv | hv | hv | hv | hv
  · have he : v = 0 := Fin.ext hv; subst v; exact ⟨p0, rfl, rfl⟩
  · have he : v = 1 := Fin.ext hv; subst v; exact ⟨p1, rfl, rfl⟩
  · have he : v = 2 := Fin.ext hv; subst v; exact ⟨p2, rfl, rfl⟩
  · have he : v = 3 := Fin.ext hv; subst v; exact ⟨p3, rfl, rfl⟩
  · have he : v = 4 := Fin.ext hv; subst v; exact ⟨p4, rfl, rfl⟩
  · have he : v = 5 := Fin.ext hv; subst v; exact ⟨p5, rfl, rfl⟩
  · have he : v = 6 := Fin.ext hv; subst v; exact ⟨Path.trivial fixture 6, rfl, rfl⟩

/-- info: true -/
#guard_msgs in
#eval summarize (executeFull edgeless_reaches 0 0) ==
  (some 0, [(0, none, none, none), (1, none, none, none)])

/-- info: true -/
#guard_msgs in
#eval summarize (executeFull edgeless_reaches 0 1) == (none, [])

-- Vertex 3 was visited on an abandoned branch. Its red parent must still be
-- present, although neither final saved root-to-bottleneck path contains it.
/-- info: true -/
#guard_msgs in
#eval summarize (executeFull fixture_reaches 0 1) ==
  (some 5, [(0, some false, none, none), (1, some true, none, none),
    (2, some true, none, some 1), (3, some false, some 0, none),
    (4, some false, some 0, none), (5, none, some 4, some 2),
    (6, none, none, none)])

/-- info: true -/
#guard_msgs in
#eval summarize (executeFull fixture_reaches 5 1) ==
  (some 5, [(0, none, none, none), (1, some true, none, none),
    (2, some true, none, some 1), (3, none, none, none),
    (4, none, none, none), (5, none, none, some 2), (6, none, none, none)])

/-- info: true -/
#guard_msgs in
#eval summarize (executeFull fixture_reaches 0 5) ==
  (some 5, [(0, some false, none, none), (1, none, none, none),
    (2, some false, some 0, none), (3, some false, some 0, none),
    (4, some false, some 0, none), (5, none, some 2, none), (6, none, none, none)])

end MaximumMatching.DDFS.ExecutableExamples

end DDFSExecutableExamples

section DDFSBudExamples

/-! Executable regression checks for actual DDFS-driven bud merging, including
an old descendant outside the search region and an abandoned search branch. -/
namespace MaximumMatching.DDFS.BudExamples
open Machine

def roots {n : Nat} (F : BudForest (Fin n)) : List Nat :=
  (List.finRange n).map fun v => (F.root v).val

def identityForest {n : Nat} (H : LayeredGraph (Fin n)) : BudForest (Fin n) where
  parent v := v
  rank := H.level
  decreases := by intro v hv; exact False.elim (hv rfl)

abbrev star : LayeredGraph (Fin 4) where
  Edge u v := v = 0 ∧ u ≠ 0
  level v := v.val
  decreases := by
    intro u v h
    rcases h with ⟨rfl, hu⟩
    have hupos : 0 < u.val := by
      by_cases hz : u.val = 0
      · exact False.elim (hu (Fin.ext hz))
      · omega
    exact hupos

instance : DecidableRel star.Edge := fun _ _ => inferInstanceAs (Decidable (_ = 0 ∧ _ ≠ 0))

theorem star_reaches : ReachBottom star := by
  intro v
  by_cases hv : v = 0
  · subst v
    exact ⟨Path.trivial star 0, rfl, rfl⟩
  · let p := (Path.trivial star v).snoc 0 ⟨rfl, hv⟩
    exact ⟨p, rfl, rfl⟩

-- Vertex 3 is an old descendant of root 2. It is never searched from roots
-- 1 and 2, but must move with the selected root's entire existing bud class.
def oldForest : BudForest (Fin 4) where
  parent v := if v = 3 then 2 else v
  rank v := v.val
  decreases := by
    intro v hv
    by_cases he : v = 3
    · subst v
      decide
    · exact False.elim (hv (ite_eq_right he))

/-- info: true -/
#guard_msgs in
#eval roots (executeAndContract star_reaches 2 1 oldForest).2 == [0, 0, 0, 0]

-- When only root 1 is selected, the untouched class rooted at 2 remains.
/-- info: true -/
#guard_msgs in
#eval roots (executeAndContract star_reaches 0 1 oldForest).2 == [0, 0, 2, 2]

-- The abandoned branch vertex 3 is still contracted with the full region.
/-- info: true -/
#guard_msgs in
#eval roots (executeAndContract ExecutableExamples.fixture_reaches 0 1
  (identityForest ExecutableExamples.fixture)).2 == [5, 5, 5, 5, 5, 5, 6]

-- A disjoint-path output requests no contraction.
/-- info: true -/
#guard_msgs in
#eval roots (executeAndContract ExecutableExamples.edgeless_reaches 0 1
  (identityForest ExecutableExamples.edgeless)).2 == [0, 1]

end MaximumMatching.DDFS.BudExamples

end DDFSBudExamples

section RecursiveRemovalExamples

/-! Executed recursive-removal cascade and independent surviving branch. -/
namespace MaximumMatching.DDFS.RecursiveRemoval.Examples

def graph : LayeredGraph (Fin 5) where
  Edge u v := (u = 3 ∧ v = 2) ∨ (u = 2 ∧ v = 0) ∨ (u = 4 ∧ v = 1)
  level v := if v = 3 then 2 else if v = 2 ∨ v = 4 then 1 else 0
  decreases := by
    intro u v he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

instance : DecidableRel graph.Edge := fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- Removing bottom 0 recursively removes 2 and then 3, while the separate
4-to-1 branch remains available. -/
example : (remove graph (List.finRange 5) [0]).map Fin.val = [1, 4] := by
  simp only [remove]
  rw [prune]
  change (prune graph [1, 3, 4]).map Fin.val = [1, 4]
  rw [prune]
  change (prune graph [1, 4]).map Fin.val = [1, 4]
  rw [prune]
  decide

/-- With no explicit deletion the two full bottom-reaching branches survive. -/
example : prune graph (List.finRange 5) = List.finRange 5 := by
  rw [prune]
  decide

example : ReachBottom (restricted graph (remove graph (List.finRange 5) [0])) :=
  remove_reachBottom graph _ _

end MaximumMatching.DDFS.RecursiveRemoval.Examples

end RecursiveRemovalExamples
