import MaximumMatching.DDFSTrees

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
