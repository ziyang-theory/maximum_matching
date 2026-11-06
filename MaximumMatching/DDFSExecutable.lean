import MaximumMatching.DDFSLocalWork

/-! A deterministic executable refinement of the finite DDFS stack machine.
The selector enumerates `Fin n` in order. Its predicate/path representation is
executable but no constant-time adjacency or stack-operation cost is claimed. -/
namespace MaximumMatching.DDFS.Machine
variable {n : Nat} {H : LayeredGraph (Fin n)}

/-- Deciders travel with the evolving predicates; no classical decision oracle
is used to execute visited or explored tests. -/
structure ExecutableState (H : LayeredGraph (Fin n)) where
  state : State H
  visitedDec : DecidablePred state.frame.visited
  exploredDec : DecidableRel state.frame.explored

namespace ExecutableState

def initial (H : LayeredGraph (Fin n)) (r g : Fin n) : ExecutableState H where
  state := Machine.initial H r g
  visitedDec := fun _ => inferInstanceAs (Decidable (_ = r ∨ _ = g))
  exploredDec := fun _ _ => inferInstanceAs (Decidable False)

def withMode (s : ExecutableState H) (mode : Mode H) : ExecutableState H where
  state := { s.state with mode := mode }
  visitedDec := s.visitedDec
  exploredDec := s.exploredDec

def advanceRed (s : ExecutableState H) (v : Fin n) (he : H.Edge s.state.frame.red.last v)
    (mode : Mode H) : ExecutableState H where
  state := ⟨s.state.frame.advanceRed v he, mode⟩
  visitedDec := fun u => @instDecidableOr _ _ (inferInstanceAs (Decidable (u = v))) (s.visitedDec u)
  exploredDec := fun u w => @instDecidableOr _ _
    (inferInstanceAs (Decidable (u = s.state.frame.red.last ∧ w = v))) (s.exploredDec u w)

def advanceGreen (s : ExecutableState H) (v : Fin n) (he : H.Edge s.state.frame.green.last v)
    (mode : Mode H) : ExecutableState H where
  state := ⟨s.state.frame.advanceGreen v he, mode⟩
  visitedDec := fun u => @instDecidableOr _ _ (inferInstanceAs (Decidable (u = v))) (s.visitedDec u)
  exploredDec := fun u w => @instDecidableOr _ _
    (inferInstanceAs (Decidable (u = s.state.frame.green.last ∧ w = v))) (s.exploredDec u w)

def scanRed (s : ExecutableState H) (v : Fin n) : ExecutableState H where
  state := ⟨s.state.frame.scanRed v, s.state.mode⟩
  visitedDec := s.visitedDec
  exploredDec := fun u w => @instDecidableOr _ _
    (inferInstanceAs (Decidable (u = s.state.frame.red.last ∧ w = v))) (s.exploredDec u w)

def scanGreen (s : ExecutableState H) (v : Fin n) : ExecutableState H where
  state := ⟨s.state.frame.scanGreen v, s.state.mode⟩
  visitedDec := s.visitedDec
  exploredDec := fun u w => @instDecidableOr _ _
    (inferInstanceAs (Decidable (u = s.state.frame.green.last ∧ w = v))) (s.exploredDec u w)

def popRed (s : ExecutableState H) (hpos : 0 < s.state.frame.red.length) : ExecutableState H where
  state := ⟨s.state.frame.backtrackRed hpos, s.state.mode⟩
  visitedDec := s.visitedDec
  exploredDec := s.exploredDec

def popGreen (s : ExecutableState H) (hpos : 0 < s.state.frame.green.length) : ExecutableState H where
  state := ⟨s.state.frame.backtrackGreen hpos, s.state.mode⟩
  visitedDec := s.visitedDec
  exploredDec := s.exploredDec

def restoreRed (s : ExecutableState H) (b : Fin n) (p q : Path H) : ExecutableState H where
  state := ⟨s.state.frame.restoreRed p b, .greenRecovery b p q⟩
  visitedDec := s.visitedDec
  exploredDec := s.exploredDec

private def selectWitness {A : Type} (P : A → Prop) [DecidablePred P] :
    List A → Option {v : A // P v}
  | [] => none
  | v :: vs => if hv : P v then some ⟨v, hv⟩ else selectWitness P vs

private theorem selectWitness_none {A : Type} (P : A → Prop) [DecidablePred P]
    (xs : List A) (h : selectWitness P xs = none) : ∀ v ∈ xs, ¬P v := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [selectWitness] at h
    split at h
    · contradiction
    next ha =>
      intro v hv
      rcases List.mem_cons.mp hv with hv | hv
      · exact hv ▸ ha
      · exact ih h v hv

/-- Choose the first unscanned outgoing neighbor in increasing vertex order. -/
def selectEdge [DecidableRel H.Edge] (s : ExecutableState H) (u : Fin n) :
    Option {v : Fin n // H.Edge u v ∧ ¬s.state.frame.explored u v} := by
  letI := s.exploredDec
  exact selectWitness (fun v => H.Edge u v ∧ ¬s.state.frame.explored u v) (List.finRange n)

theorem selectEdge_none [DecidableRel H.Edge] (s : ExecutableState H) (u : Fin n)
    (h : s.selectEdge u = none) : s.state.frame.Exhausted u := by
  letI := s.exploredDec
  have hn := selectWitness_none (fun v => H.Edge u v ∧ ¬s.state.frame.explored u v)
    (List.finRange n) h
  intro v he
  by_cases hx : s.state.frame.explored u v
  · exact hx
  · exact False.elim (hn v (List.mem_finRange v) ⟨he, hx⟩)

end ExecutableState

/-- Every selected continuation carries an actual machine transition; stopping
carries a terminal-state proof. -/
inductive Next (s : ExecutableState H) where
  | terminal : Terminal s.state → Next s
  | step (t : ExecutableState H) : Step s.state t.state → Next s

private theorem positive_of_barrier {s : State H} (hb : s.frame.BarrierSafe)
    (hne : s.frame.red.last ≠ s.frame.barrier) : 0 < s.frame.red.length := by
  obtain ⟨i, hi⟩ := hb.1
  by_cases hp : 0 < s.frame.red.length
  · exact hp
  · have he : i = ⟨s.frame.red.length, by omega⟩ := Fin.ext (by have := i.isLt; omega)
    exact False.elim (hne (by rw [he] at hi; exact hi))

private def retireRed (s : ExecutableState H) (b : Fin n) (p q : Path H)
    (hm : s.state.mode = .redRecovery b p q) (hb : s.state.frame.BarrierSafe)
    (hex : s.state.frame.red.last = b ∨ s.state.frame.Exhausted s.state.frame.red.last) : Next s :=
  if hbar : s.state.frame.red.last = s.state.frame.barrier then
    .step (s.restoreRed b p q) (.redFail s.state b p q hm hbar hex)
  else
    .step (s.popRed (positive_of_barrier hb hbar))
      (.redPop s.state b p q hm (positive_of_barrier hb hbar) hbar hex)

private def retireGreen (s : ExecutableState H) (b : Fin n) (p q : Path H)
    (hm : s.state.mode = .greenRecovery b p q)
    (hex : s.state.frame.green.last = b ∨ s.state.frame.Exhausted s.state.frame.green.last) : Next s :=
  if hz : s.state.frame.green.length = 0 then
    .step (s.withMode (.bottleneck b p q)) (.greenFail s.state b p q hm hz hex)
  else
    .step (s.popGreen (by omega)) (.greenPop s.state b p q hm (by omega) hex)

private theorem positive_out_edge (hreach : ReachBottom H) (u : Fin n)
    (hpos : 0 < H.level u) : ∃ v, H.Edge u v := by
  obtain ⟨p, hpu, hp0⟩ := hreach u
  have hl : 0 < p.length := by
    by_cases hz : p.length = 0
    · have he : p.first = p.last := congrArg p.vertex (Fin.ext (by omega))
      rw [← hpu, he, hp0] at hpos
      omega
    · omega
  refine ⟨p.vertex ⟨1, by omega⟩, ?_⟩
  have he := p.adjacent ⟨0, hl⟩
  change H.Edge p.first (p.vertex ⟨1, by omega⟩) at he
  rwa [hpu] at he

/-- Deterministic case analysis of the actual DDFS control rules. Reachability
is used only in erased proofs, never as a search or choice oracle. -/
def next [DecidableRel H.Edge] (hreach : ReachBottom H) (r g : Fin n)
    (s : ExecutableState H) (hs : Reachable r g s.state) : Next s := by
  letI := s.visitedDec
  have hi := reachable_invariant hreach hs
  cases hm : s.state.mode with
  | normal =>
    have hn : s.state.frame.NormalSafe ∧ s.state.frame.CollisionDepth := by
      simpa only [ModeInv, hm] using hi.mode
    by_cases hmeet : s.state.frame.red.last = s.state.frame.green.last
    · by_cases hroots : s.state.frame.red.first = s.state.frame.green.first
      · have hgin : s.state.frame.green.Contains s.state.frame.red.first := by
          rw [hroots]; exact s.state.frame.green.contains_first
        have hh := hn.1.separated s.state.frame.red.first s.state.frame.red.contains_first hgin
        have hr : s.state.frame.red.length = 0 := by
          have he := congrArg Fin.val (s.state.frame.red.injective ⟨0, by omega⟩
            ⟨s.state.frame.red.length, by omega⟩ hh.1)
          change 0 = s.state.frame.red.length at he
          omega
        have hg : s.state.frame.green.length = 0 := by
          have he := congrArg Fin.val (s.state.frame.green.injective ⟨0, by omega⟩
            ⟨s.state.frame.green.length, by omega⟩ (hroots.symm.trans hh.2))
          change 0 = s.state.frame.green.length at he
          omega
        exact .step (s.withMode (.bottleneck s.state.frame.red.last s.state.frame.red s.state.frame.green))
          (.sameRoot s.state hm hr hg hmeet)
      · exact .step (s.withMode (.redRecovery s.state.frame.red.last s.state.frame.red s.state.frame.green))
          (.collision s.state hm hmeet hroots)
    · by_cases hb : H.level s.state.frame.red.last = 0 ∧ H.level s.state.frame.green.last = 0
      · exact .step (s.withMode .disjoint) (.bottom s.state hm hmeet hb.1 hb.2)
      · by_cases horder : H.level s.state.frame.green.last ≤ H.level s.state.frame.red.last
        · cases he : s.selectEdge s.state.frame.red.last with
          | none =>
            have hex := s.selectEdge_none s.state.frame.red.last he
            have hf : False := by
              obtain ⟨v, hedge⟩ := positive_out_edge hreach s.state.frame.red.last (by omega)
              exact hn.1.red_unexpanded v (hex v hedge)
            exact False.elim hf
          | some e =>
            have hv : ¬s.state.frame.visited e.val ∨ e.val = s.state.frame.green.last := by
              by_cases hvis : s.state.frame.visited e.val
              · exact Or.inr (s.state.frame.visited_red_target hn.1.depth horder e.property.1 hvis)
              · exact Or.inl hvis
            exact .step (s.advanceRed e.val e.property.1 .normal)
              (.redMove s.state hm hmeet horder e.val e.property.1 e.property.2 hv)
        · cases he : s.selectEdge s.state.frame.green.last with
          | none =>
            have hex := s.selectEdge_none s.state.frame.green.last he
            have hf : False := by
              obtain ⟨v, hedge⟩ := positive_out_edge hreach s.state.frame.green.last (by omega)
              exact hn.1.green_unexpanded v (hex v hedge)
            exact False.elim hf
          | some e =>
            have hv : ¬s.state.frame.visited e.val ∨ e.val = s.state.frame.red.last := by
              by_cases hvis : s.state.frame.visited e.val
              · exact Or.inr (s.state.frame.swap.visited_red_target (s.state.frame.swap_safe hn.1).depth
                  (by change H.level s.state.frame.red.last ≤ H.level s.state.frame.green.last; omega) e.property.1 hvis)
              · exact Or.inl hvis
            exact .step (s.advanceGreen e.val e.property.1 .normal)
              (.greenMove s.state hm hmeet (by omega) e.val e.property.1 e.property.2 hv)
  | redRecovery b p q =>
    have hr : s.state.frame.RecoverySafe b ∧ s.state.frame.green = q ∧ SavedPaths r g b s.state.frame p q := by
      simpa only [ModeInv, hm] using hi.mode
    by_cases heq : s.state.frame.red.last = b
    · exact retireRed s b p q hm hi.basic.barrier (Or.inl heq)
    · cases he : s.selectEdge s.state.frame.red.last with
      | none => exact retireRed s b p q hm hi.basic.barrier (Or.inr (s.selectEdge_none _ he))
      | some e =>
        have hh := hr.1.depth s.state.frame.red.last (hr.1.red_visited _ s.state.frame.red.contains_last) heq
        by_cases hv : s.state.frame.visited e.val
        · exact .step (s.scanRed e.val) (.redSkip s.state b p q hm hh e.val e.property.1 e.property.2 hv)
        · by_cases hl : H.level b < H.level e.val
          · exact .step (s.advanceRed e.val e.property.1 s.state.mode)
              (.redDeeper s.state b p q hm hh e.val e.property.1 e.property.2 hv hl)
          · exact .step (s.advanceRed e.val e.property.1 .normal)
              (.redEscape s.state b p q hm hh e.val e.property.1 e.property.2 hv (by omega))
  | greenRecovery b p q =>
    have hg : s.state.frame.swap.RecoverySafe b ∧ s.state.frame.red = p ∧ s.state.frame.barrier = b ∧
        SavedPaths r g b s.state.frame p q := by simpa only [ModeInv, hm] using hi.mode
    by_cases heq : s.state.frame.green.last = b
    · exact retireGreen s b p q hm (Or.inl heq)
    · cases he : s.selectEdge s.state.frame.green.last with
      | none => exact retireGreen s b p q hm (Or.inr (s.selectEdge_none _ he))
      | some e =>
        have hh := hg.1.depth s.state.frame.green.last (hg.1.red_visited _ s.state.frame.green.contains_last) heq
        by_cases hv : s.state.frame.visited e.val
        · exact .step (s.scanGreen e.val) (.greenSkip s.state b p q hm hh e.val e.property.1 e.property.2 hv)
        · by_cases hl : H.level b < H.level e.val
          · exact .step (s.advanceGreen e.val e.property.1 s.state.mode)
              (.greenDeeper s.state b p q hm hh e.val e.property.1 e.property.2 hv hl)
          · exact .step (s.advanceGreen e.val e.property.1 .normal)
              (.greenEscape s.state b p q hm hh e.val e.property.1 e.property.2 hv (by omega))
  | disjoint => exact .terminal (Or.inl hm)
  | bottleneck b p q => exact .terminal (Or.inr ⟨b, p, q, hm⟩)

/-- The actual final state and counted trace produced by the deterministic run. -/
structure Execution (s : ExecutableState H) where
  finalState : ExecutableState H
  steps : Nat
  trace : Trace steps s.state finalState.state
  terminal : Terminal finalState.state

/-- Execute the selected transitions until a terminal state. The finite-state
rank is used only to justify termination, not evaluated by the program. -/
def executeFrom [DecidableRel H.Edge] (hreach : ReachBottom H) (r g : Fin n)
    (s : ExecutableState H) (hs : Reachable r g s.state) : Execution s :=
  match next hreach r g s hs with
  | .terminal hdone => ⟨s, 0, .refl s.state, hdone⟩
  | .step t hstep =>
    let out := executeFrom hreach r g t (.step hs hstep)
    ⟨out.finalState, out.steps + 1, .cons hstep out.trace, out.terminal⟩
termination_by rank s.state
decreasing_by exact step_rank_lt hstep

/-- An executable DDFS search, with finite increasing-order edge enumeration. -/
def execute [DecidableRel H.Edge] (hreach : ReachBottom H) (r g : Fin n) :
    Execution (ExecutableState.initial H r g) :=
  executeFrom hreach r g (ExecutableState.initial H r g) .initial

theorem execute_correct [DecidableRel H.Edge] (hreach : ReachBottom H) (r g : Fin n) :
    CorrectOutcome r g (execute hreach r g).finalState.state :=
  reachable_terminal_correct hreach ((execute hreach r g).trace.reachable .initial)
    (execute hreach r g).terminal

/-- The executable selector inherits the abstract transition bound. Its linear
vertex enumeration per edge-selection attempt is not asserted constant-time. -/
theorem execute_steps_bound [DecidableRel H.Edge] (hreach : ReachBottom H) (r g : Fin n) :
    (execute hreach r g).steps ≤ 4 * edgeCount H + 3 :=
  trace_linear_bound hreach r g (execute hreach r g).trace

theorem execute_scanned_bound [DecidableRel H.Edge] (hreach : ReachBottom H) (r g : Fin n) :
    (execute hreach r g).steps ≤
      4 * scannedEdges (execute hreach r g).finalState.state.frame + 3 := by
  have h := trace_scanned_bound hreach r g (execute hreach r g).trace
  omega

end MaximumMatching.DDFS.Machine
