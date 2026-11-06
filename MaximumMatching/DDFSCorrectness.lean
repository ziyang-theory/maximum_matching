import MaximumMatching.DDFSInvariant
import MaximumMatching.DDFSTermination

/-! Total correctness of the finite DDFS stack transition system for its two
path/bottleneck outcomes. This does not assert a globally colored pair of
spanning trees, a chosen executable edge-order implementation, or linear cost. -/
namespace MaximumMatching.DDFS.Machine
variable {V : Type} {H : LayeredGraph V}

/-- An independently stated mathematical specification of the terminal data. -/
def CorrectOutcome (r g : V) (s : State H) : Prop :=
  match s.mode with
  | .disjoint => s.frame.red.ToBottom r ∧ s.frame.green.ToBottom g ∧
      s.frame.red.Disjoint s.frame.green
  | .bottleneck b p q => HighestBottleneck H r g b ∧
      p.first = r ∧ p.last = b ∧ q.first = g ∧ q.last = b ∧
      (∀ u, p.Contains u → q.Contains u → u = b)
  | _ => False

/-- Every reachable terminal state satisfies the output specification. -/
theorem reachable_terminal_correct (hreach : ReachBottom H) {r g : V} {s : State H}
    (hs : Reachable r g s) (hterminal : Terminal s) : CorrectOutcome r g s := by
  have hi := reachable_invariant hreach hs
  cases hm : s.mode with
  | normal => simp [Terminal, hm] at hterminal
  | redRecovery b p q => simp [Terminal, hm] at hterminal
  | greenRecovery b p q => simp [Terminal, hm] at hterminal
  | disjoint => simpa only [CorrectOutcome, ModeInv, hm] using hi.mode
  | bottleneck b p q =>
    have hh : HighestBottleneck H r g b ∧ SavedPaths r g b s.frame p q := by
      simpa only [ModeInv, hm] using hi.mode
    simp only [CorrectOutcome, hm]
    exact ⟨hh.1, hh.2.red_root, hh.2.red_end, hh.2.green_root, hh.2.green_end, hh.2.meet⟩

variable {n : Nat} {H : LayeredGraph (Fin n)}

/-- A concrete finite transition trace reaches a terminal, correct outcome.
No progress or coverage invariant is supplied by the caller: both are derived
from the source's bottom-reachability requirement and initialization. -/
theorem exists_correct_run (hreach : ReachBottom H) (r g : Fin n) :
    ∃ (k : Nat) (s : State H), Trace k (initial H r g) s ∧
      Terminal s ∧ CorrectOutcome r g s := by
  obtain ⟨k, s, htrace, hstuck⟩ := reaches_stuck (initial H r g)
  have hs : Reachable r g s := htrace.reachable .initial
  have hterminal : Terminal s := by
    rcases reachable_progress hreach hs with hdone | ⟨t, hstep⟩
    · exact hdone
    · exact False.elim (hstuck t hstep)
  exact ⟨k, s, htrace, hterminal, reachable_terminal_correct hreach hs hterminal⟩

/-- Every finite maximal execution is correct, independently of edge choices. -/
theorem maximal_trace_correct (hreach : ReachBottom H) (r g : Fin n)
    {k : Nat} {s : State H} (htrace : Trace k (initial H r g) s)
    (hstuck : ∀ t, ¬Step s t) : Terminal s ∧ CorrectOutcome r g s := by
  have hs : Reachable r g s := htrace.reachable .initial
  have hterminal : Terminal s := by
    rcases reachable_progress hreach hs with hdone | ⟨t, hstep⟩
    · exact hdone
    · exact False.elim (hstuck t hstep)
  exact ⟨hterminal, reachable_terminal_correct hreach hs hterminal⟩

end MaximumMatching.DDFS.Machine
