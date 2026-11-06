import MaximumMatching.DDFSInvariant
import MaximumMatching.DDFSMachine

section DDFSTermination

/-! Finite termination of the explicit DDFS transition relation.
The potential counts still-unexplored ordered vertex pairs and finite stack/mode
credit. Strict decrease of this natural-valued rank proves that every
execution terminates.
-/
namespace MaximumMatching.DDFS

theorem Path.length_lt_vertices {n : Nat} {H : LayeredGraph (Fin n)} (p : Path H) :
    p.length < n := by
  have hd : ((List.finRange (p.length + 1)).map p.vertex).Nodup :=
    (List.nodup_finRange _).map p.vertex (fun i j h hij => h (p.injective _ _ hij))
  have hl := hd.length_le_of_subset (l₂ := List.finRange n) (fun v _ => List.mem_finRange v)
  simp only [List.length_map, List.length_finRange] at hl
  omega

namespace Machine
variable {n : Nat} {H : LayeredGraph (Fin n)}

def vertexPairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => (u, v)

theorem mem_vertexPairs (u v : Fin n) : (u, v) ∈ vertexPairs n := by
  exact List.mem_flatMap.mpr ⟨u, List.mem_finRange u,
    List.mem_map.mpr ⟨v, List.mem_finRange v, rfl⟩⟩

noncomputable def remaining (s : SearchFrame H) : Nat := by
  classical
  exact (vertexPairs n).countP fun e => decide (¬s.explored e.1 e.2)

def credit (m : Mode H) : Nat :=
  match m with
  | .normal => 2 * n + 3
  | .redRecovery .. => n + 2
  | .greenRecovery .. => 1
  | .disjoint | .bottleneck .. => 0

def localRank (s : State H) : Nat :=
  s.frame.red.length + s.frame.green.length + credit s.mode

noncomputable def rank (s : State H) : Nat :=
  remaining s.frame * (4 * n + 6) + localRank s

theorem localRank_lt (s : State H) : localRank s < 4 * n + 6 := by
  have hr := s.frame.red.length_lt_vertices
  have hg := s.frame.green.length_lt_vertices
  unfold localRank credit
  split <;> omega

private theorem countP_strict {A : Type} (xs : List A) (p q : A → Bool)
    (hle : ∀ a ∈ xs, p a = true → q a = true)
    (hex : ∃ a, a ∈ xs ∧ p a = false ∧ q a = true) : xs.countP p < xs.countP q := by
  induction xs with
  | nil => simp at hex
  | cons a xs ih =>
    obtain ⟨b, hb, hbp, hbq⟩ := hex
    have htail : ∀ x ∈ xs, p x = true → q x = true := fun x hx => hle x (List.mem_cons_of_mem _ hx)
    rcases List.mem_cons.mp hb with he | hb
    · subst b
      have hh := List.countP_mono_left htail
      simp only [List.countP_cons, hbp, hbq, Bool.false_eq_true, ↓reduceIte]
      omega
    · have hh := ih htail ⟨b, hb, hbp, hbq⟩
      have ha := hle a (List.mem_cons_self)
      rw [List.countP_cons, List.countP_cons]
      cases hpa : p a <;> cases hqa : q a <;> simp_all <;> omega

/-- Marking any genuinely new scan strictly consumes the finite pair budget. -/
theorem remaining_mark_lt (s t : SearchFrame H) (u v : Fin n)
    (hu : ¬s.explored u v)
    (hmark : ∀ a b, t.explored a b ↔ (a = u ∧ b = v) ∨ s.explored a b) :
    remaining t < remaining s := by
  classical
  unfold remaining
  apply countP_strict
  · intro e _ he
    simp only [decide_eq_true_eq] at he ⊢
    intro hs
    exact he ((hmark e.1 e.2).2 (Or.inr hs))
  · refine ⟨(u, v), mem_vertexPairs u v, ?_, ?_⟩
    · simp only [decide_eq_false_iff_not]
      intro hn
      exact hn ((hmark u v).2 (Or.inl ⟨rfl, rfl⟩))
    · simp only [decide_eq_true_eq]
      exact hu

theorem rank_lt_of_scan (s t : State H) (u v : Fin n)
    (hu : ¬s.frame.explored u v)
    (hmark : ∀ a b, t.frame.explored a b ↔ (a = u ∧ b = v) ∨ s.frame.explored a b) :
    rank t < rank s := by
  have he := remaining_mark_lt s.frame t.frame u v hu hmark
  have hl := localRank_lt t
  have hm := Nat.mul_le_mul_right (4 * n + 6) (show remaining t.frame + 1 ≤ remaining s.frame by omega)
  simp only [Nat.add_mul, Nat.one_mul] at hm
  unfold rank
  omega

/-- Every actual transition strictly decreases the potential. Restoration is
paid for by switching from red-recovery credit to green-recovery credit. -/
theorem step_rank_lt {s t : State H} (h : Step s t) : rank t < rank s := by
  cases h with
  | sameRoot hn hr hg heq =>
    simp only [rank, localRank, hn, credit]
    omega
  | redMove hn hne hsched v he hu hv =>
    apply rank_lt_of_scan s _ s.frame.red.last v hu
    intro a b
    rfl
  | greenMove hn hne hsched v he hu hv =>
    apply rank_lt_of_scan s _ s.frame.green.last v hu
    intro a b
    rfl
  | bottom hn hne hr hg =>
    simp only [rank, localRank, hn, credit]
    omega
  | collision hn heq hroots =>
    simp only [rank, localRank, hn, credit]
    omega
  | redPop b p q hm hpos hbar hex =>
    change remaining s.frame * (4*n+6) +
      ((s.frame.red.length - 1) + s.frame.green.length + credit s.mode) < rank s
    unfold rank localRank
    omega
  | redSkip b p q hm hhigh v he hu hv =>
    apply rank_lt_of_scan s _ s.frame.red.last v hu
    intro a b
    rfl
  | redDeeper b p q hm hhigh v he hu hv hvhigh =>
    apply rank_lt_of_scan s _ s.frame.red.last v hu
    intro a b
    rfl
  | redEscape b p q hm hhigh v he hu hv hvlow =>
    apply rank_lt_of_scan s _ s.frame.red.last v hu
    intro a b
    rfl
  | redFail b p q hm hbar hex =>
    have hp := p.length_lt_vertices
    change remaining s.frame * (4*n+6) +
      (p.length + s.frame.green.length + 1) < rank s
    simp only [rank, localRank, hm, credit]
    omega
  | greenPop b p q hm hpos hex =>
    change remaining s.frame * (4*n+6) +
      (s.frame.red.length + (s.frame.green.length - 1) + credit s.mode) < rank s
    unfold rank localRank
    omega
  | greenSkip b p q hm hhigh v he hu hv =>
    apply rank_lt_of_scan s _ s.frame.green.last v hu
    intro a b
    rfl
  | greenDeeper b p q hm hhigh v he hu hv hvhigh =>
    apply rank_lt_of_scan s _ s.frame.green.last v hu
    intro a b
    rfl
  | greenEscape b p q hm hhigh v he hu hv hvlow =>
    apply rank_lt_of_scan s _ s.frame.green.last v hu
    intro a b
    rfl
  | greenFail b p q hm hroot hex =>
    simp only [rank, localRank, hm, credit]
    omega

/-- There is no infinite transition sequence on a finite vertex set. This
does not assert that a stuck state is terminal; that is the progress invariant. -/
theorem no_infinite_run (states : Nat → State H)
    (hstep : ∀ i, Step (states i) (states (i + 1))) : False := by
  have bound : ∀ i, rank (states i) + i ≤ rank (states 0) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hh := step_rank_lt (hstep i)
      omega
  have hh := bound (rank (states 0) + 1)
  omega

/-- The number of transitions in an actual finite execution. -/
inductive Trace : Nat → State H → State H → Prop where
  | refl (s : State H) : Trace 0 s s
  | cons {k : Nat} {s t u : State H} : Step s t → Trace k t u → Trace (k + 1) s u

theorem step_wellFounded : WellFounded (fun t s : State H => Step s t) :=
  Subrelation.wf (fun h => step_rank_lt h) (measure rank).wf

/-- Every state has a finite execution ending with no available transition.
Identifying that final state as a correct terminal outcome requires the separate
reachable-state progress theorem; no such identification is assumed here. -/
theorem reaches_stuck (s : State H) :
    ∃ (k : Nat) (t : State H), Trace k s t ∧ ∀ u, ¬ Step t u := by
  classical
  by_cases hex : ∃ t, Step s t
  · obtain ⟨t, hst⟩ := hex
    obtain ⟨k, u, htu, hu⟩ := reaches_stuck t
    exact ⟨k + 1, u, .cons hst htu, hu⟩
  · exact ⟨0, s, .refl s, fun u hsu => hex ⟨u, hsu⟩⟩
termination_by rank s
decreasing_by exact step_rank_lt hst

theorem Trace.reachable {r g : Fin n} {k : Nat} {s t : State H}
    (h : Trace k s t) (hs : Reachable r g s) : Reachable r g t := by
  induction h with
  | refl s => exact hs
  | cons hst htu ih => exact ih (.step hs hst)

end Machine
end MaximumMatching.DDFS

end DDFSTermination

section DDFSCorrectness

/-! Total correctness of the finite DDFS stack transition system for its two
path/bottleneck outcomes. This does not assert a globally colored pair of
spanning trees or a chosen executable edge-order implementation. -/
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

end DDFSCorrectness

section DDFSVisited

/-! The visited region of a completed bottleneck search is exactly the set of
vertices on root-to-bottleneck paths. Discovery provenance and terminal closure
are derived from actual reachability of the machine state. -/
namespace MaximumMatching.DDFS
variable {V : Type} {H : LayeredGraph V}

/-- Vertex membership in the union of all paths from either root to `b`. -/
def OnRootTo (r g b u : V) : Prop :=
  ∃ p : Path H, (p.first = r ∨ p.first = g) ∧ p.last = b ∧ p.Contains u

namespace SearchFrame

def SeenReachable (r g : V) (s : SearchFrame H) : Prop :=
  ∀ u, s.visited u → ∃ p : Path H, (p.first = r ∨ p.first = g) ∧ p.last = u

theorem initial_seen_reachable (r g : V) : (initial H r g).SeenReachable r g := by
  intro u hu
  rcases hu with hu | hu
  · exact ⟨Path.trivial H r, Or.inl rfl, hu.symm⟩
  · exact ⟨Path.trivial H g, Or.inr rfl, hu.symm⟩

theorem advanceRed_seen_reachable (s : SearchFrame H) (hs : s.SeenReachable r g)
    (hr : s.red.first = r) (v : V) (he : H.Edge s.red.last v) :
    (s.advanceRed v he).SeenReachable r g := by
  intro u hu
  rcases hu with hu | hu
  · exact ⟨s.red.snoc v he, Or.inl ((s.red.snoc_first v he).trans hr),
      (s.red.snoc_last v he).trans hu.symm⟩
  · exact hs u hu

theorem advanceGreen_seen_reachable (s : SearchFrame H) (hs : s.SeenReachable r g)
    (hg : s.green.first = g) (v : V) (he : H.Edge s.green.last v) :
    (s.advanceGreen v he).SeenReachable r g := by
  intro u hu
  rcases hu with hu | hu
  · exact ⟨s.green.snoc v he, Or.inr ((s.green.snoc_first v he).trans hg),
      (s.green.snoc_last v he).trans hu.symm⟩
  · exact hs u hu

end SearchFrame
namespace Machine

theorem step_seen_reachable {r g : V} {s t : State H}
    (hi : Invariant r g s) (hs : s.frame.SeenReachable r g) (he : Step s t) :
    t.frame.SeenReachable r g := by
  cases he with
  | redMove _ _ _ v hedge _ _ => exact s.frame.advanceRed_seen_reachable hs hi.basic.red_root v hedge
  | greenMove _ _ _ v hedge _ _ => exact s.frame.advanceGreen_seen_reachable hs hi.basic.green_root v hedge
  | redDeeper _ _ _ _ _ v hedge _ _ _ => exact s.frame.advanceRed_seen_reachable hs hi.basic.red_root v hedge
  | redEscape _ _ _ _ _ v hedge _ _ _ => exact s.frame.advanceRed_seen_reachable hs hi.basic.red_root v hedge
  | greenDeeper _ _ _ _ _ v hedge _ _ _ => exact s.frame.advanceGreen_seen_reachable hs hi.basic.green_root v hedge
  | greenEscape _ _ _ _ _ v hedge _ _ _ => exact s.frame.advanceGreen_seen_reachable hs hi.basic.green_root v hedge
  | _ => exact hs

/-- Every visited vertex has an actual discovery path from one of the roots. -/
theorem reachable_seen_reachable (hreach : ReachBottom H) {r g : V} {s : State H}
    (hs : Reachable r g s) : s.frame.SeenReachable r g := by
  induction hs with
  | initial => exact SearchFrame.initial_seen_reachable r g
  | step hr hstep ih => exact step_seen_reachable (reachable_invariant hreach hr) ih hstep

private theorem contains_eq_last_of_zero (p : Path H) (hp : p.length = 0)
    (u : V) (hu : p.Contains u) : u = p.last := by
  obtain ⟨i, hi⟩ := hu
  have he : i = ⟨p.length, by omega⟩ := Fin.ext (by have := i.isLt; omega)
  rw [he] at hi
  exact hi.symm

/-- Both terminal-region facts are derived at the actual terminating transition:
closure away from the bottleneck and strict depth above it. -/
theorem reachable_bottleneck_region (hreach : ReachBottom H) {r g b : V}
    {s : State H} {p q : Path H} (hs : Reachable r g s)
    (hmode : s.mode = .bottleneck b p q) :
    ClosedExcept (H := H) s.frame.visited b ∧
      ∀ u, s.frame.visited u → u ≠ b → H.level b < H.level u := by
  cases hs with
  | initial => cases hmode
  | @step s t hprev hstep =>
    have hi := reachable_invariant hreach hprev
    cases hstep with
    | sameRoot hn hr hg heq =>
      cases hmode
      have hnormal : s.frame.NormalSafe ∧ s.frame.CollisionDepth := by
        simpa only [ModeInv, hn] using hi.mode
      refine ⟨?_, hnormal.2 heq⟩
      intro u v hseen hne hedge
      have hdone : s.frame.Exhausted u := by
        rcases hi.basic.covered u hseen with hd | hred | hgreen
        · exact hd
        · exact False.elim (hne (contains_eq_last_of_zero s.frame.red hr u hred))
        · exact False.elim (hne ((contains_eq_last_of_zero s.frame.green hg u hgreen).trans heq.symm))
      exact hi.basic.targets u v (hdone v hedge)
    | greenFail b0 p0 q0 hm hroot hex =>
      cases hmode
      have hrec : s.frame.swap.RecoverySafe b ∧ s.frame.red = p ∧ s.frame.barrier = b ∧
          SavedPaths r g b s.frame p q := by simpa only [ModeInv, hm] using hi.mode
      refine ⟨?_, hrec.1.depth⟩
      have hrend : s.frame.red.last = b := hrec.2.1 ▸ hrec.2.2.2.red_end
      apply s.frame.closure_at_double_exhaustion hi.basic.covered hi.basic.barrier hi.basic.targets b
        hrend hrec.2.2.1
      intro u hu hn
      have he := contains_eq_last_of_zero s.frame.green hroot u hu
      rcases hex with hb | hd
      · exact False.elim (hn (he.trans hb))
      · exact he ▸ hd
    | redMove => cases hmode
    | greenMove => cases hmode
    | bottom => cases hmode
    | collision => cases hmode
    | redPop _ _ _ hm _ _ _ => rw [hm] at hmode; cases hmode
    | redSkip _ _ _ hm _ _ _ _ _ => rw [hm] at hmode; cases hmode
    | redDeeper _ _ _ hm _ _ _ _ _ _ => rw [hm] at hmode; cases hmode
    | redEscape => cases hmode
    | redFail => cases hmode
    | greenPop _ _ _ hm _ _ => rw [hm] at hmode; cases hmode
    | greenSkip _ _ _ hm _ _ _ _ _ => rw [hm] at hmode; cases hmode
    | greenDeeper _ _ _ hm _ _ _ _ _ _ => rw [hm] at hmode; cases hmode
    | greenEscape => cases hmode

private theorem path_stays_until_last (p : Path H) (S : V → Prop) (b : V)
    (hclosed : ClosedExcept (H := H) S b) (hfirst : S p.first) (hlast : p.last = b) :
    ∀ i, S (p.vertex i) := by
  have aux : ∀ k (hk : k < p.length + 1), S (p.vertex ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero => intro hk; exact hfirst
    | succ k ih =>
      intro hk
      apply hclosed _ _ (ih (by omega))
      · intro he
        have hi := p.injective ⟨k, by omega⟩ ⟨p.length, by omega⟩ (he.trans hlast.symm)
        have hv : k = p.length := congrArg (fun i : Fin (p.length + 1) => i.val) hi
        omega
      · exact p.adjacent ⟨k, by omega⟩
  intro i
  exact aux i.val i.isLt

/-- At a reported bottleneck, the machine has visited exactly every vertex on
any root-to-bottleneck path. No discovery or coverage predicate is an assumption. -/
theorem visited_iff_on_root_to_bottleneck (hreach : ReachBottom H) {r g b : V}
    {s : State H} {p q : Path H} (hs : Reachable r g s)
    (hmode : s.mode = .bottleneck b p q) (u : V) :
    s.frame.visited u ↔ OnRootTo (H := H) r g b u := by
  have hi := reachable_invariant hreach hs
  have hout : HighestBottleneck H r g b ∧ SavedPaths r g b s.frame p q := by
    simpa only [ModeInv, hmode] using hi.mode
  obtain ⟨hclosed, hdepth⟩ := reachable_bottleneck_region hreach hs hmode
  constructor
  · intro hu
    obtain ⟨a, ha, hau⟩ := reachable_seen_reachable hreach hs u hu
    by_cases hub : u = b
    · exact ⟨a, ha, hau.trans hub, hau ▸ a.contains_last⟩
    · have hhigh := hdepth u hu hub
      obtain ⟨z, hzu, hz0⟩ := hreach u
      have hjoin : a.last = z.first := hau.trans hzu.symm
      have hfull : (a.append z hjoin).ToBottom r ∨ (a.append z hjoin).ToBottom g := by
        rcases ha with ha | ha
        · exact Or.inl ⟨(a.append_first z hjoin).trans ha, by rw [a.append_last]; exact hz0⟩
        · exact Or.inr ⟨(a.append_first z hjoin).trans ha, by rw [a.append_last]; exact hz0⟩
      have hbfull := hout.1.1 (a.append z hjoin) hfull
      have hbz : z.Contains b := by
        rcases (Path.contains_append_iff a z hjoin b).1 hbfull with hba | hbz
        · have hlow := a.last_level_le hba
          rw [hau] at hlow
          omega
        · exact hbz
      obtain ⟨j, hj⟩ := hbz
      let tail := z.take j.val (by omega)
      have hjn : a.last = tail.first := hjoin
      refine ⟨a.append tail hjn, ?_, ?_, ?_⟩
      · rw [a.append_first]
        exact ha
      · rw [a.append_last]
        exact hj
      · exact (Path.contains_append_iff a tail hjn u).2 (Or.inl (hau ▸ a.contains_last))
  · rintro ⟨a, ha, hab, ⟨i, hi⟩⟩
    have hrseen : s.frame.visited r := hout.2.red_root ▸ hout.2.red_seen p.first p.contains_first
    have hgseen : s.frame.visited g := hout.2.green_root ▸ hout.2.green_seen q.first q.contains_first
    have hfirst : s.frame.visited a.first := by
      rcases ha with ha | ha
      · exact ha ▸ hrseen
      · exact ha ▸ hgseen
    exact hi ▸ path_stays_until_last a s.frame.visited b hclosed hfirst hab i

end Machine
end MaximumMatching.DDFS

end DDFSVisited

section DDFSExecutable

/-! A deterministic executable refinement of the finite DDFS stack machine.
The selector enumerates `Fin n` in order and carries decidable state
predicates through every actual transition. -/
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

end MaximumMatching.DDFS.Machine

end DDFSExecutable
