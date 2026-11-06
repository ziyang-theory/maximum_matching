import MaximumMatching.DDFSMachine

/-! Finite termination of the explicit DDFS transition relation.
The potential counts still-unexplored ordered vertex pairs and finite stack/mode
credit. This is a coarse termination argument, not the source's linear work bound
or a machine-cost analysis of the functional state representation.
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

theorem trace_rank_bound {k : Nat} {s t : State H} (h : Trace k s t) :
    rank t + k ≤ rank s := by
  induction h with
  | refl s => simp
  | cons hs ht ih =>
    have hh := step_rank_lt hs
    omega

/-- A search cannot take more steps than its initial potential. This bound is
deliberately coarse; it does not replace the unproved linear edge/retirement bound. -/
theorem trace_length_bound {k : Nat} {s t : State H} (h : Trace k s t) : k ≤ rank s := by
  have hh := trace_rank_bound h
  omega

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
