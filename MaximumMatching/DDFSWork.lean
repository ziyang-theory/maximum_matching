import MaximumMatching.DDFSCorrectness

/-! Linear accounting for the abstract DDFS transition system. Each edge scan
and each stack/control transition is one operation. This does not assign a
constant machine cost to the functional path or predicate representation. -/
namespace MaximumMatching.DDFS
namespace Path
variable {V : Type} {H : LayeredGraph V}

/-- The number of stack edges strictly below a specified vertex. The value is
zero when that vertex is absent; reachable machine states contain Barrier. -/
noncomputable def tailDepth (p : Path H) (b : V) : Nat := by
  classical
  exact if h : p.Contains b then p.length - (Classical.choose h).val else 0

theorem tailDepth_eq (p : Path H) (b : V) (i : Fin (p.length + 1))
    (hi : p.vertex i = b) : p.tailDepth b = p.length - i.val := by
  classical
  have h : p.Contains b := ⟨i, hi⟩
  have he : Classical.choose h = i := p.injective _ _ ((Classical.choose_spec h).trans hi.symm)
  simp only [tailDepth, dite_eq_left h, he]

@[simp] theorem tailDepth_last (p : Path H) : p.tailDepth p.last = 0 := by
  rw [p.tailDepth_eq p.last ⟨p.length, by omega⟩ rfl]
  exact Nat.sub_self _

theorem tailDepth_snoc (p : Path H) (b : V) (hb : p.Contains b)
    (v : V) (he : H.Edge p.last v) :
    (p.snoc v he).tailDepth b = p.tailDepth b + 1 := by
  obtain ⟨i, hi⟩ := hb
  rw [p.tailDepth_eq b i hi,
    (p.snoc v he).tailDepth_eq b ⟨i.val, by change i.val < p.length + 1 + 1; omega⟩
      ((p.snoc_vertex_old v he i).trans hi)]
  simp only [snoc_length]
  omega

theorem tailDepth_pop (p : Path H) (b : V) (hb : p.Contains b)
    (hpos : 0 < p.length) (hne : p.last ≠ b) :
    (p.pop hpos).tailDepth b + 1 = p.tailDepth b := by
  obtain ⟨i, hi⟩ := hb
  have hil : i.val < p.length := by
    by_cases hil : i.val < p.length
    · exact hil
    · have hie : i = ⟨p.length, by omega⟩ := Fin.ext (by change i.val = p.length; omega)
      exact False.elim (hne (by rw [hie] at hi; exact hi))
  rw [p.tailDepth_eq b i hi,
    (p.pop hpos).tailDepth_eq b ⟨i.val, by change i.val < p.length - 1 + 1; omega⟩ hi]
  simp only [pop_length]
  omega

end Path
namespace Machine
variable {n : Nat} {H : LayeredGraph (Fin n)}

/-- Actual directed edges of the layered input, counted once per ordered pair. -/
noncomputable def edgeCount (H : LayeredGraph (Fin n)) : Nat := by
  classical
  exact (vertexPairs n).countP fun e => decide (H.Edge e.1 e.2)

noncomputable def unscannedEdges (s : SearchFrame H) : Nat := by
  classical
  exact (vertexPairs n).countP fun e => decide (H.Edge e.1 e.2 ∧ ¬s.explored e.1 e.2)

/-- Actual input edges recorded as scanned by the search. -/
noncomputable def scannedEdges (s : SearchFrame H) : Nat := by
  classical
  exact (vertexPairs n).countP fun e => decide (H.Edge e.1 e.2 ∧ s.explored e.1 e.2)

theorem edge_partition (s : SearchFrame H) :
    unscannedEdges s + scannedEdges s = edgeCount H := by
  classical
  unfold unscannedEdges scannedEdges edgeCount
  have aux : ∀ xs : List (Fin n × Fin n),
      (xs.countP fun e => decide (H.Edge e.1 e.2 ∧ ¬s.explored e.1 e.2)) +
      (xs.countP fun e => decide (H.Edge e.1 e.2 ∧ s.explored e.1 e.2)) =
      (xs.countP fun e => decide (H.Edge e.1 e.2)) := by
    intro xs
    induction xs with
    | nil => simp
    | cons e xs ih =>
      by_cases he : H.Edge e.1 e.2 <;> by_cases hx : s.explored e.1 e.2 <;>
        simp only [List.countP_cons, he, hx, not_true_eq_false, not_false_eq_true,
          and_true, and_false, decide_true, decide_false,
          Bool.false_eq_true, ↓reduceIte] <;> omega
  exact aux _

/-- Constant control credit pays for collision, red failure, and finalization. -/
def workCredit (m : Mode H) : Nat :=
  match m with
  | .normal => 3
  | .redRecovery .. => 2
  | .greenRecovery .. => 1
  | .disjoint | .bottleneck .. => 0

noncomputable def workLocal (s : State H) : Nat :=
  s.frame.red.tailDepth s.frame.barrier + s.frame.green.length + workCredit s.mode

noncomputable def workRank (s : State H) : Nat :=
  4 * unscannedEdges s.frame + workLocal s

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

theorem unscannedEdges_mark_lt (s t : SearchFrame H) (u v : Fin n)
    (he : H.Edge u v) (hu : ¬s.explored u v)
    (hmark : ∀ a b, t.explored a b ↔ (a = u ∧ b = v) ∨ s.explored a b) :
    unscannedEdges t < unscannedEdges s := by
  classical
  unfold unscannedEdges
  apply countP_strict
  · intro e _ hh
    simp only [decide_eq_true_eq] at hh ⊢
    exact ⟨hh.1, fun hs => hh.2 ((hmark e.1 e.2).2 (Or.inr hs))⟩
  · refine ⟨(u, v), mem_vertexPairs u v, ?_, ?_⟩
    · simp only [decide_eq_false_iff_not]
      exact fun hh => hh.2 ((hmark u v).2 (Or.inl ⟨rfl, rfl⟩))
    · simp only [decide_eq_true_eq]
      exact ⟨he, hu⟩

theorem workRank_lt_of_scan (s t : State H) (u v : Fin n)
    (he : H.Edge u v) (hu : ¬s.frame.explored u v)
    (hmark : ∀ a b, t.frame.explored a b ↔ (a = u ∧ b = v) ∨ s.frame.explored a b)
    (hlocal : workLocal t ≤ workLocal s + 3) : workRank t < workRank s := by
  have hh := unscannedEdges_mark_lt s.frame t.frame u v he hu hmark
  unfold workRank
  omega

/-- Every transition decreases the linear edge potential. Barrier makes saved
red-prefix restoration free in this potential: the restored suffix has length
zero. The full invariant is derived from reachability by the caller. -/
theorem step_workRank_lt {r g : Fin n} {s t : State H}
    (hs : Invariant r g s) (h : Step s t) : workRank t < workRank s := by
  cases h with
  | sameRoot hn hr hg heq =>
    simp only [workRank, workLocal, hn, workCredit]
    omega
  | redMove hn hne hsched v he hu hv =>
    apply workRank_lt_of_scan s _ s.frame.red.last v he hu (fun _ _ => Iff.rfl)
    change (s.frame.red.snoc v he).tailDepth s.frame.barrier + s.frame.green.length + 3 ≤ workLocal s + 3
    rw [Path.tailDepth_snoc _ _ hs.basic.barrier.1]
    simp only [workLocal, hn, workCredit]
    omega
  | greenMove hn hne hsched v he hu hv =>
    apply workRank_lt_of_scan s _ s.frame.green.last v he hu (fun _ _ => Iff.rfl)
    change s.frame.red.tailDepth s.frame.barrier + (s.frame.green.length + 1) + 3 ≤ workLocal s + 3
    simp only [workLocal, hn, workCredit]
    omega
  | bottom hn hne hr hg =>
    simp only [workRank, workLocal, hn, workCredit]
    omega
  | collision hn heq hroots =>
    simp only [workRank, workLocal, hn, workCredit]
    omega
  | redPop b p q hm hpos hbar hex =>
    have hh := s.frame.red.tailDepth_pop s.frame.barrier hs.basic.barrier.1 hpos hbar
    change 4 * unscannedEdges s.frame +
      ((s.frame.red.pop hpos).tailDepth s.frame.barrier + s.frame.green.length + workCredit s.mode) < workRank s
    unfold workRank workLocal
    omega
  | redSkip b p q hm hhigh v he hu hv =>
    apply workRank_lt_of_scan s _ s.frame.red.last v he hu (fun _ _ => Iff.rfl)
    change workLocal s ≤ workLocal s + 3
    omega
  | redDeeper b p q hm hhigh v he hu hv hvhigh =>
    apply workRank_lt_of_scan s _ s.frame.red.last v he hu (fun _ _ => Iff.rfl)
    change (s.frame.red.snoc v he).tailDepth s.frame.barrier + s.frame.green.length + workCredit s.mode ≤ workLocal s + 3
    rw [Path.tailDepth_snoc _ _ hs.basic.barrier.1]
    unfold workLocal
    omega
  | redEscape b p q hm hhigh v he hu hv hvlow =>
    apply workRank_lt_of_scan s _ s.frame.red.last v he hu (fun _ _ => Iff.rfl)
    change (s.frame.red.snoc v he).tailDepth s.frame.barrier + s.frame.green.length + 3 ≤ workLocal s + 3
    rw [Path.tailDepth_snoc _ _ hs.basic.barrier.1]
    simp only [workLocal, hm, workCredit]
    omega
  | redFail b p q hm hbar hex =>
    have hmode : s.frame.RecoverySafe b ∧ s.frame.green = q ∧ SavedPaths r g b s.frame p q := by
      simpa only [ModeInv, hm] using hs.mode
    have hp : p.tailDepth b = 0 := by rw [← hmode.2.2.red_end, Path.tailDepth_last]
    change 4 * unscannedEdges s.frame + (p.tailDepth b + s.frame.green.length + 1) < workRank s
    simp only [workRank, workLocal, hm, workCredit, hp]
    omega
  | greenPop b p q hm hpos hex =>
    change 4 * unscannedEdges s.frame +
      (s.frame.red.tailDepth s.frame.barrier + (s.frame.green.length - 1) + workCredit s.mode) < workRank s
    unfold workRank workLocal
    omega
  | greenSkip b p q hm hhigh v he hu hv =>
    apply workRank_lt_of_scan s _ s.frame.green.last v he hu (fun _ _ => Iff.rfl)
    change workLocal s ≤ workLocal s + 3
    omega
  | greenDeeper b p q hm hhigh v he hu hv hvhigh =>
    apply workRank_lt_of_scan s _ s.frame.green.last v he hu (fun _ _ => Iff.rfl)
    change s.frame.red.tailDepth s.frame.barrier + (s.frame.green.length + 1) + workCredit s.mode ≤ workLocal s + 3
    unfold workLocal
    omega
  | greenEscape b p q hm hhigh v he hu hv hvlow =>
    apply workRank_lt_of_scan s _ s.frame.green.last v he hu (fun _ _ => Iff.rfl)
    change s.frame.red.tailDepth s.frame.barrier + (s.frame.green.length + 1) + 3 ≤ workLocal s + 3
    simp only [workLocal, hm, workCredit]
    omega
  | greenFail b p q hm hroot hex =>
    simp only [workRank, workLocal, hm, workCredit]
    omega

/-- Amortized bound valid for every finite execution from an invariant state. -/
theorem trace_workRank_bound (hreach : ReachBottom H) {r g : Fin n}
    {k : Nat} {s t : State H} (h : Trace k s t) (hs : Invariant r g s) :
    workRank t + k ≤ workRank s := by
  induction h with
  | refl s => simp
  | cons hst htu ih =>
    have hh := step_workRank_lt hs hst
    have ht := ih (step_invariant hreach hs hst)
    omega

@[simp] theorem workRank_initial (r g : Fin n) :
    workRank (initial H r g) = 4 * edgeCount H + 3 := by
  classical
  have ht : (Path.trivial H r).tailDepth r = 0 := (Path.trivial H r).tailDepth_last
  simp only [workRank, unscannedEdges, initial, SearchFrame.initial, not_false_eq_true,
    and_true, edgeCount, workLocal, workCredit, Path.trivial]
  exact congrArg (fun a => 4 * edgeCount H + (a + 0 + 3)) ht

/-- A run takes at most four transitions per directed input edge, plus three
control transitions, independent of edge order. This is an abstract operation
bound, not a constant-time implementation claim. -/
theorem trace_linear_bound (hreach : ReachBottom H) (r g : Fin n)
    {k : Nat} {s : State H} (h : Trace k (initial H r g) s) :
    k ≤ 4 * edgeCount H + 3 := by
  have hh := trace_workRank_bound hreach h (initial_invariant r g)
  rw [workRank_initial] at hh
  omega

/-- The sharper local bound charges only edges actually scanned in this
execution, including skip scans. Unvisited parts of the graph do not enter it. -/
theorem trace_scanned_bound (hreach : ReachBottom H) (r g : Fin n)
    {k : Nat} {s : State H} (h : Trace k (initial H r g) s) :
    k + workLocal s ≤ 4 * scannedEdges s.frame + 3 := by
  have hh := trace_workRank_bound hreach h (initial_invariant r g)
  rw [workRank_initial] at hh
  have hp := edge_partition s.frame
  unfold workRank at hh
  omega

/-- DDFS has a correct terminal execution within the linear transition bound. -/
theorem exists_correct_run_linear (hreach : ReachBottom H) (r g : Fin n) :
    ∃ (k : Nat) (s : State H), Trace k (initial H r g) s ∧
      Terminal s ∧ CorrectOutcome r g s ∧ k ≤ 4 * edgeCount H + 3 := by
  obtain ⟨k, s, ht, hd, hc⟩ := exists_correct_run hreach r g
  exact ⟨k, s, ht, hd, hc, trace_linear_bound hreach r g ht⟩

end Machine
end MaximumMatching.DDFS
