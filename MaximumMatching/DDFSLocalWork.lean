import MaximumMatching.DDFSWork
import MaximumMatching.DDFSVisited

/-! Output-local edge accounting for DDFS. The final bounds count edges on
root-to-reported-output paths, rather than all input edges. They count abstract
machine transitions and do not assign costs to a concrete data representation. -/
namespace MaximumMatching.DDFS
namespace Path
variable {V : Type} {H : LayeredGraph V}

def ContainsEdge (p : Path H) (u v : V) : Prop :=
  ∃ i : Fin p.length, p.vertex ⟨i.val, by omega⟩ = u ∧
    p.vertex ⟨i.val + 1, by omega⟩ = v

theorem snoc_containsEdge (p : Path H) (v : V) (he : H.Edge p.last v) :
    (p.snoc v he).ContainsEdge p.last v := by
  refine ⟨⟨p.length, by change p.length < p.length + 1; omega⟩, ?_, ?_⟩
  · simp only [snoc, Nat.le_refl, dite_true, last]
  · simp only [snoc, show ¬p.length + 1 ≤ p.length by omega, dite_false]

theorem containsEdge_append_left (p q : Path H) (hj : p.last = q.first)
    {u v : V} (he : p.ContainsEdge u v) : (p.append q hj).ContainsEdge u v := by
  obtain ⟨i, hi, hv⟩ := he
  refine ⟨⟨i.val, by change i.val < p.length + q.length; omega⟩, ?_, ?_⟩
  · simpa only [append, dite_eq_left (show i.val ≤ p.length by omega)] using hi
  · simpa only [append, dite_eq_left (show i.val + 1 ≤ p.length by omega)] using hv

end Path

/-- Membership in the union of directed edges on paths from either root to
one of the specified terminal vertices. This is a union, not an intersection. -/
def EdgeOnRootTo {V : Type} {H : LayeredGraph V} (r g : V) (T : V → Prop) (u v : V) : Prop :=
  ∃ p : Path H, (p.first = r ∨ p.first = g) ∧ T p.last ∧ p.ContainsEdge u v

namespace SearchFrame
variable {V : Type} {H : LayeredGraph V}

/-- Every explored edge's source has an actual discovery path from a root. -/
def ExploredRooted (r g : V) (s : SearchFrame H) : Prop :=
  ∀ u v, s.explored u v → ∃ p : Path H, (p.first = r ∨ p.first = g) ∧ p.last = u

/-- A visited bottom vertex is still one of the two activity centers. -/
def BottomTracked (s : SearchFrame H) : Prop :=
  ∀ u, s.visited u → H.level u = 0 → u = s.red.last ∨ u = s.green.last

theorem initial_bottomTracked (r g : V) : (initial H r g).BottomTracked := by
  intro u hu _
  exact hu

theorem advanceRed_bottomTracked (s : SearchFrame H) (hs : s.BottomTracked)
    (v : V) (he : H.Edge s.red.last v) : (s.advanceRed v he).BottomTracked := by
  intro u hu hz
  rcases hu with hu | hu
  · exact Or.inl ((s.advanceRed_last v he).symm ▸ hu)
  · rcases hs u hu hz with hr | hg
    · have hd := H.decreases he
      rw [← hr, hz] at hd
      omega
    · exact Or.inr hg

theorem BottomTracked.swap {s : SearchFrame H} (hs : s.BottomTracked) : s.swap.BottomTracked := by
  intro u hu hz
  exact (hs u hu hz).symm

theorem advanceGreen_bottomTracked (s : SearchFrame H) (hs : s.BottomTracked)
    (v : V) (he : H.Edge s.green.last v) : (s.advanceGreen v he).BottomTracked :=
  BottomTracked.swap (s.swap.advanceRed_bottomTracked hs.swap v he)

theorem RecoverySafe.bottom_eq {s : SearchFrame H} {b : V} (hs : s.RecoverySafe b)
    {u : V} (hu : s.visited u) (hz : H.level u = 0) : u = b := by
  by_cases he : u = b
  · exact he
  · have hd := hs.depth u hu he
    omega

/-- Coverage routes every visited vertex to one of the active centers. For a
retired vertex, follow an exhausted outgoing edge and induct on layer. -/
theorem covered_reaches_center (hreach : ReachBottom H) (s : SearchFrame H)
    (hc : s.Covered) (ht : s.TargetsVisited) (hb : s.BottomTracked)
    (u : V) (hu : s.visited u) :
    ∃ p : Path H, p.first = u ∧ (p.last = s.red.last ∨ p.last = s.green.last) := by
  have aux : ∀ k : Nat, ∀ u : V, H.level u = k → s.visited u →
      ∃ p : Path H, p.first = u ∧ (p.last = s.red.last ∨ p.last = s.green.last) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro u huk hu
      by_cases hr : s.red.Contains u
      · obtain ⟨i, hi⟩ := hr
        exact ⟨s.red.drop i.val (by omega), by simpa using hi, Or.inl (by simp)⟩
      by_cases hg : s.green.Contains u
      · obtain ⟨i, hi⟩ := hg
        exact ⟨s.green.drop i.val (by omega), by simpa using hi, Or.inr (by simp)⟩
      have hex : s.Exhausted u := by
        rcases hc u hu with hd | hh | hh
        · exact hd
        · exact False.elim (hr hh)
        · exact False.elim (hg hh)
      have hpos : 0 < H.level u := by
        by_cases hz : H.level u = 0
        · rcases hb u hu hz with hh | hh
          · exact False.elim (hr (hh ▸ s.red.contains_last))
          · exact False.elim (hg (hh ▸ s.green.contains_last))
        · omega
      obtain ⟨a, hau, ha0⟩ := hreach u
      have hal : 0 < a.length := by
        by_cases hz : a.length = 0
        · have he : a.first = a.last := congrArg a.vertex (Fin.ext (by omega))
          rw [← hau, he, ha0] at hpos
          omega
        · omega
      let v := a.vertex ⟨1, by omega⟩
      have hedge : H.Edge u v := by
        have he := a.adjacent ⟨0, hal⟩
        change H.Edge a.first v at he
        rwa [hau] at he
      have hv := ht u v (hex v hedge)
      obtain ⟨z, hzv, hzout⟩ := ih (H.level v) (by have := H.decreases hedge; omega) v rfl hv
      have hj : H.Edge u z.first := hzv ▸ hedge
      exact ⟨Path.prepend u z hj, rfl, by simpa only [Path.prepend_last] using hzout⟩
  exact aux (H.level u) u rfl hu

end SearchFrame
namespace Machine
variable {V : Type} {H : LayeredGraph V}

private theorem marked_exploredRooted {r g a b : V} {s t : SearchFrame H}
    (hs : s.ExploredRooted r g)
    (ha : ∃ p : Path H, (p.first = r ∨ p.first = g) ∧ p.last = a)
    (hm : ∀ u v, t.explored u v → (u = a ∧ v = b) ∨ s.explored u v) :
    t.ExploredRooted r g := by
  intro u v huv
  rcases hm u v huv with ⟨hu, _⟩ | hprev
  · exact hu ▸ ha
  · exact hs u v hprev

theorem step_exploredRooted {r g : V} {s t : State H} (hi : Invariant r g s)
    (hs : s.frame.ExploredRooted r g) (he : Step s t) : t.frame.ExploredRooted r g := by
  have hr := fun (v : V) (t : SearchFrame H)
      (hm : ∀ u w, t.explored u w → (u = s.frame.red.last ∧ w = v) ∨ s.frame.explored u w) =>
    marked_exploredRooted hs ⟨s.frame.red, Or.inl hi.basic.red_root, rfl⟩ hm
  have hg := fun (v : V) (t : SearchFrame H)
      (hm : ∀ u w, t.explored u w → (u = s.frame.green.last ∧ w = v) ∨ s.frame.explored u w) =>
    marked_exploredRooted hs ⟨s.frame.green, Or.inr hi.basic.green_root, rfl⟩ hm
  cases he with
  | redMove _ _ _ v _ _ _ => exact hr v _ (fun _ _ h => h)
  | greenMove _ _ _ v _ _ _ => exact hg v _ (fun _ _ h => h)
  | redSkip _ _ _ _ _ v _ _ _ => exact hr v _ (fun _ _ h => h)
  | redDeeper _ _ _ _ _ v _ _ _ _ => exact hr v _ (fun _ _ h => h)
  | redEscape _ _ _ _ _ v _ _ _ _ => exact hr v _ (fun _ _ h => h)
  | greenSkip _ _ _ _ _ v _ _ _ => exact hg v _ (fun _ _ h => h)
  | greenDeeper _ _ _ _ _ v _ _ _ _ => exact hg v _ (fun _ _ h => h)
  | greenEscape _ _ _ _ _ v _ _ _ _ => exact hg v _ (fun _ _ h => h)
  | _ => exact hs

theorem reachable_exploredRooted (hreach : ReachBottom H) {r g : V} {s : State H}
    (hs : Reachable r g s) : s.frame.ExploredRooted r g := by
  induction hs with
  | initial => intro u v h; exact False.elim h
  | step hprev he ih => exact step_exploredRooted (reachable_invariant hreach hprev) ih he

theorem step_bottomTracked {r g : V} {s t : State H} (hi : Invariant r g s)
    (hs : s.frame.BottomTracked) (he : Step s t) : t.frame.BottomTracked := by
  cases he with
  | redMove _ _ _ v hedge _ _ => exact s.frame.advanceRed_bottomTracked hs v hedge
  | greenMove _ _ _ v hedge _ _ => exact s.frame.advanceGreen_bottomTracked hs v hedge
  | redDeeper _ _ _ _ _ v hedge _ _ _ => exact s.frame.advanceRed_bottomTracked hs v hedge
  | redEscape _ _ _ _ _ v hedge _ _ _ => exact s.frame.advanceRed_bottomTracked hs v hedge
  | greenDeeper _ _ _ _ _ v hedge _ _ _ => exact s.frame.advanceGreen_bottomTracked hs v hedge
  | greenEscape _ _ _ _ _ v hedge _ _ _ => exact s.frame.advanceGreen_bottomTracked hs v hedge
  | redPop b p q hm _ _ _ =>
    have hr : s.frame.RecoverySafe b ∧ s.frame.green = q ∧ SavedPaths r g b s.frame p q := by
      simpa only [ModeInv, hm] using hi.mode
    intro u hu hz
    exact Or.inr ((hr.1.bottom_eq hu hz).trans hr.1.waiting.symm)
  | redFail b p q hm _ _ =>
    have hr : s.frame.RecoverySafe b ∧ s.frame.green = q ∧ SavedPaths r g b s.frame p q := by
      simpa only [ModeInv, hm] using hi.mode
    intro u hu hz
    exact Or.inr ((hr.1.bottom_eq hu hz).trans hr.1.waiting.symm)
  | greenPop b p q hm _ _ =>
    have hr : s.frame.swap.RecoverySafe b ∧ s.frame.red = p ∧ s.frame.barrier = b ∧
        SavedPaths r g b s.frame p q := by simpa only [ModeInv, hm] using hi.mode
    intro u hu hz
    exact Or.inl ((hr.1.bottom_eq hu hz).trans hr.1.waiting.symm)
  | _ => exact hs

theorem reachable_bottomTracked (hreach : ReachBottom H) {r g : V} {s : State H}
    (hs : Reachable r g s) : s.frame.BottomTracked := by
  induction hs with
  | initial => exact SearchFrame.initial_bottomTracked r g
  | step hprev he ih => exact step_bottomTracked (reachable_invariant hreach hprev) ih he

/-- Every visited vertex has a continuation to a final reported bottom in the
disjoint outcome. In particular, abandoned search branches do not require
charging edges outside the paper's output-local path region. -/
theorem visited_reaches_final_bottom (hreach : ReachBottom H) {r g : V} {s : State H}
    (hs : Reachable r g s) (_hm : s.mode = .disjoint) (u : V) (hu : s.frame.visited u) :
    ∃ p : Path H, p.first = u ∧ (p.last = s.frame.red.last ∨ p.last = s.frame.green.last) := by
  have hi := reachable_invariant hreach hs
  exact s.frame.covered_reaches_center hreach hi.basic.covered hi.basic.targets
    (reachable_bottomTracked hreach hs) u hu

private theorem edgeOnRootTo_of_join {r g u v : V} {T : V → Prop}
    (he : H.Edge u v)
    (ha : ∃ p : Path H, (p.first = r ∨ p.first = g) ∧ p.last = u)
    (hb : ∃ q : Path H, q.first = v ∧ T q.last) : EdgeOnRootTo (H := H) r g T u v := by
  obtain ⟨p, hp, hpu⟩ := ha
  obtain ⟨q, hqv, hq⟩ := hb
  have hed : H.Edge p.last v := hpu ▸ he
  let a := p.snoc v hed
  have hj : a.last = q.first := (p.snoc_last v hed).trans hqv.symm
  refine ⟨a.append q hj, ?_, ?_, ?_⟩
  · simpa only [Path.append_first, a, Path.snoc_first] using hp
  · simpa only [Path.append_last] using hq
  · apply Path.containsEdge_append_left
    rw [← hpu]
    exact p.snoc_containsEdge v hed

/-- Every scanned edge at a bottleneck outcome lies on a root-to-bottleneck
path. Source discovery and the exact visited region supply the two pieces. -/
theorem explored_edge_on_bottleneck_path (hreach : ReachBottom H) {r g b : V}
    {s : State H} {p q : Path H} (hs : Reachable r g s)
    (hm : s.mode = .bottleneck b p q) (u v : V) (he : H.Edge u v) (hex : s.frame.explored u v) :
    EdgeOnRootTo (H := H) r g (fun w => w = b) u v := by
  have hi := reachable_invariant hreach hs
  have hv := hi.basic.targets u v hex
  obtain ⟨a, _, hab, ⟨i, hiv⟩⟩ := (visited_iff_on_root_to_bottleneck hreach hs hm v).1 hv
  apply edgeOnRootTo_of_join he (reachable_exploredRooted hreach hs u v hex)
  exact ⟨a.drop i.val (by omega), by simpa using hiv, by simpa using hab⟩

/-- Every scanned edge at a disjoint outcome lies on a path from a root to
one of the two reported bottom vertices. -/
theorem explored_edge_on_disjoint_path (hreach : ReachBottom H) {r g : V}
    {s : State H} (hs : Reachable r g s) (hm : s.mode = .disjoint)
    (u v : V) (he : H.Edge u v) (hex : s.frame.explored u v) :
    EdgeOnRootTo (H := H) r g (fun w => w = s.frame.red.last ∨ w = s.frame.green.last) u v := by
  have hi := reachable_invariant hreach hs
  exact edgeOnRootTo_of_join he (reachable_exploredRooted hreach hs u v hex)
    (visited_reaches_final_bottom hreach hs hm v (hi.basic.targets u v hex))

variable {n : Nat} {H : LayeredGraph (Fin n)}

/-- Number of distinct ordered edges in the specified root-to-output region. -/
noncomputable def outputEdges (H : LayeredGraph (Fin n)) (r g : Fin n) (T : Fin n → Prop) : Nat := by
  classical
  exact (vertexPairs n).countP fun e => decide (EdgeOnRootTo (H := H) r g T e.1 e.2)

theorem scannedEdges_le_outputEdges {r g : Fin n} {T : Fin n → Prop} (s : SearchFrame H)
    (hs : ∀ u v, H.Edge u v → s.explored u v → EdgeOnRootTo (H := H) r g T u v) :
    scannedEdges s ≤ outputEdges H r g T := by
  classical
  unfold scannedEdges outputEdges
  apply List.countP_mono_left
  intro e _ he
  simp only [decide_eq_true_eq] at he ⊢
  exact hs e.1 e.2 he.1 he.2

/-- The bottleneck case uses at most 4|E_b|+3 abstract transitions, where E_b
is exactly the union of edges on paths from either root to the reported b. -/
theorem trace_bottleneck_local_bound (hreach : ReachBottom H) (r g : Fin n)
    {k : Nat} {s : State H} {b : Fin n} {p q : Path H}
    (ht : Trace k (initial H r g) s) (hm : s.mode = .bottleneck b p q) :
    k ≤ 4 * outputEdges H r g (fun w => w = b) + 3 := by
  have hscan := trace_scanned_bound hreach r g ht
  have hlocal := scannedEdges_le_outputEdges s.frame
    (explored_edge_on_bottleneck_path hreach (ht.reachable .initial) hm)
  omega

/-- The disjoint case uses at most 4|E_p|+3 abstract transitions, where E_p
is the union of edges on root-to-reported-bottom paths. -/
theorem trace_disjoint_local_bound (hreach : ReachBottom H) (r g : Fin n)
    {k : Nat} {s : State H} (ht : Trace k (initial H r g) s) (hm : s.mode = .disjoint) :
    k ≤ 4 * outputEdges H r g
      (fun w => w = s.frame.red.last ∨ w = s.frame.green.last) + 3 := by
  have hscan := trace_scanned_bound hreach r g ht
  have hlocal := scannedEdges_le_outputEdges s.frame
    (explored_edge_on_disjoint_path hreach (ht.reachable .initial) hm)
  omega

end Machine
end MaximumMatching.DDFS
