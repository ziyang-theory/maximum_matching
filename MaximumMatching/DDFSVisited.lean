import MaximumMatching.DDFSCorrectness

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
