import MaximumMatching.DDFSMachine

namespace MaximumMatching.DDFS
variable {V : Type} {H : LayeredGraph V}
namespace SearchFrame

/-- Facts common to normal mode and both recovery modes. -/
structure StackSafe (s : SearchFrame H) : Prop where
  red_visited : ∀ u, s.red.Contains u → s.visited u
  green_visited : ∀ u, s.green.Contains u → s.visited u
  explored_source : ∀ u v, s.explored u v → s.visited u
  separated : ∀ u, s.red.Contains u → s.green.Contains u →
    u = s.red.last ∧ u = s.green.last

theorem NormalSafe.stack {s : SearchFrame H} (hs : s.NormalSafe) : s.StackSafe :=
  ⟨hs.red_visited, hs.green_visited, hs.explored_source, hs.separated⟩

def CollisionDepth (s : SearchFrame H) : Prop :=
  s.red.last = s.green.last → ∀ u, s.visited u → u ≠ s.red.last →
    H.level s.red.last < H.level u

structure RecoverySafe (s : SearchFrame H) (b : V) : Prop extends s.StackSafe where
  waiting : s.green.last = b
  depth : ∀ u, s.visited u → u ≠ b → H.level b < H.level u
  waiting_unexpanded : ∀ v, ¬s.explored s.green.last v

theorem initial_collision_depth (r g : V) : (initial H r g).CollisionDepth := by
  intro he u hu hn
  change r = g at he
  rcases hu with hu | hu
  · exact False.elim (hn hu)
  · exact False.elim (hn (hu.trans he.symm))

theorem advanceRed_collision_invariant (s : SearchFrame H) (hs : s.NormalSafe)
    (hsched : H.level s.green.last ≤ H.level s.red.last)
    (v : V) (he : H.Edge s.red.last v) : (s.advanceRed v he).CollisionDepth := by
  intro hh u hu hn
  have hv : v = s.green.last := (s.advanceRed_last v he).symm.trans hh
  subst v
  have hh' := s.advanceRed_collision_depth hs hsched he u hu
  simpa only [advanceRed_last] using hh' (by simpa only [advanceRed_last] using hn)

theorem StackSafe.swap {s : SearchFrame H} (hs : s.StackSafe) : s.swap.StackSafe := by
  refine ⟨hs.green_visited, hs.red_visited, hs.explored_source, ?_⟩
  intro u hur hug
  exact ⟨(hs.separated u hug hur).2, (hs.separated u hug hur).1⟩

theorem CollisionDepth.swap {s : SearchFrame H} (hs : s.CollisionDepth) : s.swap.CollisionDepth := by
  intro he u hu hn
  have he' : s.red.last = s.green.last := he.symm
  have hh := hs he' u hu (by change u ≠ s.green.last at hn; rwa [he'])
  change H.level s.green.last < H.level u
  rwa [he'] at hh

theorem advanceGreen_collision_invariant (s : SearchFrame H) (hs : s.NormalSafe)
    (hsched : H.level s.red.last < H.level s.green.last)
    (v : V) (he : H.Edge s.green.last v) : (s.advanceGreen v he).CollisionDepth :=
  CollisionDepth.swap (advanceRed_collision_invariant s.swap (s.swap_safe hs) (Nat.le_of_lt hsched) v he)

theorem advanceRed_stack_fresh (s : SearchFrame H) (hs : s.StackSafe)
    (hne : s.red.last ≠ s.green.last) (v : V) (he : H.Edge s.red.last v)
    (hf : ¬s.visited v) : (s.advanceRed v he).StackSafe := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu
    rcases (Path.snoc_contains_iff s.red v he u).1 hu with hu | hu
    · exact Or.inr (hs.red_visited u hu)
    · exact Or.inl hu
  · intro u hu
    exact Or.inr (hs.green_visited u hu)
  · intro u w hew
    rcases hew with ⟨hu, _⟩ | hew
    · exact Or.inr (hu ▸ hs.red_visited s.red.last s.red.contains_last)
    · exact Or.inr (hs.explored_source u w hew)
  · intro u hur hug
    rcases (Path.snoc_contains_iff s.red v he u).1 hur with hur | huv
    · have hh := hs.separated u hur hug
      exact False.elim (hne (hh.1.symm.trans hh.2))
    · exact False.elim (hf (huv ▸ hs.green_visited u hug))

theorem backtrackRed_stack (s : SearchFrame H) (hs : s.StackSafe)
    (hpos : 0 < s.red.length) : (s.backtrackRed hpos).StackSafe := by
  refine ⟨?_, hs.green_visited, hs.explored_source, ?_⟩
  · intro u hu
    exact hs.red_visited u (s.red.contains_pop hpos hu)
  · intro u hur hug
    have hh := hs.separated u (s.red.contains_pop hpos hur) hug
    exact False.elim (s.red.pop_not_contains_last hpos (hh.1 ▸ hur))

theorem scanRed_stack (s : SearchFrame H) (hs : s.StackSafe) (v : V) :
    (s.scanRed v).StackSafe := by
  refine ⟨hs.red_visited, hs.green_visited, ?_, hs.separated⟩
  intro u w huw
  rcases huw with ⟨hu, _⟩ | huw
  · exact hu ▸ hs.red_visited s.red.last s.red.contains_last
  · exact hs.explored_source u w huw

theorem backtrackRed_recovery (s : SearchFrame H) (hs : s.RecoverySafe b)
    (hpos : 0 < s.red.length) : (s.backtrackRed hpos).RecoverySafe b :=
  ⟨s.backtrackRed_stack hs.toStackSafe hpos, hs.waiting, hs.depth, hs.waiting_unexpanded⟩

theorem scanRed_recovery (s : SearchFrame H) (hs : s.RecoverySafe b)
    (hhigh : H.level b < H.level s.red.last) (v : V) :
    (s.scanRed v).RecoverySafe b := by
  refine ⟨s.scanRed_stack hs.toStackSafe v, hs.waiting, hs.depth, ?_⟩
  intro u hu
  rcases hu with ⟨heq, _⟩ | hu
  · have hh : s.red.last = b := heq.symm.trans hs.waiting
    rw [hh] at hhigh
    omega
  · exact hs.waiting_unexpanded u hu

theorem advanceRed_recovery (s : SearchFrame H) (hs : s.RecoverySafe b)
    (hhigh : H.level b < H.level s.red.last)
    (v : V) (he : H.Edge s.red.last v) (hf : ¬s.visited v)
    (hvhigh : H.level b < H.level v) : (s.advanceRed v he).RecoverySafe b := by
  have hne : s.red.last ≠ s.green.last := by intro hh; rw [hh, hs.waiting] at hhigh; omega
  refine ⟨s.advanceRed_stack_fresh hs.toStackSafe hne v he hf, hs.waiting, ?_, ?_⟩
  · intro u hu hn
    rcases hu with hu | hu
    · exact hu ▸ hvhigh
    · exact hs.depth u hu hn
  · intro u hu
    rcases hu with ⟨hh, _⟩ | hu
    · exact hne hh.symm
    · exact hs.waiting_unexpanded u hu

theorem advanceRed_escape (s : SearchFrame H) (hs : s.RecoverySafe b)
    (hhigh : H.level b < H.level s.red.last)
    (v : V) (he : H.Edge s.red.last v) (hf : ¬s.visited v)
    (hvlow : H.level v ≤ H.level b) : (s.advanceRed v he).NormalSafe ∧
      (s.advanceRed v he).CollisionDepth := by
  have hne : s.red.last ≠ s.green.last := by intro hh; rw [hh, hs.waiting] at hhigh; omega
  have hshape := s.advanceRed_stack_fresh hs.toStackSafe hne v he hf
  have hvg : v ≠ s.green.last := by
    intro hh
    exact hf (hh ▸ hs.green_visited s.green.last s.green.contains_last)
  refine ⟨⟨?_, hshape.red_visited, hshape.green_visited, hshape.explored_source,
    ?_, ?_, hshape.separated⟩, ?_⟩
  · intro u hu hur hug
    rw [advanceRed_last] at hur
    change max (H.level (s.advanceRed v he).red.last) (H.level s.green.last) ≤ H.level u
    rw [advanceRed_last, hs.waiting]
    rcases hu with hu | hu
    · exact False.elim (hur hu)
    · have hh := hs.depth u hu (by change u ≠ s.green.last at hug; rwa [hs.waiting] at hug)
      omega
  · intro u hu
    change ((s.advanceRed v he).red.last = s.red.last ∧ u = v) ∨
      s.explored (s.advanceRed v he).red.last u at hu
    rw [advanceRed_last] at hu
    rcases hu with ⟨hh, _⟩ | hu
    · have hd := H.decreases he
      rw [hh] at hd
      omega
    · exact hf (hs.explored_source v u hu)
  · intro u hu
    rcases hu with ⟨hh, _⟩ | hu
    · exact hne hh.symm
    · exact hs.waiting_unexpanded u hu
  · intro hh
    exact False.elim (hvg ((s.advanceRed_last v he).symm.trans hh))

theorem Covered.swap {s : SearchFrame H} (hs : s.Covered) : s.swap.Covered := by
  intro u hu
  rcases hs u hu with hd | hr | hg
  · exact Or.inl hd
  · exact Or.inr (Or.inr hr)
  · exact Or.inr (Or.inl hg)

structure BasicInv (r g : V) (s : SearchFrame H) : Prop where
  red_root : s.red.first = r
  green_root : s.green.first = g
  covered : s.Covered
  barrier : s.BarrierSafe
  targets : s.TargetsVisited

theorem initial_basic (r g : V) : (initial H r g).BasicInv r g :=
  ⟨rfl, rfl, initial_covered r g, initial_barrier_safe r g, initial_targets_visited r g⟩

theorem advanceRed_basic (s : SearchFrame H) (hs : s.BasicInv r g)
    (v : V) (he : H.Edge s.red.last v) : (s.advanceRed v he).BasicInv r g :=
  ⟨(s.advanceRed_first v he).trans hs.red_root, hs.green_root,
    s.advanceRed_covered hs.covered v he, s.advanceRed_barrier_safe hs.barrier v he,
    s.advanceRed_targets_visited hs.targets v he⟩

theorem advanceGreen_basic (s : SearchFrame H) (hs : s.BasicInv r g)
    (v : V) (he : H.Edge s.green.last v) : (s.advanceGreen v he).BasicInv r g := by
  refine ⟨hs.red_root, (Path.snoc_first s.green v he).trans hs.green_root,
    Covered.swap (s.swap.advanceRed_covered hs.covered.swap v he), ?_, ?_⟩
  · refine ⟨hs.barrier.1, ?_⟩
    intro u hu hlevel w hw
    exact Or.inr (hs.barrier.2 u hu hlevel w hw)
  · intro u w huw
    exact s.swap.advanceRed_targets_visited hs.targets v he u w huw

theorem backtrackRed_basic (s : SearchFrame H) (hs : s.BasicInv r g)
    (hpos : 0 < s.red.length) (hbar : s.red.last ≠ s.barrier)
    (hex : s.Exhausted s.red.last ∨ s.green.Contains s.red.last) :
    (s.backtrackRed hpos).BasicInv r g :=
  ⟨(Path.pop_first s.red hpos).trans hs.red_root, hs.green_root,
    s.backtrackRed_covered hs.covered hpos hex,
    s.backtrackRed_barrier_safe hs.barrier hpos (Ne.symm hbar), hs.targets⟩

theorem backtrackGreen_basic (s : SearchFrame H) (hs : s.BasicInv r g)
    (hpos : 0 < s.green.length)
    (hex : s.Exhausted s.green.last ∨ s.red.Contains s.green.last) :
    (s.backtrackGreen hpos).BasicInv r g :=
  ⟨hs.red_root, (Path.pop_first s.green hpos).trans hs.green_root,
    Covered.swap (s.swap.backtrackRed_covered hs.covered.swap hpos hex), hs.barrier, hs.targets⟩

theorem scanRed_basic (s : SearchFrame H) (hs : s.BasicInv r g)
    (v : V) (hv : s.visited v) : (s.scanRed v).BasicInv r g := by
  refine ⟨hs.red_root, hs.green_root, ?_, ?_, ?_⟩
  · intro u hu
    rcases hs.covered u hu with hd | hr | hg
    · exact Or.inl (fun w hw => Or.inr (hd w hw))
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr hg)
  · exact ⟨hs.barrier.1, fun u hu hl w hw => Or.inr (hs.barrier.2 u hu hl w hw)⟩
  · intro u w huw
    rcases huw with ⟨_, hw⟩ | huw
    · exact hw ▸ hv
    · exact hs.targets u w huw

theorem scanGreen_basic (s : SearchFrame H) (hs : s.BasicInv r g)
    (v : V) (hv : s.visited v) : (s.scanGreen v).BasicInv r g := by
  refine ⟨hs.red_root, hs.green_root, ?_, ?_, ?_⟩
  · intro u hu
    rcases hs.covered u hu with hd | hr | hg
    · exact Or.inl (fun w hw => Or.inr (hd w hw))
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr hg)
  · exact ⟨hs.barrier.1, fun u hu hl w hw => Or.inr (hs.barrier.2 u hu hl w hw)⟩
  · intro u w huw
    rcases huw with ⟨_, hw⟩ | huw
    · exact hw ▸ hv
    · exact hs.targets u w huw

end SearchFrame
namespace Machine

/-- Collision paths are preserved even while active stacks backtrack. -/
structure SavedPaths (r g b : V) (s : SearchFrame H) (p q : Path H) : Prop where
  red_root : p.first = r
  green_root : q.first = g
  red_end : p.last = b
  green_end : q.last = b
  red_seen : ∀ u, p.Contains u → s.visited u
  green_seen : ∀ u, q.Contains u → s.visited u
  meet : ∀ u, p.Contains u → q.Contains u → u = b

theorem SavedPaths.mono {r g b : V} {s t : SearchFrame H} {p q : Path H}
    (hs : SavedPaths r g b s p q) (hmono : ∀ u, s.visited u → t.visited u) :
    SavedPaths r g b t p q :=
  ⟨hs.red_root, hs.green_root, hs.red_end, hs.green_end,
    fun u hu => hmono u (hs.red_seen u hu), fun u hu => hmono u (hs.green_seen u hu), hs.meet⟩

def ModeInv (r g : V) (s : State H) : Prop :=
  match s.mode with
  | .normal => s.frame.NormalSafe ∧ s.frame.CollisionDepth
  | .redRecovery b p q =>
      s.frame.RecoverySafe b ∧ s.frame.green = q ∧ SavedPaths r g b s.frame p q
  | .greenRecovery b p q =>
      s.frame.swap.RecoverySafe b ∧ s.frame.red = p ∧ s.frame.barrier = b ∧
        SavedPaths r g b s.frame p q
  | .disjoint => s.frame.red.ToBottom r ∧ s.frame.green.ToBottom g ∧
      s.frame.red.Disjoint s.frame.green
  | .bottleneck b p q => HighestBottleneck H r g b ∧ SavedPaths r g b s.frame p q

structure Invariant (r g : V) (s : State H) : Prop where
  basic : s.frame.BasicInv r g
  mode : ModeInv r g s

theorem initial_invariant (r g : V) : Invariant r g (initial H r g) :=
  ⟨SearchFrame.initial_basic r g,
    ⟨SearchFrame.initial_safe r g, SearchFrame.initial_collision_depth r g⟩⟩

private theorem collision_saved (r g : V) (s : SearchFrame H)
    (hb : s.BasicInv r g) (hs : s.NormalSafe) (he : s.red.last = s.green.last) :
    SavedPaths r g s.red.last s s.red s.green :=
  ⟨hb.red_root, hb.green_root, rfl, he.symm, hs.red_visited, hs.green_visited,
    fun u hr hg => (hs.separated u hr hg).1⟩

private theorem collision_recovery (s : SearchFrame H) (hs : s.NormalSafe)
    (hd : s.CollisionDepth) (he : s.red.last = s.green.last) :
    s.RecoverySafe s.red.last :=
  ⟨hs.stack, he.symm, hd he, hs.green_unexpanded⟩

/-- Failing the red search restores the original red path, transfers the
collision, and derives the new Barrier invariant from coverage. -/
theorem red_failure_invariant (r g b : V) (s : SearchFrame H) (p q : Path H)
    (hbasic : s.BasicInv r g) (hs : s.RecoverySafe b) (hgreen : s.green = q)
    (hsaved : SavedPaths r g b s p q) (hbar : s.red.last = s.barrier)
    (hfail : s.red.last = b ∨ s.Exhausted s.red.last) :
    Invariant r g ⟨s.restoreRed p b, .greenRecovery b p q⟩ := by
  have hfailure : s.Exhausted s.barrier ∨ s.barrier = b := by
    rcases hfail with he | hd
    · exact Or.inr (hbar.symm.trans he)
    · exact Or.inl (hbar ▸ hd)
  have hret := s.red_failure_exhausted hbasic.barrier b hs.waiting hbar hfailure
  have hmeet : ∀ u, p.Contains u → s.green.Contains u → u = b := by
    intro u hp hg
    exact hsaved.meet u hp (hgreen ▸ hg)
  refine ⟨⟨hsaved.red_root, hbasic.green_root,
    s.restoreRed_covered hbasic.covered p b hret,
    s.restoreRed_barrier_safe hbasic.covered p b hsaved.red_end hsaved.red_seen hmeet hret,
    hbasic.targets⟩, ?_⟩
  refine ⟨?_, rfl, rfl, hsaved.mono (fun _ h => h)⟩
  refine ⟨⟨hs.green_visited, hsaved.red_seen, hs.explored_source, ?_⟩,
    hsaved.red_end, hs.depth, ?_⟩
  · intro u hg hp
    have he := hmeet u hp hg
    exact ⟨he.trans hs.waiting.symm, he.trans hsaved.red_end.symm⟩
  · intro u hu
    apply hs.waiting_unexpanded u
    change s.explored p.last u at hu
    simpa only [hsaved.red_end, hs.waiting] using hu

private theorem first_eq_last_of_length_zero (p : Path H) (hp : p.length = 0) : p.first = p.last :=
  congrArg p.vertex (Fin.ext hp.symm)

/-- Coverage at final green exhaustion gives the highest bottleneck using the
saved collision paths. The possibly shortened green stack is not used as the
root-to-bottleneck witness. -/
theorem green_failure_highest (hreach : ReachBottom H) (r g b : V)
    (s : SearchFrame H) (p q : Path H) (hbasic : s.BasicInv r g)
    (hs : s.swap.RecoverySafe b) (hred : s.red = p) (hbar : s.barrier = b)
    (hsaved : SavedPaths r g b s p q)
    (hroot : s.green.length = 0)
    (hfail : s.green.last = b ∨ s.Exhausted s.green.last) : HighestBottleneck H r g b := by
  have hredend : s.red.last = b := hred ▸ hsaved.red_end
  have hgreen_done : ∀ u, s.green.Contains u → u ≠ b → s.Exhausted u := by
    intro u hu hne
    have he : u = s.green.last := by
      obtain ⟨i, hi⟩ := hu
      have hi' : i = ⟨s.green.length, by omega⟩ := Fin.ext (by have := i.isLt; omega)
      exact (hi' ▸ hi).symm
    rcases hfail with hb | hd
    · exact False.elim (hne (he.trans hb))
    · exact he ▸ hd
  have hclosed := s.closure_at_double_exhaustion hbasic.covered hbasic.barrier
    hbasic.targets b hredend hbar hgreen_done
  have hvr : s.visited r := by
    have hh := hs.green_visited s.red.first s.red.contains_first
    change s.visited s.red.first at hh
    simpa only [hbasic.red_root] using hh
  have hvg : s.visited g := by
    have hh := hs.red_visited s.green.first s.green.contains_first
    change s.visited s.green.first at hh
    simpa only [hbasic.green_root] using hh
  have hbottom : ∀ u, s.visited u → H.level u = 0 → u = b := by
    intro u hu hz
    by_cases he : u = b
    · exact he
    · have hh := hs.depth u hu he
      omega
  exact highestBottleneck_of_closed_region r g b s.visited hvr hvg hclosed hbottom
    (hreach b) p q hsaved.red_root hsaved.red_end hsaved.green_root hsaved.green_end hsaved.meet

/-- Every concrete machine step preserves the proved mode/coverage invariant. -/
theorem step_invariant (hreach : ReachBottom H) {r g : V} {s t : State H}
    (hs : Invariant r g s) (hstep : Step s t) : Invariant r g t := by
  cases hstep with
  | sameRoot hn hr hg heq =>
    have hrr : s.frame.red.last = r :=
      (first_eq_last_of_length_zero s.frame.red hr).symm.trans hs.basic.red_root
    have hgr : g = r := hs.basic.green_root.symm.trans
      ((first_eq_last_of_length_zero s.frame.green hg).trans (heq.symm.trans hrr))
    have hn' : s.frame.NormalSafe ∧ s.frame.CollisionDepth := by
      simpa only [ModeInv, hn] using hs.mode
    refine ⟨hs.basic, ?_, collision_saved r g s.frame hs.basic hn'.1 heq⟩
    rw [hgr, hrr]
    exact highestBottleneck_same_root r (hreach r)
  | redMove hn hne hsched v he hu hv =>
    have hm : s.frame.NormalSafe ∧ s.frame.CollisionDepth := by
      simpa only [ModeInv, hn] using hs.mode
    exact ⟨s.frame.advanceRed_basic hs.basic v he,
      s.frame.advanceRed_safe hm.1 hne hsched v he,
      s.frame.advanceRed_collision_invariant hm.1 hsched v he⟩
  | greenMove hn hne hsched v he hu hv =>
    have hm : s.frame.NormalSafe ∧ s.frame.CollisionDepth := by
      simpa only [ModeInv, hn] using hs.mode
    exact ⟨s.frame.advanceGreen_basic hs.basic v he,
      s.frame.advanceGreen_safe hm.1 hne hsched v he,
      s.frame.advanceGreen_collision_invariant hm.1 hsched v he⟩
  | bottom hn hne hr hg =>
    have hm : s.frame.NormalSafe ∧ s.frame.CollisionDepth := by
      simpa only [ModeInv, hn] using hs.mode
    refine ⟨hs.basic, ⟨hs.basic.red_root, hr⟩, ⟨hs.basic.green_root, hg⟩, ?_⟩
    intro u hur hug
    have hh := hm.1.separated u hur hug
    exact hne (hh.1.symm.trans hh.2)
  | collision hn heq hroots =>
    have hm : s.frame.NormalSafe ∧ s.frame.CollisionDepth := by
      simpa only [ModeInv, hn] using hs.mode
    exact ⟨hs.basic, collision_recovery s.frame hm.1 hm.2 heq, rfl,
      collision_saved r g s.frame hs.basic hm.1 heq⟩
  | redPop b p q hm hpos hbar hex =>
    have hmode : s.frame.RecoverySafe b ∧ s.frame.green = q ∧ SavedPaths r g b s.frame p q := by
      simpa only [ModeInv, hm] using hs.mode
    have hret : s.frame.Exhausted s.frame.red.last ∨ s.frame.green.Contains s.frame.red.last := by
      rcases hex with he | hd
      · exact Or.inr ((he.trans hmode.1.waiting.symm) ▸ s.frame.green.contains_last)
      · exact Or.inl hd
    refine ⟨s.frame.backtrackRed_basic hs.basic hpos hbar hret, ?_⟩
    simp only [ModeInv, hm]
    exact ⟨s.frame.backtrackRed_recovery hmode.1 hpos, hmode.2.1,
      hmode.2.2.mono (fun _ h => h)⟩
  | redSkip b p q hm hhigh v he hu hv =>
    have hmode : s.frame.RecoverySafe b ∧ s.frame.green = q ∧ SavedPaths r g b s.frame p q := by
      simpa only [ModeInv, hm] using hs.mode
    refine ⟨s.frame.scanRed_basic hs.basic v hv, ?_⟩
    simp only [ModeInv, hm]
    exact ⟨s.frame.scanRed_recovery hmode.1 hhigh v, hmode.2.1,
      hmode.2.2.mono (fun _ h => h)⟩
  | redDeeper b p q hm hhigh v he hu hv hvhigh =>
    have hmode : s.frame.RecoverySafe b ∧ s.frame.green = q ∧ SavedPaths r g b s.frame p q := by
      simpa only [ModeInv, hm] using hs.mode
    refine ⟨s.frame.advanceRed_basic hs.basic v he, ?_⟩
    simp only [ModeInv, hm]
    exact ⟨s.frame.advanceRed_recovery hmode.1 hhigh v he hv hvhigh, hmode.2.1,
      hmode.2.2.mono (fun _ h => Or.inr h)⟩
  | redEscape b p q hm hhigh v he hu hv hvlow =>
    have hmode : s.frame.RecoverySafe b ∧ s.frame.green = q ∧ SavedPaths r g b s.frame p q := by
      simpa only [ModeInv, hm] using hs.mode
    exact ⟨s.frame.advanceRed_basic hs.basic v he,
      s.frame.advanceRed_escape hmode.1 hhigh v he hv hvlow⟩
  | redFail b p q hm hbar hex =>
    have hmode : s.frame.RecoverySafe b ∧ s.frame.green = q ∧ SavedPaths r g b s.frame p q := by
      simpa only [ModeInv, hm] using hs.mode
    exact red_failure_invariant r g b s.frame p q hs.basic hmode.1 hmode.2.1 hmode.2.2 hbar hex
  | greenPop b p q hm hpos hex =>
    have hmode : s.frame.swap.RecoverySafe b ∧ s.frame.red = p ∧ s.frame.barrier = b ∧
        SavedPaths r g b s.frame p q := by simpa only [ModeInv, hm] using hs.mode
    have hret : s.frame.Exhausted s.frame.green.last ∨ s.frame.red.Contains s.frame.green.last := by
      rcases hex with he | hd
      · exact Or.inr ((he.trans hmode.1.waiting.symm) ▸ s.frame.red.contains_last)
      · exact Or.inl hd
    refine ⟨s.frame.backtrackGreen_basic hs.basic hpos hret, ?_⟩
    simp only [ModeInv, hm]
    exact ⟨s.frame.swap.backtrackRed_recovery hmode.1 hpos, hmode.2.1, hmode.2.2.1,
      hmode.2.2.2.mono (fun _ h => h)⟩
  | greenSkip b p q hm hhigh v he hu hv =>
    have hmode : s.frame.swap.RecoverySafe b ∧ s.frame.red = p ∧ s.frame.barrier = b ∧
        SavedPaths r g b s.frame p q := by simpa only [ModeInv, hm] using hs.mode
    refine ⟨s.frame.scanGreen_basic hs.basic v hv, ?_⟩
    simp only [ModeInv, hm]
    exact ⟨s.frame.swap.scanRed_recovery hmode.1 hhigh v, hmode.2.1, hmode.2.2.1,
      hmode.2.2.2.mono (fun _ h => h)⟩
  | greenDeeper b p q hm hhigh v he hu hv hvhigh =>
    have hmode : s.frame.swap.RecoverySafe b ∧ s.frame.red = p ∧ s.frame.barrier = b ∧
        SavedPaths r g b s.frame p q := by simpa only [ModeInv, hm] using hs.mode
    refine ⟨s.frame.advanceGreen_basic hs.basic v he, ?_⟩
    simp only [ModeInv, hm]
    exact ⟨s.frame.swap.advanceRed_recovery hmode.1 hhigh v he hv hvhigh, hmode.2.1, hmode.2.2.1,
      hmode.2.2.2.mono (fun _ h => Or.inr h)⟩
  | greenEscape b p q hm hhigh v he hu hv hvlow =>
    have hmode : s.frame.swap.RecoverySafe b ∧ s.frame.red = p ∧ s.frame.barrier = b ∧
        SavedPaths r g b s.frame p q := by simpa only [ModeInv, hm] using hs.mode
    have hescape := s.frame.swap.advanceRed_escape hmode.1 hhigh v he hv hvlow
    exact ⟨s.frame.advanceGreen_basic hs.basic v he,
      SearchFrame.swap_safe _ hescape.1, hescape.2.swap⟩
  | greenFail b p q hm hroot hex =>
    have hmode : s.frame.swap.RecoverySafe b ∧ s.frame.red = p ∧ s.frame.barrier = b ∧
        SavedPaths r g b s.frame p q := by simpa only [ModeInv, hm] using hs.mode
    exact ⟨hs.basic, green_failure_highest hreach r g b s.frame p q hs.basic hmode.1
      hmode.2.1 hmode.2.2.1 hmode.2.2.2 hroot hex, hmode.2.2.2⟩

/-- All states of the actual transition system satisfy the invariant; it is
proved from initialization and preservation rather than supplied as an oracle. -/
theorem reachable_invariant (hreach : ReachBottom H) {r g : V} {s : State H}
    (hs : Reachable r g s) : Invariant r g s := by
  induction hs with
  | initial => exact initial_invariant r g
  | step hr hstep ih => exact step_invariant hreach ih hstep

private theorem length_zero_of_first_eq_last (p : Path H) (he : p.first = p.last) : p.length = 0 := by
  have hi := p.injective ⟨0, by omega⟩ ⟨p.length, by omega⟩ he
  have hv : 0 = p.length := congrArg (fun i : Fin (p.length + 1) => i.val) hi
  omega

private theorem positive_of_contains_ne_last (p : Path H) (u : V)
    (hu : p.Contains u) (hne : p.last ≠ u) : 0 < p.length := by
  obtain ⟨i, hi⟩ := hu
  by_cases hp : 0 < p.length
  · exact hp
  · have hiz : i = ⟨p.length, by omega⟩ := Fin.ext (by have := i.isLt; omega)
    rw [hiz] at hi
    exact False.elim (hne hi)

private theorem edge_unexplored_of_not_exhausted (s : SearchFrame H) (u : V)
    (hn : ¬s.Exhausted u) : ∃ v, H.Edge u v ∧ ¬s.explored u v := by
  classical
  apply Classical.byContradiction
  intro hnone
  apply hn
  intro v hv
  apply Classical.byContradiction
  intro he
  exact hnone ⟨v, hv, he⟩

private theorem red_retire_progress (s : State H) (b : V) (p q : Path H)
    (hm : s.mode = .redRecovery b p q) (hb : s.frame.BarrierSafe)
    (hex : s.frame.red.last = b ∨ s.frame.Exhausted s.frame.red.last) :
    ∃ t, Step s t := by
  classical
  by_cases hbar : s.frame.red.last = s.frame.barrier
  · exact ⟨_, Step.redFail s b p q hm hbar hex⟩
  · have hpos := positive_of_contains_ne_last s.frame.red s.frame.barrier hb.1 hbar
    exact ⟨_, Step.redPop s b p q hm hpos hbar hex⟩

private theorem green_retire_progress (s : State H) (b : V) (p q : Path H)
    (hm : s.mode = .greenRecovery b p q)
    (hex : s.frame.green.last = b ∨ s.frame.Exhausted s.frame.green.last) :
    ∃ t, Step s t := by
  by_cases hzero : s.frame.green.length = 0
  · exact ⟨_, Step.greenFail s b p q hm hzero hex⟩
  · exact ⟨_, Step.greenPop s b p q hm (by omega) hex⟩

/-- Every invariant state is terminal or has an enabled concrete transition.
Recovery explores an unused edge, backtracks an exhausted stack, or executes
its explicit Barrier/root failure branch. -/
theorem invariant_progress (hreach : ReachBottom H) {r g : V} {s : State H}
    (hs : Invariant r g s) : Terminal s ∨ ∃ t, Step s t := by
  classical
  cases hm : s.mode with
  | normal =>
    right
    have hn : s.frame.NormalSafe ∧ s.frame.CollisionDepth := by
      simpa only [ModeInv, hm] using hs.mode
    by_cases hmeet : s.frame.red.last = s.frame.green.last
    · by_cases hroots : s.frame.red.first = s.frame.green.first
      · have hgin : s.frame.green.Contains s.frame.red.first := by
          rw [hroots]
          exact s.frame.green.contains_first
        have hh := hn.1.separated s.frame.red.first s.frame.red.contains_first hgin
        have hr := length_zero_of_first_eq_last s.frame.red hh.1
        have hg := length_zero_of_first_eq_last s.frame.green (hroots.symm.trans hh.2)
        exact ⟨_, Step.sameRoot s hm hr hg hmeet⟩
      · exact ⟨_, Step.collision s hm hmeet hroots⟩
    · by_cases hbottom : H.level s.frame.red.last = 0 ∧ H.level s.frame.green.last = 0
      · exact ⟨_, Step.bottom s hm hmeet hbottom.1 hbottom.2⟩
      · rcases normal_move_exists hreach s.frame hn.1 hbottom with
          ⟨horder, v, he, hu, hv⟩ | ⟨horder, v, he, hu, hv⟩
        · exact ⟨_, Step.redMove s hm hmeet horder v he hu hv⟩
        · exact ⟨_, Step.greenMove s hm hmeet horder v he hu hv⟩
  | redRecovery b p q =>
    right
    have hr : s.frame.RecoverySafe b ∧ s.frame.green = q ∧ SavedPaths r g b s.frame p q := by
      simpa only [ModeInv, hm] using hs.mode
    by_cases heq : s.frame.red.last = b
    · exact red_retire_progress s b p q hm hs.basic.barrier (Or.inl heq)
    · by_cases hd : s.frame.Exhausted s.frame.red.last
      · exact red_retire_progress s b p q hm hs.basic.barrier (Or.inr hd)
      · have hhigh := hr.1.depth s.frame.red.last (hr.1.red_visited _ s.frame.red.contains_last) heq
        obtain ⟨v, he, hu⟩ := edge_unexplored_of_not_exhausted s.frame s.frame.red.last hd
        by_cases hv : s.frame.visited v
        · exact ⟨_, Step.redSkip s b p q hm hhigh v he hu hv⟩
        · by_cases hvhigh : H.level b < H.level v
          · exact ⟨_, Step.redDeeper s b p q hm hhigh v he hu hv hvhigh⟩
          · exact ⟨_, Step.redEscape s b p q hm hhigh v he hu hv (by omega)⟩
  | greenRecovery b p q =>
    right
    have hg : s.frame.swap.RecoverySafe b ∧ s.frame.red = p ∧ s.frame.barrier = b ∧
        SavedPaths r g b s.frame p q := by simpa only [ModeInv, hm] using hs.mode
    by_cases heq : s.frame.green.last = b
    · exact green_retire_progress s b p q hm (Or.inl heq)
    · by_cases hd : s.frame.Exhausted s.frame.green.last
      · exact green_retire_progress s b p q hm (Or.inr hd)
      · have hhigh := hg.1.depth s.frame.green.last (hg.1.red_visited _ s.frame.green.contains_last) heq
        obtain ⟨v, he, hu⟩ := edge_unexplored_of_not_exhausted s.frame s.frame.green.last hd
        by_cases hv : s.frame.visited v
        · exact ⟨_, Step.greenSkip s b p q hm hhigh v he hu hv⟩
        · by_cases hvhigh : H.level b < H.level v
          · exact ⟨_, Step.greenDeeper s b p q hm hhigh v he hu hv hvhigh⟩
          · exact ⟨_, Step.greenEscape s b p q hm hhigh v he hu hv (by omega)⟩
  | disjoint => exact Or.inl (Or.inl hm)
  | bottleneck b p q => exact Or.inl (Or.inr ⟨b, p, q, hm⟩)

theorem reachable_progress (hreach : ReachBottom H) {r g : V} {s : State H}
    (hs : Reachable r g s) : Terminal s ∨ ∃ t, Step s t :=
  invariant_progress hreach (reachable_invariant hreach hs)

end Machine

end MaximumMatching.DDFS
