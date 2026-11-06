import MaximumMatching.DDFSCut
import MaximumMatching.DDFSStack

/-! Checked normal-mode transitions of the coordinated DDFS machine.

This file proves scheduling, collision recognition and coverage lemmas for
actual path-stack updates. DDFSMachine and DDFSInvariant assemble all recovery
modes, and DDFSCorrectness proves total path/bottleneck outcome correctness.
The source's linear runtime and global colored trees remain separate. -/
namespace MaximumMatching.DDFS
variable {V : Type} {H : LayeredGraph V}

/-- The shared search frame. The two directed paths are the active DFS stacks. -/
structure SearchFrame (H : LayeredGraph V) where
  red : Path H
  green : Path H
  visited : V → Prop
  explored : V → V → Prop
  barrier : V

namespace SearchFrame

/-- Normal scheduling keeps every earlier visited vertex at least as high as
both current centers. In particular, a visited outgoing neighbor of the higher
center can only be the other current center. -/
def Depth (s : SearchFrame H) : Prop :=
  ∀ u, s.visited u → u ≠ s.red.last → u ≠ s.green.last →
    max (H.level s.red.last) (H.level s.green.last) ≤ H.level u

/-- Local safety facts whose preservation does not need collision recovery. -/
structure NormalSafe (s : SearchFrame H) : Prop where
  depth : s.Depth
  red_visited : ∀ u, s.red.Contains u → s.visited u
  green_visited : ∀ u, s.green.Contains u → s.visited u
  explored_source : ∀ u v, s.explored u v → s.visited u
  red_unexpanded : ∀ v, ¬ s.explored s.red.last v
  green_unexpanded : ∀ v, ¬ s.explored s.green.last v
  separated : ∀ u, s.red.Contains u → s.green.Contains u →
    u = s.red.last ∧ u = s.green.last

def initial (H : LayeredGraph V) (r g : V) : SearchFrame H where
  red := Path.trivial H r
  green := Path.trivial H g
  visited := fun u => u = r ∨ u = g
  explored := fun _ _ => False
  barrier := r

theorem initial_safe (r g : V) : (initial H r g).NormalSafe := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu hr hg
    exact False.elim (hu.elim hr hg)
  · rintro u ⟨i, hi⟩
    exact Or.inl hi.symm
  · rintro u ⟨i, hi⟩
    exact Or.inr hi.symm
  · intro u v h; exact False.elim h
  · intro v h; exact False.elim h
  · intro v h; exact False.elim h
  · rintro u ⟨i, hi⟩ ⟨j, hj⟩
    exact ⟨hi.symm, hj.symm⟩

/-- Recognition of a collision takes precedence over the visited-vertex skip.
The latter has no reachable instance in normal mode under `Depth`. -/
theorem visited_red_target (s : SearchFrame H) (hdepth : s.Depth)
    (hsched : H.level s.green.last ≤ H.level s.red.last)
    {v : V} (hedge : H.Edge s.red.last v) (hseen : s.visited v) :
    v = s.green.last := by
  have hdrop := H.decreases hedge
  by_cases hvr : v = s.red.last
  · rw [hvr] at hdrop
    omega
  · by_cases hvg : v = s.green.last
    · exact hvg
    · have hd := hdepth v hseen hvr hvg
      omega

/-- Scan one outgoing edge of the red center, pushing its destination. This
operation is used for a fresh destination or for the other activity center. -/
def advanceRed (s : SearchFrame H) (v : V) (he : H.Edge s.red.last v) : SearchFrame H where
  red := s.red.snoc v he
  green := s.green
  visited := fun u => u = v ∨ s.visited u
  explored := fun a b => (a = s.red.last ∧ b = v) ∨ s.explored a b
  barrier := s.barrier

@[simp] theorem advanceRed_last (s : SearchFrame H) (v : V) (he : H.Edge s.red.last v) :
    (s.advanceRed v he).red.last = v := Path.snoc_last s.red v he

@[simp] theorem advanceRed_first (s : SearchFrame H) (v : V) (he : H.Edge s.red.last v) :
    (s.advanceRed v he).red.first = s.red.first := Path.snoc_first s.red v he

/-- The selected center is unexpanded, so this transition records a new edge,
not an edge already scanned earlier in the run. -/
theorem advanceRed_new_edge (s : SearchFrame H) (hs : s.NormalSafe)
    (v : V) (he : H.Edge s.red.last v) :
    ¬ s.explored s.red.last v ∧ (s.advanceRed v he).explored s.red.last v :=
  ⟨hs.red_unexpanded v, Or.inl ⟨rfl, rfl⟩⟩

/-- Normal-mode safety is preserved by the actual stack/visited/explored update,
including the transition that makes both centers coincide. -/
theorem advanceRed_safe (s : SearchFrame H) (hs : s.NormalSafe)
    (hne : s.red.last ≠ s.green.last)
    (hsched : H.level s.green.last ≤ H.level s.red.last)
    (v : V) (he : H.Edge s.red.last v) : (s.advanceRed v he).NormalSafe := by
  have hdrop := H.decreases he
  have hvr : v ≠ s.red.last := by intro hv; rw [hv] at hdrop; omega
  have htarget : ¬ s.visited v ∨ v = s.green.last := by
    by_cases hv : s.visited v
    · exact Or.inr (s.visited_red_target hs.depth hsched he hv)
    · exact Or.inl hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu hur hug
    change u = v ∨ s.visited u at hu
    rw [advanceRed_last] at hur
    change u ≠ s.green.last at hug
    change max (H.level (s.advanceRed v he).red.last) (H.level s.green.last) ≤ H.level u
    rw [advanceRed_last]
    rcases hu with hu | hu
    · exact False.elim (hur hu)
    · by_cases huo : u = s.red.last
      · rw [huo]
        omega
      · have hh := hs.depth u hu huo hug
        omega
  · intro u hu
    rcases (Path.snoc_contains_iff s.red v he u).1 hu with hu | hu
    · exact Or.inr (hs.red_visited u hu)
    · exact Or.inl hu
  · intro u hu
    exact Or.inr (hs.green_visited u hu)
  · intro a b hab
    rcases hab with ⟨ha, _⟩ | hab
    · exact Or.inr (ha ▸ hs.red_visited s.red.last s.red.contains_last)
    · exact Or.inr (hs.explored_source a b hab)
  · intro u hu
    change ((s.advanceRed v he).red.last = s.red.last ∧ u = v) ∨
      s.explored (s.advanceRed v he).red.last u at hu
    rw [advanceRed_last] at hu
    rcases hu with ⟨hv, _⟩ | hu
    · exact hvr hv
    · rcases htarget with hn | hv
      · exact hn (hs.explored_source v u hu)
      · exact hs.green_unexpanded u (hv ▸ hu)
  · intro u hu
    change (s.green.last = s.red.last ∧ u = v) ∨ s.explored s.green.last u at hu
    rcases hu with ⟨hh, _⟩ | hu
    · exact hne hh.symm
    · exact hs.green_unexpanded u hu
  · intro u hur hug
    rcases (Path.snoc_contains_iff s.red v he u).1 hur with hur | huv
    · have hh := hs.separated u hur hug
      exact False.elim (hne (hh.1.symm.trans hh.2))
    · refine ⟨by rw [advanceRed_last]; exact huv, ?_⟩
      change u = s.green.last
      rcases htarget with hn | hv
      · exact False.elim (hn (huv ▸ hs.green_visited u hug))
      · exact huv.trans hv

/-- Immediately at collision all other visited vertices are strictly above the
collision. This supplies the initial depth invariant for recovery mode. -/
theorem advanceRed_collision_depth (s : SearchFrame H) (hs : s.NormalSafe)
    (_hsched : H.level s.green.last ≤ H.level s.red.last)
    (he : H.Edge s.red.last s.green.last) :
    ∀ u, (s.advanceRed s.green.last he).visited u → u ≠ s.green.last →
      H.level s.green.last < H.level u := by
  intro u hu hne
  have hd := H.decreases he
  change u = s.green.last ∨ s.visited u at hu
  rcases hu with hu | hu
  · exact False.elim (hne hu)
  · by_cases hur : u = s.red.last
    · rw [hur]; exact hd
    · have hb := hs.depth u hu hur hne
      omega

/-- Swapping the two activity centers supports the symmetric green transition.
The Barrier pointer is not changed by normal moves. -/
def swap (s : SearchFrame H) : SearchFrame H :=
  { s with red := s.green, green := s.red }

theorem swap_safe (s : SearchFrame H) (hs : s.NormalSafe) : s.swap.NormalSafe := by
  refine ⟨?_, hs.green_visited, hs.red_visited, hs.explored_source,
    hs.green_unexpanded, hs.red_unexpanded, ?_⟩
  · intro u hu hur hug
    have hh := hs.depth u hu hug hur
    change max (H.level s.green.last) (H.level s.red.last) ≤ H.level u
    omega
  · intro u hur hug
    exact ⟨(hs.separated u hug hur).2, (hs.separated u hug hur).1⟩

def advanceGreen (s : SearchFrame H) (v : V) (he : H.Edge s.green.last v) : SearchFrame H :=
  (s.swap.advanceRed v he).swap

theorem advanceGreen_safe (s : SearchFrame H) (hs : s.NormalSafe)
    (hne : s.red.last ≠ s.green.last)
    (hsched : H.level s.red.last < H.level s.green.last)
    (v : V) (he : H.Edge s.green.last v) : (s.advanceGreen v he).NormalSafe := by
  exact swap_safe _ (advanceRed_safe s.swap (swap_safe s hs) (Ne.symm hne) (by exact Nat.le_of_lt hsched) v he)

/-- Exhaustion refers to actual recorded edge scans, not to a semantic oracle. -/
def Exhausted (s : SearchFrame H) (u : V) : Prop :=
  ∀ v, H.Edge u v → s.explored u v

/-- Every visited vertex with work remaining lies on one of the active stacks. -/
def Covered (s : SearchFrame H) : Prop :=
  ∀ u, s.visited u → s.Exhausted u ∨ s.red.Contains u ∨ s.green.Contains u

/-- The red prefix above Barrier has already been exhausted. Restoring this
prefix after a failed red escape must preserve this invariant. -/
def BarrierSafe (s : SearchFrame H) : Prop :=
  s.red.Contains s.barrier ∧
    ∀ u, s.red.Contains u → H.level s.barrier < H.level u → s.Exhausted u

/-- Every scanned destination remains in the visited set. -/
def TargetsVisited (s : SearchFrame H) : Prop :=
  ∀ u v, s.explored u v → s.visited v

theorem initial_covered (r g : V) : (initial H r g).Covered := by
  intro u hu
  rcases hu with hu | hu
  · exact Or.inr (Or.inl (hu ▸ (Path.trivial H r).contains_last))
  · exact Or.inr (Or.inr (hu ▸ (Path.trivial H g).contains_last))

theorem initial_barrier_safe (r g : V) : (initial H r g).BarrierSafe := by
  refine ⟨(Path.trivial H r).contains_last, ?_⟩
  rintro u ⟨i, hi⟩ hu
  have he : r = u := hi
  change H.level r < H.level u at hu
  rw [he] at hu
  omega

theorem initial_targets_visited (r g : V) : (initial H r g).TargetsVisited := by
  intro u v he
  exact False.elim he

theorem advanceRed_exhausted (s : SearchFrame H) (v : V) (he : H.Edge s.red.last v)
    (u : V) (hu : s.Exhausted u) : (s.advanceRed v he).Exhausted u := by
  intro w hw
  exact Or.inr (hu w hw)

theorem advanceRed_covered (s : SearchFrame H) (hc : s.Covered)
    (v : V) (he : H.Edge s.red.last v) : (s.advanceRed v he).Covered := by
  intro u hu
  rcases hu with hu | hu
  · exact Or.inr (Or.inl ((Path.snoc_contains_iff s.red v he u).2 (Or.inr hu)))
  · rcases hc u hu with hdone | hred | hgreen
    · exact Or.inl (advanceRed_exhausted s v he u hdone)
    · exact Or.inr (Or.inl ((Path.snoc_contains_iff s.red v he u).2 (Or.inl hred)))
    · exact Or.inr (Or.inr hgreen)

theorem advanceRed_targets_visited (s : SearchFrame H) (hs : s.TargetsVisited)
    (v : V) (he : H.Edge s.red.last v) : (s.advanceRed v he).TargetsVisited := by
  intro u w huw
  rcases huw with ⟨_, hw⟩ | huw
  · exact Or.inl hw
  · exact Or.inr (hs u w huw)

theorem advanceRed_barrier_safe (s : SearchFrame H) (hs : s.BarrierSafe)
    (v : V) (he : H.Edge s.red.last v) : (s.advanceRed v he).BarrierSafe := by
  refine ⟨(Path.snoc_contains_iff s.red v he s.barrier).2 (Or.inl hs.1), ?_⟩
  intro u hu hlevel
  rcases (Path.snoc_contains_iff s.red v he u).1 hu with hu | hu
  · exact advanceRed_exhausted s v he u (hs.2 u hu hlevel)
  · have hb := s.red.last_level_le hs.1
    have hd := H.decreases he
    change H.level s.barrier < H.level u at hlevel
    rw [hu] at hlevel
    omega

/-- Backtrack the red stack without changing its visited history or scans. -/
def backtrackRed (s : SearchFrame H) (hpos : 0 < s.red.length) : SearchFrame H :=
  { s with red := s.red.pop hpos }

theorem backtrackRed_covered (s : SearchFrame H) (hc : s.Covered)
    (hpos : 0 < s.red.length)
    (hretire : s.Exhausted s.red.last ∨ s.green.Contains s.red.last) :
    (s.backtrackRed hpos).Covered := by
  intro u hu
  rcases hc u hu with hdone | hred | hgreen
  · exact Or.inl hdone
  · rcases (s.red.contains_iff_pop_or_last hpos u).1 hred with hpop | hlast
    · exact Or.inr (Or.inl hpop)
    · rcases hretire with hdone | hgreen
      · exact Or.inl (hlast ▸ hdone)
      · exact Or.inr (Or.inr (hlast ▸ hgreen))
  · exact Or.inr (Or.inr hgreen)

theorem backtrackRed_barrier_safe (s : SearchFrame H) (hs : s.BarrierSafe)
    (hpos : 0 < s.red.length) (hne : s.barrier ≠ s.red.last) :
    (s.backtrackRed hpos).BarrierSafe := by
  refine ⟨(s.red.pop_contains_iff hpos s.barrier).2 ⟨hs.1, hne⟩, ?_⟩
  intro u hu hlevel
  exact hs.2 u (s.red.contains_pop hpos hu) hlevel

/-- Every proper-prefix vertex is strictly above the stack's current center. -/
private theorem proper_prefix_above (p : Path H) (u : V) (hu : p.Contains u)
    (hne : u ≠ p.last) : H.level p.last < H.level u := by
  have hle := p.last_level_le hu
  by_cases hlt : H.level p.last < H.level u
  · exact hlt
  · have he := p.eq_of_contains_level_eq hu p.contains_last (by omega)
    exact False.elim (hne he)

/-- At failed red escape, everything still on its allowed stack is exhausted,
except the collision vertex retained by the green stack. -/
theorem red_failure_exhausted (s : SearchFrame H) (hb : s.BarrierSafe)
    (b : V) (hgreen : s.green.last = b) (hstop : s.red.last = s.barrier)
    (hfail : s.Exhausted s.barrier ∨ s.barrier = b) :
    ∀ u, s.red.Contains u → s.Exhausted u ∨ s.green.Contains u := by
  intro u hu
  by_cases he : u = s.red.last
  · rcases hfail with hdone | hbar
    · exact Or.inl ((he.trans hstop) ▸ hdone)
    · exact Or.inr ((he.trans (hstop.trans (hbar.trans hgreen.symm))) ▸ s.green.contains_last)
  · have hlevel := proper_prefix_above s.red u hu he
    rw [hstop] at hlevel
    exact Or.inl (hb.2 u hu hlevel)

/-- Restore the suspended red collision stack and lower Barrier to its end. -/
def restoreRed (s : SearchFrame H) (saved : Path H) (b : V) : SearchFrame H :=
  { s with red := saved, barrier := b }

/-- Restoration preserves coverage because the abandoned active red prefix is
exhausted. No vertex is removed from the visited history. -/
theorem restoreRed_covered (s : SearchFrame H) (hc : s.Covered)
    (saved : Path H) (b : V)
    (hretired : ∀ u, s.red.Contains u → s.Exhausted u ∨ s.green.Contains u) :
    (s.restoreRed saved b).Covered := by
  intro u hu
  rcases hc u hu with hdone | hred | hgreen
  · exact Or.inl hdone
  · rcases hretired u hred with hdone | hgreen
    · exact Or.inl hdone
    · exact Or.inr (Or.inr hgreen)
  · exact Or.inr (Or.inr hgreen)

/-- The new Barrier invariant is derived from old coverage and the separation
of the saved collision stacks. In particular, exhaustion of the restored
prefix is a conclusion, not an input assumption. -/
theorem restoreRed_barrier_safe (s : SearchFrame H) (hc : s.Covered)
    (saved : Path H) (b : V) (hend : saved.last = b)
    (hseen : ∀ u, saved.Contains u → s.visited u)
    (hseparated : ∀ u, saved.Contains u → s.green.Contains u → u = b)
    (hretired : ∀ u, s.red.Contains u → s.Exhausted u ∨ s.green.Contains u) :
    (s.restoreRed saved b).BarrierSafe := by
  refine ⟨hend ▸ saved.contains_last, ?_⟩
  intro u hu hlevel
  change H.level b < H.level u at hlevel
  have hne : u ≠ b := by intro he; rw [he] at hlevel; omega
  have hnotgreen : ¬ s.green.Contains u := fun hg => hne (hseparated u hu hg)
  rcases hc u (hseen u hu) with hdone | hred | hgreen
  · exact hdone
  · rcases hretired u hred with hdone | hgreen
    · exact hdone
    · exact False.elim (hnotgreen hgreen)
  · exact False.elim (hnotgreen hgreen)

/-- At failed green escape, the red prefix above its collision Barrier and the
fully exhausted green stack give a closed searched region away from `b`. -/
theorem closure_at_double_exhaustion (s : SearchFrame H) (hc : s.Covered)
    (hb : s.BarrierSafe) (hv : s.TargetsVisited) (b : V)
    (hred : s.red.last = b) (hbar : s.barrier = b)
    (hgreen : ∀ u, s.green.Contains u → u ≠ b → s.Exhausted u) :
    ClosedExcept (H := H) s.visited b := by
  intro u v hseen hne he
  have hdone : s.Exhausted u := by
    rcases hc u hseen with hdone | hredmem | hgreenmem
    · exact hdone
    · have hneq : u ≠ s.red.last := hred ▸ hne
      have hlevel := proper_prefix_above s.red u hredmem hneq
      apply hb.2 u hredmem
      simpa only [hred, hbar] using hlevel
    · exact hgreen u hgreenmem hne
  exact hv u v (hdone v he)

/-- Record a skipped edge; its destination was already visited. -/
def scanRed (s : SearchFrame H) (v : V) : SearchFrame H :=
  { s with explored := fun a b => (a = s.red.last ∧ b = v) ∨ s.explored a b }

def scanGreen (s : SearchFrame H) (v : V) : SearchFrame H :=
  (s.swap.scanRed v).swap

def backtrackGreen (s : SearchFrame H) (hpos : 0 < s.green.length) : SearchFrame H :=
  (s.swap.backtrackRed hpos).swap

end SearchFrame

/-- The DDFS Requirement gives a legal next edge from every positive layer. -/
theorem edge_exists_of_positive (hreach : ReachBottom H) (v : V) (hv : 0 < H.level v) :
    ∃ u, H.Edge v u := by
  obtain ⟨p, hp, hz⟩ := hreach v
  have hpos : 0 < p.length := by
    apply Classical.byContradiction
    intro hn
    have he : p.length = 0 := by omega
    have hfl : p.first = p.last := congrArg p.vertex (Fin.ext he.symm)
    rw [← hfl, hp] at hz
    omega
  have hedge : H.Edge p.first (p.vertex ⟨1, by omega⟩) := p.adjacent ⟨0, hpos⟩
  exact ⟨p.vertex ⟨1, by omega⟩, hp ▸ hedge⟩

/-- Normal mode cannot get stuck: before either terminal event, the scheduled
center has an unexplored edge and its visited target, if any, is a collision. -/
theorem normal_move_exists (hreach : ReachBottom H) (s : SearchFrame H) (hs : s.NormalSafe)
    (hbottom : ¬ (H.level s.red.last = 0 ∧ H.level s.green.last = 0)) :
    (H.level s.green.last ≤ H.level s.red.last ∧
      ∃ v, H.Edge s.red.last v ∧ ¬ s.explored s.red.last v ∧
        (¬ s.visited v ∨ v = s.green.last)) ∨
    (H.level s.red.last < H.level s.green.last ∧
      ∃ v, H.Edge s.green.last v ∧ ¬ s.explored s.green.last v ∧
        (¬ s.visited v ∨ v = s.red.last)) := by
  classical
  by_cases hge : H.level s.green.last ≤ H.level s.red.last
  · have hpos : 0 < H.level s.red.last := by omega
    obtain ⟨v, hv⟩ := edge_exists_of_positive hreach s.red.last hpos
    refine Or.inl ⟨hge, v, hv, hs.red_unexpanded v, ?_⟩
    by_cases hseen : s.visited v
    · exact Or.inr (s.visited_red_target hs.depth hge hv hseen)
    · exact Or.inl hseen
  · have hlt : H.level s.red.last < H.level s.green.last := by omega
    obtain ⟨v, hv⟩ := edge_exists_of_positive hreach s.green.last (by exact Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)
    refine Or.inr ⟨hlt, v, hv, hs.green_unexpanded v, ?_⟩
    by_cases hseen : s.visited v
    · exact Or.inr (s.swap.visited_red_target (s.swap_safe hs).depth (by exact Nat.le_of_lt hlt) hv hseen)
    · exact Or.inl hseen

end MaximumMatching.DDFS
