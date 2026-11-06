import MaximumMatching.DDFSGeometry
import MaximumMatching.DDFSPaths

section DDFSStack

/-! Append and backtrack operations on directed DDFS path stacks. The layered
edge condition proves freshness, and backtracking removes precisely the last
vertex of a nonempty path. -/
namespace MaximumMatching.DDFS.Path
variable {V : Type} {H : LayeredGraph V}

/-- Push an actual outgoing edge onto a path stack. -/
def snoc (p : Path H) (v : V) (he : H.Edge p.last v) : Path H where
  length := p.length + 1
  vertex i := if hi : i.val ≤ p.length then p.vertex ⟨i.val, by omega⟩ else v
  adjacent i := by
    by_cases hi : i.val < p.length
    · simpa only [dite_eq_left (show i.val ≤ p.length by omega),
        dite_eq_left (show i.val + 1 ≤ p.length by omega)] using p.adjacent ⟨i.val, hi⟩
    · have heq : i.val = p.length := by have := i.isLt; omega
      simpa only [heq, Nat.le_refl, dite_true,
        show ¬p.length + 1 ≤ p.length by omega, dite_false, last] using he

@[simp] theorem snoc_length (p : Path H) (v : V) (he : H.Edge p.last v) :
    (p.snoc v he).length = p.length + 1 := rfl

@[simp] theorem snoc_first (p : Path H) (v : V) (he : H.Edge p.last v) :
    (p.snoc v he).first = p.first := by simp only [first, snoc, Nat.zero_le, dite_true]

@[simp] theorem snoc_last (p : Path H) (v : V) (he : H.Edge p.last v) :
    (p.snoc v he).last = v := by
  simp only [last, snoc, show ¬p.length + 1 ≤ p.length by omega, dite_false]

@[simp] theorem snoc_vertex_old (p : Path H) (v : V) (he : H.Edge p.last v)
    (i : Fin (p.length + 1)) :
    (p.snoc v he).vertex ⟨i.val, by change i.val < p.length + 1 + 1; omega⟩ = p.vertex i := by
  simp only [snoc, dite_eq_left (show i.val ≤ p.length by omega)]

/-- The new vertex is fresh, as every old vertex is above the outgoing endpoint. -/
theorem snoc_fresh (p : Path H) (v : V) (he : H.Edge p.last v) : ¬ p.Contains v := by
  intro hv
  have hlo := H.decreases he
  have hhi := p.last_level_le hv
  omega

theorem snoc_contains_iff (p : Path H) (v : V) (he : H.Edge p.last v) (x : V) :
    (p.snoc v he).Contains x ↔ p.Contains x ∨ x = v := by
  constructor
  · rintro ⟨i, hi⟩
    change (if h : i.val ≤ p.length then p.vertex ⟨i.val, _⟩ else v) = x at hi
    split at hi
    · exact Or.inl ⟨_, hi⟩
    · exact Or.inr hi.symm
  · rintro (⟨i, hi⟩ | hx)
    · refine ⟨⟨i.val, by change i.val < p.length + 1 + 1; omega⟩, ?_⟩
      rw [snoc_vertex_old]
      exact hi
    · have hlast := (p.snoc v he).contains_last
      simpa only [snoc_last, ← hx] using hlast

/-- Backtrack one edge. The positivity premise distinguishes a real pop from
attempting to backtrack past a root. -/
def pop (p : Path H) (_hpos : 0 < p.length) : Path H := p.take (p.length - 1) (by omega)

@[simp] theorem pop_length (p : Path H) (hpos : 0 < p.length) :
    (p.pop hpos).length = p.length - 1 := rfl

@[simp] theorem pop_first (p : Path H) (hpos : 0 < p.length) :
    (p.pop hpos).first = p.first := rfl

@[simp] theorem pop_last (p : Path H) (hpos : 0 < p.length) :
    (p.pop hpos).last = p.vertex ⟨p.length - 1, by omega⟩ := rfl

@[simp] theorem pop_vertex (p : Path H) (hpos : 0 < p.length)
    (i : Fin ((p.pop hpos).length + 1)) :
    (p.pop hpos).vertex i = p.vertex ⟨i.val, by have := i.isLt; change i.val < p.length - 1 + 1 at this; omega⟩ := rfl

theorem contains_pop (p : Path H) (hpos : 0 < p.length) {x : V}
    (hx : (p.pop hpos).Contains x) : p.Contains x := p.contains_take _ _ hx

theorem pop_not_contains_last (p : Path H) (hpos : 0 < p.length) :
    ¬ (p.pop hpos).Contains p.last := by
  rintro ⟨i, hi⟩
  have he := p.injective ⟨i.val, by have := i.isLt; change i.val < p.length - 1 + 1 at this; omega⟩
    ⟨p.length, by omega⟩ hi
  have hv := congrArg Fin.val he
  have hib := i.isLt
  change i.val < p.length - 1 + 1 at hib
  change i.val = p.length at hv
  omega

theorem contains_iff_pop_or_last (p : Path H) (hpos : 0 < p.length) (x : V) :
    p.Contains x ↔ (p.pop hpos).Contains x ∨ x = p.last := by
  constructor
  · rintro ⟨i, hi⟩
    by_cases hlt : i.val < p.length
    · exact Or.inl ⟨⟨i.val, by change i.val < p.length - 1 + 1; omega⟩, hi⟩
    · have he : i = ⟨p.length, by omega⟩ := Fin.ext (by change i.val = p.length; omega)
      rw [he] at hi
      exact Or.inr hi.symm
  · rintro (hx | rfl)
    · exact p.contains_pop hpos hx
    · exact p.contains_last

theorem pop_contains_iff (p : Path H) (hpos : 0 < p.length) (x : V) :
    (p.pop hpos).Contains x ↔ p.Contains x ∧ x ≠ p.last := by
  constructor
  · intro hx
    refine ⟨p.contains_pop hpos hx, ?_⟩
    intro he
    exact p.pop_not_contains_last hpos (he ▸ hx)
  · rintro ⟨hx, hne⟩
    rcases (p.contains_iff_pop_or_last hpos x).1 hx with hpop | he
    · exact hpop
    · exact False.elim (hne he)

theorem pop_contains_iff_of_ne (p : Path H) (hpos : 0 < p.length) (x : V)
    (hne : x ≠ p.last) : (p.pop hpos).Contains x ↔ p.Contains x := by
  rw [pop_contains_iff]
  exact ⟨And.left, fun hx => ⟨hx, hne⟩⟩

/-- The pop follows the actual last edge in reverse. -/
theorem pop_edge (p : Path H) (hpos : 0 < p.length) : H.Edge (p.pop hpos).last p.last := by
  have he := p.adjacent ⟨p.length - 1, by omega⟩
  change H.Edge (p.vertex ⟨p.length - 1, by omega⟩) (p.vertex ⟨p.length, by omega⟩)
  simpa only [show p.length - 1 + 1 = p.length by omega] using he

theorem pop_last_level_gt (p : Path H) (hpos : 0 < p.length) :
    H.level p.last < H.level (p.pop hpos).last := H.decreases (p.pop_edge hpos)

end MaximumMatching.DDFS.Path

end DDFSStack

section DDFSRun

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

end DDFSRun

section DDFSMachine

/-! Concrete mode transitions for the DDFS stacks, collision recovery and
Barrier. Edge order is nondeterministic; every scan requires an unexplored
edge. The invariant and termination proofs are separate modules. -/
namespace MaximumMatching.DDFS.Machine
variable {V : Type} {H : LayeredGraph V}

inductive Mode (H : LayeredGraph V) where
  | normal
  | redRecovery (b : V) (savedRed savedGreen : Path H)
  | greenRecovery (b : V) (savedRed savedGreen : Path H)
  | disjoint
  | bottleneck (b : V) (redPath greenPath : Path H)

structure State (H : LayeredGraph V) where
  frame : SearchFrame H
  mode : Mode H

def initial (H : LayeredGraph V) (r g : V) : State H :=
  ⟨SearchFrame.initial H r g, .normal⟩

def Terminal (s : State H) : Prop :=
  (s.mode = .disjoint) ∨ ∃ b p q, s.mode = .bottleneck b p q

/-- All operations of the coordinated stack machine. Scanning a previously
visited destination skips it only during recovery; in normal mode the depth
invariant proves it is precisely the other activity center, hence a collision.
The candidate's outgoing edges are not scanned during recovery. -/
inductive Step : State H → State H → Prop where
  /-- Equal roots are a mathematical bottleneck. In the MV wrapper this branch
  corresponds to the immediate same-bud abort with no new petal (§4.3). -/
  | sameRoot (s : State H) (hn : s.mode = .normal)
      (hr : s.frame.red.length = 0) (hg : s.frame.green.length = 0)
      (heq : s.frame.red.last = s.frame.green.last) :
      Step s { s with mode := .bottleneck s.frame.red.last s.frame.red s.frame.green }
  | redMove (s : State H) (hn : s.mode = .normal)
      (hne : s.frame.red.last ≠ s.frame.green.last)
      (hsched : H.level s.frame.green.last ≤ H.level s.frame.red.last)
      (v : V) (he : H.Edge s.frame.red.last v)
      (hu : ¬s.frame.explored s.frame.red.last v)
      (hv : ¬s.frame.visited v ∨ v = s.frame.green.last) :
      Step s { frame := s.frame.advanceRed v he, mode := .normal }
  | greenMove (s : State H) (hn : s.mode = .normal)
      (hne : s.frame.red.last ≠ s.frame.green.last)
      (hsched : H.level s.frame.red.last < H.level s.frame.green.last)
      (v : V) (he : H.Edge s.frame.green.last v)
      (hu : ¬s.frame.explored s.frame.green.last v)
      (hv : ¬s.frame.visited v ∨ v = s.frame.red.last) :
      Step s { frame := s.frame.advanceGreen v he, mode := .normal }
  | bottom (s : State H) (hn : s.mode = .normal)
      (hne : s.frame.red.last ≠ s.frame.green.last)
      (hr : H.level s.frame.red.last = 0) (hg : H.level s.frame.green.last = 0) :
      Step s { s with mode := .disjoint }
  | collision (s : State H) (hn : s.mode = .normal)
      (heq : s.frame.red.last = s.frame.green.last)
      (hroots : s.frame.red.first ≠ s.frame.green.first) :
      Step s { s with mode := .redRecovery s.frame.red.last s.frame.red s.frame.green }
  | redPop (s : State H) (b : V) (p q : Path H)
      (hm : s.mode = .redRecovery b p q)
      (hpos : 0 < s.frame.red.length) (hbar : s.frame.red.last ≠ s.frame.barrier)
      (hex : s.frame.red.last = b ∨ s.frame.Exhausted s.frame.red.last) :
      Step s { frame := s.frame.backtrackRed hpos, mode := s.mode }
  | redSkip (s : State H) (b : V) (p q : Path H)
      (hm : s.mode = .redRecovery b p q)
      (hhigh : H.level b < H.level s.frame.red.last)
      (v : V) (he : H.Edge s.frame.red.last v)
      (hu : ¬s.frame.explored s.frame.red.last v) (hv : s.frame.visited v) :
      Step s { frame := s.frame.scanRed v, mode := s.mode }
  | redDeeper (s : State H) (b : V) (p q : Path H)
      (hm : s.mode = .redRecovery b p q)
      (hhigh : H.level b < H.level s.frame.red.last)
      (v : V) (he : H.Edge s.frame.red.last v)
      (hu : ¬s.frame.explored s.frame.red.last v) (hv : ¬s.frame.visited v)
      (hvhigh : H.level b < H.level v) :
      Step s { frame := s.frame.advanceRed v he, mode := s.mode }
  | redEscape (s : State H) (b : V) (p q : Path H)
      (hm : s.mode = .redRecovery b p q)
      (hhigh : H.level b < H.level s.frame.red.last)
      (v : V) (he : H.Edge s.frame.red.last v)
      (hu : ¬s.frame.explored s.frame.red.last v) (hv : ¬s.frame.visited v)
      (hvlow : H.level v ≤ H.level b) :
      Step s { frame := s.frame.advanceRed v he, mode := .normal }
  | redFail (s : State H) (b : V) (p q : Path H)
      (hm : s.mode = .redRecovery b p q)
      (hbar : s.frame.red.last = s.frame.barrier)
      (hex : s.frame.red.last = b ∨ s.frame.Exhausted s.frame.red.last) :
      Step s { frame := s.frame.restoreRed p b, mode := .greenRecovery b p q }
  | greenPop (s : State H) (b : V) (p q : Path H)
      (hm : s.mode = .greenRecovery b p q)
      (hpos : 0 < s.frame.green.length)
      (hex : s.frame.green.last = b ∨ s.frame.Exhausted s.frame.green.last) :
      Step s { frame := s.frame.backtrackGreen hpos, mode := s.mode }
  | greenSkip (s : State H) (b : V) (p q : Path H)
      (hm : s.mode = .greenRecovery b p q)
      (hhigh : H.level b < H.level s.frame.green.last)
      (v : V) (he : H.Edge s.frame.green.last v)
      (hu : ¬s.frame.explored s.frame.green.last v) (hv : s.frame.visited v) :
      Step s { frame := s.frame.scanGreen v, mode := s.mode }
  | greenDeeper (s : State H) (b : V) (p q : Path H)
      (hm : s.mode = .greenRecovery b p q)
      (hhigh : H.level b < H.level s.frame.green.last)
      (v : V) (he : H.Edge s.frame.green.last v)
      (hu : ¬s.frame.explored s.frame.green.last v) (hv : ¬s.frame.visited v)
      (hvhigh : H.level b < H.level v) :
      Step s { frame := s.frame.advanceGreen v he, mode := s.mode }
  | greenEscape (s : State H) (b : V) (p q : Path H)
      (hm : s.mode = .greenRecovery b p q)
      (hhigh : H.level b < H.level s.frame.green.last)
      (v : V) (he : H.Edge s.frame.green.last v)
      (hu : ¬s.frame.explored s.frame.green.last v) (hv : ¬s.frame.visited v)
      (hvlow : H.level v ≤ H.level b) :
      Step s { frame := s.frame.advanceGreen v he, mode := .normal }
  | greenFail (s : State H) (b : V) (p q : Path H)
      (hm : s.mode = .greenRecovery b p q)
      (hroot : s.frame.green.length = 0)
      (hex : s.frame.green.last = b ∨ s.frame.Exhausted s.frame.green.last) :
      Step s { s with mode := .bottleneck b p q }

inductive Reachable (r g : V) : State H → Prop where
  | initial : Reachable r g (initial H r g)
  | step {s t} : Reachable r g s → Step s t → Reachable r g t

end MaximumMatching.DDFS.Machine

end DDFSMachine
