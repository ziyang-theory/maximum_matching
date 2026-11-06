import MaximumMatching.Foundations

section DDFS

/-!
Layered-graph specifications and structural facts for the DDFS subroutine.
Source: Vazirani, arXiv:2012.03582v1, §2, pp.6–8.

These definitions do not implement the two DFS machines, recoloring or Barrier.
The conclusions below concern paths and bottlenecks in their intended input graph.
-/
namespace MaximumMatching.DDFS

/-- Every directed edge strictly lowers the layer. Finiteness and bottom
reachability are separate properties; no algorithmic conclusion is a field. -/
structure LayeredGraph (V : Type) where
  Edge : V → V → Prop
  level : V → Nat
  decreases : ∀ {u v}, Edge u v → level v < level u

/-- A directed path with `length` edges. Vertex simplicity is proved below. -/
structure Path {V : Type} (H : LayeredGraph V) where
  length : Nat
  vertex : Fin (length + 1) → V
  adjacent : ∀ i : Fin length,
    H.Edge (vertex ⟨i.val, by omega⟩) (vertex ⟨i.val + 1, by omega⟩)

namespace Path
variable {V : Type} {H : LayeredGraph V}

def first (p : Path H) : V := p.vertex ⟨0, by omega⟩
def last (p : Path H) : V := p.vertex ⟨p.length, by omega⟩
def Contains (p : Path H) (v : V) : Prop := ∃ i, p.vertex i = v

def ToBottom (p : Path H) (r : V) : Prop := p.first = r ∧ H.level p.last = 0

def Disjoint (p q : Path H) : Prop := ∀ v, p.Contains v → ¬ q.Contains v

def trivial (H : LayeredGraph V) (v : V) : Path H where
  length := 0
  vertex := fun _ => v
  adjacent := by intro i; exact Fin.elim0 i

theorem contains_first (p : Path H) : p.Contains p.first := ⟨⟨0, by omega⟩, rfl⟩
theorem contains_last (p : Path H) : p.Contains p.last := ⟨⟨p.length, by omega⟩, rfl⟩

/-- Each edge consumes at least one natural-number layer. -/
theorem level_drop (p : Path H) (i k : Nat) (hik : i + k ≤ p.length) :
    H.level (p.vertex ⟨i + k, by omega⟩) + k ≤
      H.level (p.vertex ⟨i, by omega⟩) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hprev := ih (by omega)
    have hstep := H.decreases (p.adjacent ⟨i + k, by omega⟩)
    change H.level (p.vertex ⟨i + k + 1, _⟩) <
      H.level (p.vertex ⟨i + k, _⟩) at hstep
    have heq : i + (k + 1) = i + k + 1 := by omega
    simp only [heq]
    omega

/-- Earlier vertices have strictly greater layers. -/
theorem level_strict (p : Path H) (i j : Fin (p.length + 1))
    (hij : i.val < j.val) : H.level (p.vertex j) < H.level (p.vertex i) := by
  have h := p.level_drop i.val (j.val - i.val) (by omega)
  have heq : (⟨i.val + (j.val - i.val), by omega⟩ : Fin (p.length + 1)) = j :=
    by apply Fin.ext; simp only; omega
  simp only [heq, Fin.eta] at h
  omega

/-- Directed paths in a strictly layered graph are vertex-simple. -/
theorem injective (p : Path H) (i j : Fin (p.length + 1))
    (h : p.vertex i = p.vertex j) : i = j := by
  apply Fin.ext
  by_cases hij : i.val < j.val
  · have hd := p.level_strict i j hij
    rw [h] at hd
    omega
  · by_cases hji : j.val < i.val
    · have hd := p.level_strict j i hji
      rw [h] at hd
      omega
    · omega

/-- Equal-layer vertices lying on the same directed path are the same vertex. -/
theorem eq_of_contains_level_eq (p : Path H) {u v : V}
    (hu : p.Contains u) (hv : p.Contains v) (hl : H.level u = H.level v) : u = v := by
  obtain ⟨i, rfl⟩ := hu
  obtain ⟨j, rfl⟩ := hv
  have hij : i.val = j.val := by
    by_cases h : i.val < j.val
    · have := p.level_strict i j h
      omega
    · by_cases h' : j.val < i.val
      · have := p.level_strict j i h'
        omega
      · omega
  have := Fin.ext hij
  rw [this]

/-- A path has no more edges than the level of its first vertex. -/
theorem length_le_first_level (p : Path H) : p.length ≤ H.level p.first := by
  have h := p.level_drop 0 p.length (by omega)
  simp only [Nat.zero_add] at h
  exact Nat.le_trans (Nat.le_add_left _ _) h

/-- The layer of every vertex on a path is bounded by its first layer. -/
theorem level_le_first (p : Path H) {v : V} (hv : p.Contains v) :
    H.level v ≤ H.level p.first := by
  obtain ⟨i, rfl⟩ := hv
  have h := p.level_drop 0 i.val (by omega)
  simpa only [Nat.zero_add, Fin.eta, first] using
    Nat.le_trans (Nat.le_add_right _ _) h

end Path

variable {V : Type} (H : LayeredGraph V)

/-- The source's DDFS Requirement, p.6. -/
def ReachBottom : Prop := ∀ v, ∃ p : Path H, p.ToBottom v

/-- A bottleneck is on every root-to-bottom path from either root. -/
def Bottleneck (r g b : V) : Prop :=
  ∀ p : Path H, (p.ToBottom r ∨ p.ToBottom g) → p.Contains b

/-- Highest refers to the graph's layer, not a choice of traversal order. -/
def HighestBottleneck (r g b : V) : Prop :=
  Bottleneck H r g b ∧ ∀ c, Bottleneck H r g c → H.level c ≤ H.level b

/-- Highest-bottleneck uniqueness needs a real root-to-bottom path;
without reachability the universal bottleneck predicate could be vacuous. -/
theorem highestBottleneck_unique (r g b c : V)
    (hr : ∃ p : Path H, p.ToBottom r)
    (hb : HighestBottleneck H r g b) (hc : HighestBottleneck H r g c) : b = c := by
  obtain ⟨p, hp⟩ := hr
  have hpB := hb.1 p (Or.inl hp)
  have hpC := hc.1 p (Or.inl hp)
  have hbc := hb.2 c hc.1
  have hcb := hc.2 b hb.1
  exact p.eq_of_contains_level_eq hpB hpC (by omega)

/-- A nonempty predicate on a bounded natural interval has a greatest witness. -/
private theorem bounded_maximum (P : Nat → Prop) (n : Nat)
    (hex : ∃ i, i ≤ n ∧ P i) :
    ∃ i, i ≤ n ∧ P i ∧ ∀ j, j ≤ n → P j → j ≤ i := by
  classical
  induction n with
  | zero =>
    obtain ⟨i, hi, hp⟩ := hex
    have heq : i = 0 := by omega
    subst i
    exact ⟨0, Nat.le_refl 0, hp, fun j hj _ => hj⟩
  | succ n ih =>
    by_cases hp : P (n + 1)
    · exact ⟨n + 1, Nat.le_refl _, hp, fun j hj _ => hj⟩
    · have hex' : ∃ i, i ≤ n ∧ P i := by
        obtain ⟨i, hi, hip⟩ := hex
        refine ⟨i, ?_, hip⟩
        by_cases h : i ≤ n
        · exact h
        · have : i = n + 1 := by omega
          exact False.elim (hp (this ▸ hip))
      obtain ⟨i, hi, hip, hmax⟩ := ih hex'
      refine ⟨i, by omega, hip, ?_⟩
      intro j hj hjp
      apply hmax j
      · by_cases h : j ≤ n
        · exact h
        · have : j = n + 1 := by omega
          exact False.elim (hp (this ▸ hjp))
      · exact hjp

/-- Any existing bottleneck has a highest representative. The bound comes from
one actual root-to-bottom path, so no finiteness assumption on all of `V` is needed. -/
theorem highestBottleneck_exists (r g : V)
    (hr : ∃ p : Path H, p.ToBottom r) (hex : ∃ b, Bottleneck H r g b) :
    ∃ b, HighestBottleneck H r g b := by
  obtain ⟨p, hp⟩ := hr
  have bound : ∀ b, Bottleneck H r g b → H.level b ≤ H.level r := by
    intro b hb
    have h := p.level_le_first (hb p (Or.inl hp))
    rw [hp.1] at h
    exact h
  obtain ⟨b, hb⟩ := hex
  obtain ⟨k, _, ⟨c, hc, hck⟩, hmax⟩ :=
    bounded_maximum (fun k => ∃ c, Bottleneck H r g c ∧ H.level c = k)
      (H.level r) ⟨H.level b, bound b hb, b, hb, rfl⟩
  refine ⟨c, hc, ?_⟩
  intro d hd
  rw [hck]
  exact hmax (H.level d) (bound d hd) ⟨d, hd, rfl⟩

/-- The DDFS Case-2 witness excludes every bottleneck (p.6).
This does not assert that the concrete DDFS procedure finds such witnesses. -/
theorem disjoint_paths_no_bottleneck (r g : V) (p q : Path H)
    (hp : p.ToBottom r) (hq : q.ToBottom g) (hd : p.Disjoint q) :
    ∀ b, ¬ Bottleneck H r g b := by
  intro b hb
  exact hd b (hb p (Or.inl hp)) (hb q (Or.inr hq))

/-- The two terminal paths in Case 2 necessarily have different terminal vertices. -/
theorem disjoint_paths_distinct_bottoms (p q : Path H) (hd : p.Disjoint q) :
    p.last ≠ q.last := by
  intro h
  exact hd p.last p.contains_last (h ▸ q.contains_last)

/-- A boundary case: distinct vertices already at level zero admit disjoint
zero-edge paths and therefore have no bottleneck. -/
theorem distinct_bottom_roots_no_bottleneck (r g : V) (hr : H.level r = 0)
    (hg : H.level g = 0) (hne : r ≠ g) : ∀ b, ¬ Bottleneck H r g b := by
  apply disjoint_paths_no_bottleneck H r g (Path.trivial H r) (Path.trivial H g)
  · exact ⟨rfl, hr⟩
  · exact ⟨rfl, hg⟩
  · intro v hv hv'
    obtain ⟨i, hi⟩ := hv
    obtain ⟨j, hj⟩ := hv'
    exact hne (hi.trans hj.symm)

/-! A checked obstruction to treating DDFS as two ordinary DFSs with irrevocable
ownership. The graph has disjoint solutions even though a permitted greedy red
path occupies the green root's only successor. This is not a counterexample to MV. -/
namespace OwnershipExample

inductive Vertex where
  | red | green | shared | redBottom | greenBottom
  deriving DecidableEq, Repr

open Vertex

def edge (u v : Vertex) : Prop :=
  (u = red ∧ v = shared) ∨ (u = red ∧ v = redBottom) ∨
  (u = green ∧ v = shared) ∨ (u = shared ∧ v = greenBottom)

def layer : Vertex → Nat
  | red | green => 2
  | shared => 1
  | redBottom | greenBottom => 0

def graph : LayeredGraph Vertex where
  Edge := edge
  level := layer
  decreases := by
    intro u v h
    cases u <;> cases v <;> simp_all [edge, layer]

def redSolution : Path graph where
  length := 1
  vertex := fun i => if i.val = 0 then red else redBottom
  adjacent := by
    intro i
    simp [graph, edge]

def greenSolution : Path graph where
  length := 2
  vertex := fun i => if i.val = 0 then green else if i.val = 1 then shared else greenBottom
  adjacent := by
    intro i
    have hi : i.val = 0 ∨ i.val = 1 := by omega
    rcases hi with hi | hi <;> simp [graph, edge, hi]

theorem solutions_disjoint : redSolution.Disjoint greenSolution := by
  intro v hv hv'
  obtain ⟨i, hi⟩ := hv
  obtain ⟨j, hj⟩ := hv'
  have hred : v = red ∨ v = redBottom := by
    by_cases h : i.val = 0
    · exact Or.inl (by simpa [redSolution, h] using hi.symm)
    · exact Or.inr (by simpa [redSolution, h] using hi.symm)
  have hgreen : v = green ∨ v = shared ∨ v = greenBottom := by
    by_cases h : j.val = 0
    · exact Or.inl (by simpa [greenSolution, h] using hj.symm)
    · by_cases h' : j.val = 1
      · exact Or.inr (Or.inl (by simpa [greenSolution, h, h'] using hj.symm))
      · exact Or.inr (Or.inr (by simpa [greenSolution, h, h'] using hj.symm))
  rcases hred with hred | hred <;>
    rcases hgreen with hgreen | hgreen | hgreen <;> simp_all

theorem no_bottleneck : ∀ b, ¬ Bottleneck graph red green b :=
  disjoint_paths_no_bottleneck graph red green redSolution greenSolution
    ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ solutions_disjoint

/-- The red prefix when green next attempts to enter `shared`. -/
def redAtCollision : Path graph where
  length := 1
  vertex := fun i => if i.val = 0 then red else shared
  adjacent := by
    intro i
    simp [graph, edge]

/-- Every first step available to green is already owned by the red prefix. -/
theorem green_successors_owned : ∀ v, graph.Edge green v → redAtCollision.Contains v := by
  intro v hv
  have heq : v = shared := by simpa [graph, edge] using hv
  subst v
  exact ⟨⟨1, by decide⟩, rfl⟩

/-- The fixture satisfies the source's reachability requirement. -/
theorem reaches_bottom : ReachBottom graph := by
  intro v
  cases v with
  | red => exact ⟨redSolution, rfl, rfl⟩
  | green => exact ⟨greenSolution, rfl, rfl⟩
  | shared =>
    let p : Path graph := {
      length := 1
      vertex := fun i => if i.val = 0 then shared else greenBottom
      adjacent := by
        intro i
        simp [graph, edge]
    }
    exact ⟨p, rfl, rfl⟩
  | redBottom => exact ⟨Path.trivial graph redBottom, rfl, rfl⟩
  | greenBottom => exact ⟨Path.trivial graph greenBottom, rfl, rfl⟩

end OwnershipExample

end MaximumMatching.DDFS

end DDFS

section DDFSPaths

/-! Directed path operations for the two-path/bottleneck certificate. -/
namespace MaximumMatching.DDFS.Path
variable {V : Type} {H : LayeredGraph V}

def To (p : Path H) (T : V → Prop) (r : V) : Prop := p.first = r ∧ T p.last

def take (p : Path H) (k : Nat) (hk : k ≤ p.length) : Path H where
  length := k
  vertex i := p.vertex ⟨i.val, by omega⟩
  adjacent i := p.adjacent ⟨i.val, by omega⟩

def drop (p : Path H) (k : Nat) (hk : k ≤ p.length) : Path H where
  length := p.length - k
  vertex i := p.vertex ⟨k + i.val, by omega⟩
  adjacent i := by
    have h := p.adjacent ⟨k + i.val, by omega⟩
    simpa only [Nat.add_assoc] using h

@[simp] theorem take_first (p : Path H) (k : Nat) (hk : k ≤ p.length) :
    (p.take k hk).first = p.first := rfl
@[simp] theorem take_last (p : Path H) (k : Nat) (hk : k ≤ p.length) :
    (p.take k hk).last = p.vertex ⟨k, by omega⟩ := rfl
@[simp] theorem drop_first (p : Path H) (k : Nat) (hk : k ≤ p.length) :
    (p.drop k hk).first = p.vertex ⟨k, by omega⟩ := by simp [first, drop]
@[simp] theorem drop_last (p : Path H) (k : Nat) (hk : k ≤ p.length) :
    (p.drop k hk).last = p.last := by simp [last, drop, Nat.add_sub_of_le hk]

def prepend (u : V) (p : Path H) (he : H.Edge u p.first) : Path H where
  length := p.length + 1
  vertex i := if h : i.val = 0 then u else p.vertex ⟨i.val - 1, by omega⟩
  adjacent i := by
    by_cases hi : i.val = 0
    · simpa [hi, first] using he
    · have hh := p.adjacent ⟨i.val - 1, by omega⟩
      have hidx : i.val - 1 + 1 = i.val := by omega
      simpa only [dite_eq_right hi, show ¬i.val + 1 = 0 by omega,
        dite_false, Nat.add_sub_cancel, hidx] using hh

@[simp] theorem prepend_first (u : V) (p : Path H) (he : H.Edge u p.first) :
    (prepend u p he).first = u := rfl
@[simp] theorem prepend_last (u : V) (p : Path H) (he : H.Edge u p.first) :
    (prepend u p he).last = p.last := by simp [last, prepend]

theorem contains_take (p : Path H) (k : Nat) (hk : k ≤ p.length) {v : V}
    (hv : (p.take k hk).Contains v) : p.Contains v := by
  obtain ⟨i, hi⟩ := hv
  exact ⟨⟨i.val, by have := i.isLt; change i.val < k + 1 at this; omega⟩, hi⟩

theorem contains_drop (p : Path H) (k : Nat) (hk : k ≤ p.length) {v : V}
    (hv : (p.drop k hk).Contains v) : p.Contains v := by
  obtain ⟨i, hi⟩ := hv
  exact ⟨⟨k + i.val, by have := i.isLt; change i.val < p.length - k + 1 at this; omega⟩, hi⟩

theorem contains_prepend_iff (u : V) (p : Path H) (he : H.Edge u p.first) (v : V) :
    (prepend u p he).Contains v ↔ v = u ∨ p.Contains v := by
  constructor
  · rintro ⟨i, hi⟩
    change (if h : i.val = 0 then u else p.vertex ⟨i.val - 1, _⟩) = v at hi
    split at hi
    · exact Or.inl hi.symm
    · exact Or.inr ⟨_, hi⟩
  · intro hv
    rcases hv with rfl | ⟨i, hi⟩
    · exact ⟨⟨0, by omega⟩, rfl⟩
    · refine ⟨⟨i.val + 1, by have := i.isLt; change i.val + 1 < p.length + 1 + 1; omega⟩, ?_⟩
      simpa [prepend] using hi

/-- Concatenation is a valid directed path. Its simplicity follows from layer descent. -/
def append (p q : Path H) (he : p.last = q.first) : Path H where
  length := p.length + q.length
  vertex i := if h : i.val ≤ p.length then p.vertex ⟨i.val, by omega⟩
    else q.vertex ⟨i.val - p.length, by omega⟩
  adjacent i := by
    by_cases hi : i.val < p.length
    · simpa only [dite_eq_left (show i.val ≤ p.length by omega),
        dite_eq_left (show i.val + 1 ≤ p.length by omega)] using p.adjacent ⟨i.val, hi⟩
    · by_cases heq : i.val = p.length
      · have hh := q.adjacent ⟨0, by omega⟩
        simp only [heq, Nat.le_refl, dite_true, show ¬p.length + 1 ≤ p.length by omega,
          dite_false, Nat.add_sub_cancel_left]
        change H.Edge p.last (q.vertex ⟨1, by omega⟩)
        rw [he]
        exact hh
      · have hh := q.adjacent ⟨i.val - p.length, by omega⟩
        have hidx : i.val + 1 - p.length = i.val - p.length + 1 := by omega
        simpa only [dite_eq_right (show ¬i.val ≤ p.length by omega),
          dite_eq_right (show ¬i.val + 1 ≤ p.length by omega), hidx] using hh

@[simp] theorem append_first (p q : Path H) (he : p.last = q.first) :
    (p.append q he).first = p.first := by simp [first, append]
@[simp] theorem append_last (p q : Path H) (he : p.last = q.first) :
    (p.append q he).last = q.last := by
  by_cases hq : q.length = 0
  · have hqeq : q.first = q.last := congrArg q.vertex (Fin.ext (by omega))
    simpa [last, append, hq] using he.trans hqeq
  · simp [last, append, show ¬p.length + q.length ≤ p.length by omega]

theorem contains_append_iff (p q : Path H) (he : p.last = q.first) (v : V) :
    (p.append q he).Contains v ↔ p.Contains v ∨ q.Contains v := by
  constructor
  · rintro ⟨i, hi⟩
    change (if h : i.val ≤ p.length then p.vertex ⟨i.val, _⟩ else q.vertex ⟨i.val - p.length, _⟩) = v at hi
    split at hi
    · exact Or.inl ⟨_, hi⟩
    · exact Or.inr ⟨_, hi⟩
  · intro hv
    rcases hv with ⟨i, hi⟩ | ⟨j, hj⟩
    · refine ⟨⟨i.val, by change i.val < p.length + q.length + 1; omega⟩, ?_⟩
      simpa [append, show i.val ≤ p.length by omega] using hi
    · refine ⟨⟨p.length + j.val, by change p.length + j.val < p.length + q.length + 1; omega⟩, ?_⟩
      by_cases hj0 : j.val = 0
      · have hjfirst : q.first = v := by
          have hj_eq : j = ⟨0, by omega⟩ := Fin.ext hj0
          rw [hj_eq] at hj
          exact hj
        simpa [append, hj0, last] using he.trans hjfirst
      · simpa [append, show ¬p.length + j.val ≤ p.length by omega] using hj

theorem last_level_le (p : Path H) {v : V} (hv : p.Contains v) :
    H.level p.last ≤ H.level v := by
  obtain ⟨i, hi⟩ := hv
  have h := p.level_drop i.val (p.length - i.val) (by omega)
  have he : i.val + (p.length - i.val) = p.length := by omega
  simp only [he] at h
  rw [← hi]
  exact Nat.le_trans (Nat.le_add_right _ _) h

theorem contains_eq_first_of_level_ge (p : Path H) {v : V} (hv : p.Contains v)
    (hl : H.level p.first ≤ H.level v) : v = p.first := by
  have he := Nat.le_antisymm (p.level_le_first hv) hl
  exact p.eq_of_contains_level_eq hv p.contains_first he

theorem disjoint_symm {p q : Path H} (h : p.Disjoint q) : q.Disjoint p := by
  intro v hq hp
  exact h v hp hq

end MaximumMatching.DDFS.Path

end DDFSPaths
