import MaximumMatching.PathLemmas

/-! Relative alternating paths, as in Definition 6.16.
The first edge is unmatched. The starting vertex need not be free: these are
paths from a blossom base, not augmenting paths in their own right.
-/
namespace MaximumMatching
variable {V : Type} {G : Graph V}

structure AltSegment (M : Matching G) where
  length : Nat
  vertex : Fin (length + 1) → V
  injective : ∀ i j, vertex i = vertex j → i = j
  adjacent : ∀ i : Fin length,
    G.Adj (vertex ⟨i.val, by omega⟩) (vertex ⟨i.val + 1, by omega⟩)
  alternating : ∀ i : Fin length,
    (M.mate (vertex ⟨i.val, by omega⟩) = some (vertex ⟨i.val + 1, by omega⟩)) ↔
      i.val % 2 = 1

namespace AltSegment
variable {M : Matching G}

def first (s : AltSegment M) : V := s.vertex ⟨0, by omega⟩
def last (s : AltSegment M) : V := s.vertex ⟨s.length, by omega⟩
def Contains (s : AltSegment M) (v : V) : Prop := ∃ i, s.vertex i = v

def trivial (M : Matching G) (v : V) : AltSegment M where
  length := 0
  vertex := fun _ => v
  injective := by intro i j _; apply Fin.ext; omega
  adjacent := by intro i; exact Fin.elim0 i
  alternating := by intro i; exact Fin.elim0 i

/-- A relative path is an ordinary rooted alternating path exactly when its
first vertex is free. -/
def fromFree (s : AltSegment M) (hf : M.Free s.first) : AltPath M where
  length := s.length
  vertex := s.vertex
  injective := s.injective
  adjacent := s.adjacent
  start_free := hf
  alternating := s.alternating

def take (s : AltSegment M) (k : Nat) (hk : k ≤ s.length) : AltSegment M where
  length := k
  vertex i := s.vertex ⟨i.val, by omega⟩
  injective := by
    intro i j h
    have hh := congrArg (fun x : Fin (s.length + 1) => x.val) (s.injective _ _ h)
    exact Fin.ext hh
  adjacent i := s.adjacent ⟨i.val, by omega⟩
  alternating i := s.alternating ⟨i.val, by omega⟩

/-- Remove an even-length prefix, preserving the unmatched-first convention. -/
def drop (s : AltSegment M) (k : Nat) (hk : k ≤ s.length) (he : k % 2 = 0) : AltSegment M where
  length := s.length - k
  vertex i := s.vertex ⟨k + i.val, by omega⟩
  injective := by
    intro i j h
    have hh := congrArg (fun x : Fin (s.length + 1) => x.val) (s.injective _ _ h)
    apply Fin.ext
    change k + i.val = k + j.val at hh
    omega
  adjacent i := by
    simpa only [Nat.add_assoc] using s.adjacent ⟨k + i.val, by omega⟩
  alternating i := by
    have hpar : (k + i.val) % 2 = i.val % 2 := by omega
    simpa only [Nat.add_assoc, hpar] using s.alternating ⟨k + i.val, by omega⟩

/-- An odd segment also starts with an unmatched edge when reversed. -/
def reverse (s : AltSegment M) (hs : s.length % 2 = 1) : AltSegment M where
  length := s.length
  vertex i := s.vertex ⟨s.length - i.val, by omega⟩
  injective := by
    intro i j h
    have hh := congrArg (fun x : Fin (s.length + 1) => x.val) (s.injective _ _ h)
    apply Fin.ext
    change s.length - i.val = s.length - j.val at hh
    omega
  adjacent i := by
    have h := G.symm (s.adjacent ⟨s.length - i.val - 1, by omega⟩)
    simpa only [show s.length - i.val - 1 = s.length - (i.val + 1) by omega,
      show s.length - (i.val + 1) + 1 = s.length - i.val by omega] using h
  alternating i := by
    have h := s.alternating ⟨s.length - i.val - 1, by omega⟩
    have he' : s.length - i.val - 1 = s.length - (i.val + 1) := by omega
    have hpar : (s.length - (i.val + 1)) % 2 = i.val % 2 := by omega
    have h' : (M.mate (s.vertex ⟨s.length - (i.val + 1), by omega⟩) =
        some (s.vertex ⟨s.length - i.val, by omega⟩)) ↔ i.val % 2 = 1 := by
      simpa only [he', show s.length - (i.val + 1) + 1 = s.length - i.val by omega, hpar] using h
    exact ⟨fun hm => h'.1 (M.symm hm), fun hi => M.symm (h'.2 hi)⟩

@[simp] theorem drop_first (s : AltSegment M) (k) (hk) (he) :
    (s.drop k hk he).first = s.vertex ⟨k, by omega⟩ := by simp [first, drop]

@[simp] theorem drop_last (s : AltSegment M) (k) (hk) (he) :
    (s.drop k hk he).last = s.last := by simp [last, drop, Nat.add_sub_of_le hk]

@[simp] theorem take_first (s : AltSegment M) (k) (hk) :
    (s.take k hk).first = s.first := rfl

@[simp] theorem take_last (s : AltSegment M) (k) (hk) :
    (s.take k hk).last = s.vertex ⟨k, by omega⟩ := rfl

@[simp] theorem reverse_first (s : AltSegment M) (hs) : (s.reverse hs).first = s.last := by
  simp [reverse, first, last]

@[simp] theorem reverse_last (s : AltSegment M) (hs) : (s.reverse hs).last = s.first := by
  simp [reverse, first, last]

end AltSegment

namespace AltPath
variable {M : Matching G}

/-- Extract the relative suffix after an even-indexed vertex. Simplicity and
alternation come from the original path; no base theorem is assumed. -/
def segment (p : AltPath M) (k : Nat) (hk : k ≤ p.length) (he : k % 2 = 0) : AltSegment M where
  length := p.length - k
  vertex i := p.vertex ⟨k + i.val, by omega⟩
  injective := by
    intro i j h
    have hh := congrArg (fun x : Fin (p.length + 1) => x.val) (p.injective _ _ h)
    apply Fin.ext
    change k + i.val = k + j.val at hh
    omega
  adjacent i := by
    have h := p.adjacent ⟨k + i.val, by omega⟩
    simpa only [Nat.add_assoc] using h
  alternating i := by
    have h := p.alternating ⟨k + i.val, by omega⟩
    have hpar : (k + i.val) % 2 = i.val % 2 := by omega
    simpa only [Nat.add_assoc, hpar] using h

@[simp] theorem segment_first (p : AltPath M) (k : Nat) (hk : k ≤ p.length) (he : k % 2 = 0) :
    (p.segment k hk he).first = p.vertex ⟨k, by omega⟩ := by simp [AltSegment.first, segment]

@[simp] theorem segment_last (p : AltPath M) (k : Nat) (hk : k ≤ p.length) (he : k % 2 = 0) :
    (p.segment k hk he).last = p.last := by
  simp only [AltSegment.last, segment, Nat.add_sub_of_le hk, last]

/-- Append a relative path to an even alternating prefix. The explicit
disjointness premise is exactly what remains to prove when expanding a blossom. -/
def appendSegment (p : AltPath M) (s : AltSegment M) (hp : p.length % 2 = 0)
    (hjoin : p.last = s.first)
    (hdis : ∀ (i : Fin (p.length + 1)) (j : Fin (s.length + 1)),
      0 < j.val → p.vertex i ≠ s.vertex j) : AltPath M where
  length := p.length + s.length
  vertex i := if h : i.val ≤ p.length then p.vertex ⟨i.val, by omega⟩
    else s.vertex ⟨i.val - p.length, by omega⟩
  injective := by
    intro i j hij
    split at hij <;> split at hij
    · have hh := congrArg (fun x : Fin (p.length + 1) => x.val) (p.injective _ _ hij)
      exact Fin.ext hh
    · exact False.elim (hdis ⟨i.val, by omega⟩ ⟨j.val - p.length, by omega⟩
        (by change 0 < j.val - p.length; omega) hij)
    · exact False.elim (hdis ⟨j.val, by omega⟩ ⟨i.val - p.length, by omega⟩
        (by change 0 < i.val - p.length; omega) hij.symm)
    · have hh := congrArg (fun x : Fin (s.length + 1) => x.val) (s.injective _ _ hij)
      apply Fin.ext
      dsimp only at hh
      omega
  adjacent := by
    intro i
    by_cases hi : i.val < p.length
    · simpa only [dite_eq_left (show i.val ≤ p.length by omega),
        dite_eq_left (show i.val + 1 ≤ p.length by omega)] using p.adjacent ⟨i.val, hi⟩
    · have hs := s.adjacent ⟨i.val - p.length, by omega⟩
      by_cases he : i.val = p.length
      · simp only [he, Nat.le_refl, dite_true, show ¬p.length + 1 ≤ p.length by omega, dite_false]
        change G.Adj p.last (s.vertex ⟨p.length + 1 - p.length, by omega⟩)
        rw [hjoin]
        simpa only [he, Nat.sub_self, Nat.zero_add, Nat.add_sub_cancel_left, AltSegment.first] using hs
      · simpa only [dite_eq_right (show ¬i.val ≤ p.length by omega),
          dite_eq_right (show ¬i.val + 1 ≤ p.length by omega),
          show i.val - p.length + 1 = i.val + 1 - p.length by omega] using hs
  start_free := by simpa only [Nat.zero_le, dite_true] using p.start_free
  alternating := by
    intro i
    by_cases hi : i.val < p.length
    · simpa only [dite_eq_left (show i.val ≤ p.length by omega),
        dite_eq_left (show i.val + 1 ≤ p.length by omega)] using p.alternating ⟨i.val, hi⟩
    · have hs := s.alternating ⟨i.val - p.length, by omega⟩
      have hpar : (i.val - p.length) % 2 = i.val % 2 := by omega
      by_cases he : i.val = p.length
      · simp only [he, Nat.le_refl, dite_true, show ¬p.length + 1 ≤ p.length by omega, dite_false]
        change (M.mate p.last = some (s.vertex ⟨p.length + 1 - p.length, by omega⟩)) ↔ p.length % 2 = 1
        rw [hjoin]
        simpa only [hpar, he, Nat.sub_self, Nat.zero_add, Nat.add_sub_cancel_left, AltSegment.first, hp] using hs
      · simpa only [dite_eq_right (show ¬i.val ≤ p.length by omega),
          dite_eq_right (show ¬i.val + 1 ≤ p.length by omega), hpar,
          show i.val - p.length + 1 = i.val + 1 - p.length by omega] using hs

@[simp] theorem appendSegment_length (p : AltPath M) (s : AltSegment M) (hp) (hj) (hd) :
    (p.appendSegment s hp hj hd).length = p.length + s.length := rfl

@[simp] theorem appendSegment_first (p : AltPath M) (s : AltSegment M) (hp) (hj) (hd) :
    (p.appendSegment s hp hj hd).first = p.first := by simp [first, appendSegment]

@[simp] theorem appendSegment_last (p : AltPath M) (s : AltSegment M) (hp) (hj) (hd) :
    (p.appendSegment s hp hj hd).last = s.last := by
  by_cases hz : s.length = 0
  · have hse : s.first = s.last := congrArg s.vertex (Fin.ext (by omega))
    simpa [last, appendSegment, hz] using hj.trans hse
  · simp only [last, appendSegment, dite_eq_right (by omega : ¬p.length + s.length ≤ p.length),
      Nat.add_sub_cancel_left, AltSegment.last]

theorem appendSegment_contains_iff (p : AltPath M) (s : AltSegment M) (hp) (hj) (hd) (v : V) :
    (∃ i, (p.appendSegment s hp hj hd).vertex i = v) ↔
      (∃ i, p.vertex i = v) ∨ s.Contains v := by
  constructor
  · rintro ⟨i, hi⟩
    change (if h : i.val ≤ p.length then p.vertex ⟨i.val, _⟩ else s.vertex ⟨i.val - p.length, _⟩) = v at hi
    split at hi
    · exact Or.inl ⟨_, hi⟩
    · exact Or.inr ⟨_, hi⟩
  · rintro (⟨i, hi⟩ | ⟨j, hjv⟩)
    · refine ⟨⟨i.val, by change i.val < p.length + s.length + 1; omega⟩, ?_⟩
      simpa [appendSegment, show i.val ≤ p.length by omega] using hi
    · refine ⟨⟨p.length + j.val, by change p.length + j.val < p.length + s.length + 1; omega⟩, ?_⟩
      by_cases hj0 : j.val = 0
      · have hjfirst : s.first = v := by
          have he : j = ⟨0, by omega⟩ := Fin.ext hj0
          rw [he] at hjv
          exact hjv
        simpa [appendSegment, hj0, last] using hj.trans hjfirst
      · simpa [appendSegment, show ¬p.length + j.val ≤ p.length by omega] using hjv

end AltPath
end MaximumMatching
