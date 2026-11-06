import MaximumMatching.BaseGeometry
import MaximumMatching.BlossomStructure
import MaximumMatching.Foundations

section Segment

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

end Segment

section SegmentSplice

/-! Simple splices into relative alternating paths. These generalize the
free-rooted splice operations: only the retained prefix needs a free root. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The replacement path does not meet the strict suffix being retained. -/
def SegmentSuffixDisjoint (q : AltPath M) (p : AltSegment M) (k : Nat) : Prop :=
  ∀ (i : Fin (q.length + 1)) (j : Fin (p.length + 1)),
    k < j.val → q.vertex i ≠ p.vertex j

/-- Replace a prefix by a same-parity path with the same endpoint, provided its
vertices avoid the retained suffix. The fresh start may be a different free vertex. -/
def spliceSegment (q : AltPath M) (p : AltSegment M) (k : Nat) (hk : k ≤ p.length)
    (hjoin : q.last = p.vertex ⟨k, by omega⟩)
    (hpar : q.length % 2 = k % 2) (hdisj : q.SegmentSuffixDisjoint p k) : AltPath M where
  length := q.length + (p.length - k)
  vertex := fun i => if h : i.val ≤ q.length then q.vertex ⟨i.val, by omega⟩
    else p.vertex ⟨i.val - q.length + k, by omega⟩
  injective := by
    intro i j he
    split at he <;> split at he
    · have hi := q.injective _ _ he
      apply Fin.ext
      exact congrArg (fun x : Fin (q.length + 1) => x.val) hi
    · exact False.elim (hdisj _ _ (by change k < j.val - q.length + k; omega) he)
    · exact False.elim (hdisj _ _ (by change k < i.val - q.length + k; omega) he.symm)
    · have hi := p.injective _ _ he
      have heq : i.val - q.length + k = j.val - q.length + k :=
        congrArg (fun x : Fin (p.length + 1) => x.val) hi
      apply Fin.ext
      omega
  adjacent := by
    intro i
    by_cases hi : i.val < q.length
    · simpa only [dite_eq_left (show i.val ≤ q.length by omega),
        dite_eq_left (show i.val + 1 ≤ q.length by omega)] using q.adjacent ⟨i.val, hi⟩
    · by_cases heq : i.val = q.length
      · simp only [heq, Nat.le_refl, dite_true,
          show ¬q.length + 1 ≤ q.length by omega, dite_false]
        change G.Adj q.last _
        rw [hjoin]
        have he : q.length + 1 - q.length + k = k + 1 := by omega
        simpa only [he] using p.adjacent ⟨k, by omega⟩
      · simp only [dite_eq_right (show ¬i.val ≤ q.length by omega),
          dite_eq_right (show ¬i.val + 1 ≤ q.length by omega)]
        have he : i.val + 1 - q.length + k = (i.val - q.length + k) + 1 := by omega
        simpa only [he] using p.adjacent ⟨i.val - q.length + k, by omega⟩
  start_free := by simpa using q.start_free
  alternating := by
    intro i
    by_cases hi : i.val < q.length
    · simpa only [dite_eq_left (show i.val ≤ q.length by omega),
        dite_eq_left (show i.val + 1 ≤ q.length by omega)] using q.alternating ⟨i.val, hi⟩
    · by_cases heq : i.val = q.length
      · simp only [heq, Nat.le_refl, dite_true,
          show ¬q.length + 1 ≤ q.length by omega, dite_false]
        change (M.mate q.last = some _) ↔ q.length % 2 = 1
        rw [hjoin, hpar]
        have he : q.length + 1 - q.length + k = k + 1 := by omega
        simpa only [he] using p.alternating ⟨k, by omega⟩
      · simp only [dite_eq_right (show ¬i.val ≤ q.length by omega),
          dite_eq_right (show ¬i.val + 1 ≤ q.length by omega)]
        have he : i.val + 1 - q.length + k = (i.val - q.length + k) + 1 := by omega
        have hp : (i.val - q.length + k) % 2 = i.val % 2 := by omega
        simpa only [he, hp] using p.alternating ⟨i.val - q.length + k, by omega⟩

@[simp] theorem spliceSegment_length (q : AltPath M) (p : AltSegment M) (k : Nat) (hk : k ≤ p.length)
    (hjoin : q.last = p.vertex ⟨k, by omega⟩)
    (hpar : q.length % 2 = k % 2) (hdisj : q.SegmentSuffixDisjoint p k) :
    (q.spliceSegment p k hk hjoin hpar hdisj).length = q.length + (p.length - k) := rfl

@[simp] theorem spliceSegment_last (q : AltPath M) (p : AltSegment M) (k : Nat) (hk : k ≤ p.length)
    (hjoin : q.last = p.vertex ⟨k, by omega⟩)
    (hpar : q.length % 2 = k % 2) (hdisj : q.SegmentSuffixDisjoint p k) :
    (q.spliceSegment p k hk hjoin hpar hdisj).last = p.last := by
  simp only [last, spliceSegment]
  split
  · rename_i h
    have hlen : k = p.length := by omega
    have hnew : q.length + (p.length - k) = q.length := by omega
    simp only [hnew]
    simpa only [last, AltSegment.last, hlen] using hjoin
  · have he : q.length + (p.length - k) - q.length + k = p.length := by omega
    congr 1
    exact Fin.ext he

theorem spliceSegment_parity (q : AltPath M) (p : AltSegment M) (k : Nat) (hk : k ≤ p.length)
    (hjoin : q.last = p.vertex ⟨k, by omega⟩)
    (hpar : q.length % 2 = k % 2) (hdisj : q.SegmentSuffixDisjoint p k) :
    (q.spliceSegment p k hk hjoin hpar hdisj).length % 2 = p.length % 2 := by
  simp only [spliceSegment_length]
  omega

/-- The replacement path avoids the segment traversed in reverse. -/
def SegmentReverseDisjoint (q : AltPath M) (p : AltSegment M) (k j : Nat) : Prop :=
  ∀ (a : Fin (q.length + 1)) (b : Fin (p.length + 1)),
    k ≤ b.val → b.val < j → q.vertex a ≠ p.vertex b

/-- Join an odd-length path to an even-indexed vertex, then follow a segment backward. -/
def spliceReverseSegment (q : AltPath M) (p : AltSegment M) (k j : Nat) (hkj : k ≤ j) (hj : j ≤ p.length)
    (hjoin : q.last = p.vertex ⟨j, by omega⟩)
    (hqo : q.length % 2 = 1) (hje : j % 2 = 0)
    (hdisj : q.SegmentReverseDisjoint p k j) : AltPath M where
  length := q.length + (j - k)
  vertex := fun a => if h : a.val ≤ q.length then q.vertex ⟨a.val, by omega⟩
    else p.vertex ⟨j - (a.val - q.length), by omega⟩
  injective := by
    intro a b he
    split at he <;> split at he
    · have hh := q.injective _ _ he
      apply Fin.ext
      exact congrArg (fun x : Fin (q.length + 1) => x.val) hh
    · exact False.elim (hdisj _ _ (by change k ≤ j - (b.val - q.length); omega)
        (by change j - (b.val - q.length) < j; omega) he)
    · exact False.elim (hdisj _ _ (by change k ≤ j - (a.val - q.length); omega)
        (by change j - (a.val - q.length) < j; omega) he.symm)
    · have hh := p.injective _ _ he
      have heq : j - (a.val - q.length) = j - (b.val - q.length) :=
        congrArg (fun x : Fin (p.length + 1) => x.val) hh
      apply Fin.ext
      omega
  adjacent := by
    intro a
    by_cases ha : a.val < q.length
    · simpa only [dite_eq_left (show a.val ≤ q.length by omega),
        dite_eq_left (show a.val + 1 ≤ q.length by omega)] using q.adjacent ⟨a.val, ha⟩
    · by_cases heq : a.val = q.length
      · simp only [heq, Nat.le_refl, dite_true,
          show ¬q.length + 1 ≤ q.length by omega, dite_false]
        change G.Adj q.last _
        rw [hjoin]
        have he : j - (q.length + 1 - q.length) = j - 1 := by omega
        have he' : j - 1 + 1 = j := by omega
        simpa only [he, he'] using G.symm (p.adjacent ⟨j - 1, by omega⟩)
      · simp only [dite_eq_right (show ¬a.val ≤ q.length by omega),
          dite_eq_right (show ¬a.val + 1 ≤ q.length by omega)]
        have he : j - (a.val + 1 - q.length) + 1 = j - (a.val - q.length) := by omega
        simpa only [he] using G.symm (p.adjacent ⟨j - (a.val + 1 - q.length), by omega⟩)
  start_free := by simpa using q.start_free
  alternating := by
    intro a
    by_cases ha : a.val < q.length
    · simpa only [dite_eq_left (show a.val ≤ q.length by omega),
        dite_eq_left (show a.val + 1 ≤ q.length by omega)] using q.alternating ⟨a.val, ha⟩
    · by_cases heq : a.val = q.length
      · simp only [heq, Nat.le_refl, dite_true,
          show ¬q.length + 1 ≤ q.length by omega, dite_false]
        change (M.mate q.last = some _) ↔ q.length % 2 = 1
        rw [hjoin]
        have hm : M.mate (p.vertex ⟨j, by omega⟩) = some (p.vertex ⟨j - 1, by omega⟩) := by
          have hh := (p.alternating ⟨j - 1, by omega⟩).2 (by change (j - 1) % 2 = 1; omega)
          have hh' := M.symm hh
          simpa only [show j - 1 + 1 = j by omega] using hh'
        have he : j - (q.length + 1 - q.length) = j - 1 := by omega
        constructor
        · intro _; exact hqo
        · intro _; simpa only [he] using hm
      · simp only [dite_eq_right (show ¬a.val ≤ q.length by omega),
          dite_eq_right (show ¬a.val + 1 ≤ q.length by omega)]
        have he : j - (a.val + 1 - q.length) + 1 = j - (a.val - q.length) := by omega
        have hpar : (j - (a.val + 1 - q.length)) % 2 = a.val % 2 := by omega
        have hh := p.alternating ⟨j - (a.val + 1 - q.length), by omega⟩
        rw [hpar] at hh
        constructor
        · intro hm
          apply hh.1
          simpa only [he] using M.symm hm
        · intro hp
          simpa only [he] using M.symm (hh.2 hp)

@[simp] theorem spliceReverseSegment_length (q : AltPath M) (p : AltSegment M) (k j : Nat)
    (hkj : k ≤ j) (hj : j ≤ p.length) (hjoin : q.last = p.vertex ⟨j, by omega⟩)
    (hqo : q.length % 2 = 1) (hje : j % 2 = 0) (hdisj : q.SegmentReverseDisjoint p k j) :
    (q.spliceReverseSegment p k j hkj hj hjoin hqo hje hdisj).length = q.length + (j - k) := rfl

@[simp] theorem spliceReverseSegment_last (q : AltPath M) (p : AltSegment M) (k j : Nat)
    (hkj : k ≤ j) (hj : j ≤ p.length) (hjoin : q.last = p.vertex ⟨j, by omega⟩)
    (hqo : q.length % 2 = 1) (hje : j % 2 = 0) (hdisj : q.SegmentReverseDisjoint p k j) :
    (q.spliceReverseSegment p k j hkj hj hjoin hqo hje hdisj).last = p.vertex ⟨k, by omega⟩ := by
  simp only [last, spliceReverseSegment]
  split
  · have hlen : k = j := by omega
    have hnew : q.length + (j - k) = q.length := by omega
    simp only [hnew]
    exact hlen ▸ hjoin
  · have he : j - (q.length + (j - k) - q.length) = k := by omega
    congr 1
    exact Fin.ext he


end MaximumMatching.AltPath

end SegmentSplice

section RelativeShortest

/-! Relative shortestness at a high-tenacity even vertex. The argument compares
all relative alternating paths, including ones intersecting the free-root prefix.
-/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Relative minimality quantifies over all simple alternating segments of the
same parity and with the same endpoints; no extension or confinement is assumed. -/
def AltSegment.Shortest (s : AltSegment M) : Prop :=
  ∀ q : AltSegment M, q.first = s.first → q.last = s.last →
    q.length % 2 = s.length % 2 → s.length ≤ q.length

private theorem least_segment_hit (P : Nat → Prop) (n : Nat) (hn : P n) :
    ∃ m, P m ∧ ∀ l, l < m → ¬P l := by
  classical
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hs : ∃ m, m < n ∧ P m
    · obtain ⟨m, hm, hp⟩ := hs
      exact ih m hm hp
    · exact ⟨n, hn, fun l hl hp => hs ⟨l, hl, hp⟩⟩

namespace AltPath

/-- The earliest vertex of an ordinary path meeting a relative path. Its strict
prefix avoids the entire relative path, in both traversal directions. -/
theorem first_segment_hit (p : AltPath M) (q : AltSegment M)
    (k : Fin (p.length + 1)) (hk : p.vertex k = q.first) :
    ∃ (i : Fin (p.length + 1)) (j : Fin (q.length + 1)), i.val ≤ k.val ∧
      p.vertex i = q.vertex j ∧
      ∀ (a : Fin (p.length + 1)) (b : Fin (q.length + 1)),
        a.val < i.val → p.vertex a ≠ q.vertex b := by
  let P (i : Nat) := ∃ (hi : i < p.length + 1) (j : Fin (q.length + 1)),
    p.vertex ⟨i, hi⟩ = q.vertex j
  obtain ⟨m, ⟨hm, j, hh⟩, hmin⟩ := least_segment_hit P k.val ⟨k.isLt, ⟨0, by omega⟩, hk⟩
  have hmk : m ≤ k.val := by
    by_cases h : m ≤ k.val
    · exact h
    · exact False.elim (hmin k.val (by omega) ⟨k.isLt, ⟨0, by omega⟩, hk⟩)
  refine ⟨⟨m, hm⟩, j, hmk, hh, ?_⟩
  intro a b ha he
  exact hmin a.val ha ⟨a.isLt, b, he⟩

/-- If a shortest path passes an even vertex of tenacity greater than `t`, and
its length plus that vertex's evenlevel is at most `t`, its remaining segment
is a shortest relative path. A competing segment may intersect the prefix:
the first-intersection proof either shortens the original path or gives a
forbidden short odd path to the high-tenacity vertex. -/
theorem segment_shortest_of_high (p : AltPath M) (hp : p.Shortest)
    (k : Fin (p.length + 1)) (hke : k.val % 2 = 0) (t : Nat)
    (hlevel : evenlevel M (p.vertex k) = some k.val)
    (hhigh : levelLT (some t) (tenacity M (p.vertex k)))
    (hbound : p.length + k.val ≤ t) :
    (p.segment k.val (by omega) hke).Shortest := by
  intro q hqfirst hqlast hqpar
  change p.length - k.val ≤ q.length
  apply Nat.le_of_not_gt
  intro hshort
  have hqf : q.first = p.vertex k := by simpa only [segment_first, Fin.eta] using hqfirst
  have hql : q.last = p.last := by simpa only [segment_last] using hqlast
  have hqp : q.length % 2 = p.length % 2 := by
    change q.length % 2 = (p.length - k.val) % 2 at hqpar
    omega
  obtain ⟨i, j, hik, hij, hfirst⟩ := p.first_segment_hit q k hqf.symm
  have hpj : (p.take i.val (by omega)).last = q.vertex j := hij
  have hdis : ∀ (a : Fin ((p.take i.val (by omega)).length + 1))
      (b : Fin (q.length + 1)), b.val ≠ j.val →
      (p.take i.val (by omega)).vertex a ≠ q.vertex b := by
    intro a b hb he
    have ha : a.val ≤ i.val := by have := a.isLt; change a.val < i.val + 1 at this; omega
    change p.vertex ⟨a.val, by omega⟩ = q.vertex b at he
    by_cases hal : a.val < i.val
    · exact hfirst ⟨a.val, by omega⟩ b hal he
    · have hai : (⟨a.val, by omega⟩ : Fin (p.length + 1)) = i := Fin.ext (by change a.val = i.val; omega)
      rw [hai, hij] at he
      have heq := congrArg (fun x : Fin (q.length + 1) => x.val) (q.injective _ _ he)
      exact hb heq.symm
  have noOdd (r : AltPath M) (hre : r.last = p.vertex k) (hro : r.length % 2 = 1)
      (hrb : k.val + r.length ≤ t) : False := by
    have hw : HasPathLength M 1 (p.vertex k) r.length := ⟨r, hre, rfl, hro⟩
    cases ho : oddlevel M (p.vertex k) with
    | none => exact (level_eq_none_iff M 1 _).1 ho ⟨r.length, hw⟩
    | some a =>
      have ha := ((level_eq_some_iff M 1 _ a).1 ho).2 r.length hw
      have ht : t < k.val + a := by
        simpa only [tenacity, hlevel, ho, levelAdd, levelLT] using hhigh
      omega
  by_cases hpar : i.val % 2 = j.val % 2
  · have hd : (p.take i.val (by omega)).SegmentSuffixDisjoint q j.val := by
      intro a b hb
      exact hdis a b (by omega)
    let r := (p.take i.val (by omega)).spliceSegment q j.val (by omega) hpj hpar hd
    have hrl : r.length = i.val + (q.length - j.val) := rfl
    have hre : r.last = p.last := (spliceSegment_last _ _ _ _ _ _ _).trans hql
    have hrp : r.length % 2 = p.length % 2 := (spliceSegment_parity _ _ _ _ _ _ _).trans hqp
    have hl := hp.2 r.length ⟨r, hre, rfl, hrp⟩
    omega
  · by_cases hio : i.val % 2 = 1
    · have hje : j.val % 2 = 0 := by omega
      have hd : (p.take i.val (by omega)).SegmentReverseDisjoint q 0 j.val := by
        intro a b _ hb
        exact hdis a b (by omega)
      let r := (p.take i.val (by omega)).spliceReverseSegment q 0 j.val (by omega)
        (by omega) hpj hio hje hd
      have hrl : r.length = i.val + j.val := by change i.val + (j.val - 0) = _; omega
      have hre : r.last = p.vertex k := by
        have hh := spliceReverseSegment_last (p.take i.val (by omega)) q 0 j.val
          (by omega) (by omega) hpj hio hje hd
        exact hh.trans hqf
      exact noOdd r hre (by rw [hrl]; omega) (by rw [hrl]; omega)
    · have hie : i.val % 2 = 0 := by omega
      have hjo : j.val % 2 = 1 := by omega
      let s := (q.take j.val (by omega)).reverse hjo
      have hsfirst : s.first = q.vertex j := by
        simp only [s, AltSegment.first, AltSegment.reverse, AltSegment.take, Nat.sub_zero, Fin.eta]
      have hslast : s.last = q.first := by
        simp only [s, AltSegment.last, AltSegment.reverse, AltSegment.take, Nat.sub_self, AltSegment.first]
      have hslen : s.length = j.val := rfl
      have hd : ∀ (a : Fin ((p.take i.val (by omega)).length + 1))
          (b : Fin (s.length + 1)), 0 < b.val →
          (p.take i.val (by omega)).vertex a ≠ s.vertex b := by
        intro a b hb
        change (p.take i.val (by omega)).vertex a ≠ q.vertex ⟨j.val - b.val, by omega⟩
        exact hdis a ⟨j.val - b.val, by omega⟩ (by
          change j.val - b.val ≠ j.val
          have hbb := b.isLt
          change b.val < j.val + 1 at hbb
          omega)
      let r := (p.take i.val (by omega)).appendSegment s hie (hpj.trans hsfirst.symm) hd
      have hrl : r.length = i.val + j.val := rfl
      have hre : r.last = p.vertex k :=
        (appendSegment_last _ _ _ _ _).trans (hslast.trans hqf)
      exact noOdd r hre (by rw [hrl]; omega) (by rw [hrl]; omega)

/-- A shortest relative segment cannot return to an earlier vertex of an even
prefix to a high-tenacity base. The total target length is specified by a
semantic shortest-path fact, rather than by assuming concatenation is valid. -/
theorem segment_avoids_prefix (p : AltPath M) (q : AltSegment M)
    (hjoin : p.last = q.first)
    (hshort : IsShortest M (q.length % 2) q.last (p.length + q.length))
    (t : Nat) (hlevel : evenlevel M p.last = some p.length)
    (hhigh : levelLT (some t) (tenacity M p.last))
    (hbound : 2 * p.length + q.length ≤ t) :
    ∀ (a : Fin (p.length + 1)) (b : Fin (q.length + 1)),
      0 < b.val → p.vertex a ≠ q.vertex b := by
  intro a b hb hab
  have ha : a.val < p.length := by
    by_cases ha : a.val < p.length
    · exact ha
    · have hae : a = ⟨p.length, by omega⟩ := Fin.ext (by change a.val = p.length; omega)
      rw [hae] at hab
      have hsame : q.vertex ⟨0, by omega⟩ = q.vertex b := hjoin.symm.trans hab
      have hidx := congrArg (fun x : Fin (q.length + 1) => x.val) (q.injective _ _ hsame)
      change 0 = b.val at hidx
      omega
  obtain ⟨i, j, _, hij, hfirst⟩ := p.first_segment_hit q ⟨p.length, by omega⟩ hjoin
  have hia : i.val ≤ a.val := by
    by_cases h : i.val ≤ a.val
    · exact h
    · exact False.elim (hfirst a b (by omega) hab)
  have hil : i.val < p.length := by omega
  have hpj : (p.take i.val (by omega)).last = q.vertex j := hij
  have hdis : ∀ (x : Fin ((p.take i.val (by omega)).length + 1))
      (y : Fin (q.length + 1)), y.val ≠ j.val →
      (p.take i.val (by omega)).vertex x ≠ q.vertex y := by
    intro x y hy he
    have hx : x.val ≤ i.val := by have := x.isLt; change x.val < i.val + 1 at this; omega
    change p.vertex ⟨x.val, by omega⟩ = q.vertex y at he
    by_cases hxl : x.val < i.val
    · exact hfirst ⟨x.val, by omega⟩ y hxl he
    · have hxi : (⟨x.val, by omega⟩ : Fin (p.length + 1)) = i := Fin.ext (by change x.val = i.val; omega)
      rw [hxi, hij] at he
      exact hy (congrArg (fun z : Fin (q.length + 1) => z.val) (q.injective _ _ he)).symm
  have noOdd (r : AltPath M) (hre : r.last = p.last) (hro : r.length % 2 = 1)
      (hrb : p.length + r.length ≤ t) : False := by
    have hw : HasPathLength M 1 p.last r.length := ⟨r, hre, rfl, hro⟩
    cases ho : oddlevel M p.last with
    | none => exact (level_eq_none_iff M 1 _).1 ho ⟨r.length, hw⟩
    | some k =>
      have hk := ((level_eq_some_iff M 1 _ k).1 ho).2 r.length hw
      have ht : t < p.length + k := by
        simpa only [tenacity, hlevel, ho, levelAdd, levelLT] using hhigh
      omega
  by_cases hpar : i.val % 2 = j.val % 2
  · have hd : (p.take i.val (by omega)).SegmentSuffixDisjoint q j.val := by
      intro x y hy
      exact hdis x y (by omega)
    let r := (p.take i.val (by omega)).spliceSegment q j.val (by omega) hpj hpar hd
    have hrl : r.length = i.val + (q.length - j.val) := rfl
    have hre : r.last = q.last := spliceSegment_last _ _ _ _ _ _ _
    have hrp : r.length % 2 = q.length % 2 := spliceSegment_parity _ _ _ _ _ _ _
    have hl := hshort.2 r.length ⟨r, hre, rfl, hrp⟩
    omega
  · by_cases hio : i.val % 2 = 1
    · have hje : j.val % 2 = 0 := by omega
      have hd : (p.take i.val (by omega)).SegmentReverseDisjoint q 0 j.val := by
        intro x y _ hy
        exact hdis x y (by omega)
      let r := (p.take i.val (by omega)).spliceReverseSegment q 0 j.val (by omega)
        (by omega) hpj hio hje hd
      have hrl : r.length = i.val + j.val := by change i.val + (j.val - 0) = _; omega
      have hre : r.last = p.last :=
        (spliceReverseSegment_last _ _ _ _ _ _ _ _ _ _).trans hjoin.symm
      exact noOdd r hre (by rw [hrl]; omega) (by rw [hrl]; omega)
    · have hie : i.val % 2 = 0 := by omega
      have hjo : j.val % 2 = 1 := by omega
      let s := (q.take j.val (by omega)).reverse hjo
      have hsfirst : s.first = q.vertex j := by
        simp only [s, AltSegment.first, AltSegment.reverse, AltSegment.take, Nat.sub_zero, Fin.eta]
      have hslast : s.last = q.first := by
        simp only [s, AltSegment.last, AltSegment.reverse, AltSegment.take, Nat.sub_self, AltSegment.first]
      have hd : ∀ (x : Fin ((p.take i.val (by omega)).length + 1))
          (y : Fin (s.length + 1)), 0 < y.val →
          (p.take i.val (by omega)).vertex x ≠ s.vertex y := by
        intro x y hy
        change (p.take i.val (by omega)).vertex x ≠ q.vertex ⟨j.val - y.val, by omega⟩
        exact hdis x ⟨j.val - y.val, by omega⟩ (by
          change j.val - y.val ≠ j.val
          have hyb := y.isLt
          change y.val < j.val + 1 at hyb
          omega)
      let r := (p.take i.val (by omega)).appendSegment s hie (hpj.trans hsfirst.symm) hd
      have hrl : r.length = i.val + j.val := rfl
      have hre : r.last = p.last :=
        (appendSegment_last _ _ _ _ _).trans (hslast.trans hjoin.symm)
      exact noOdd r hre (by rw [hrl]; omega) (by rw [hrl]; omega)

end AltPath

/-- Proposition 6.17: whenever an actual common base exists, every shortest
parity path splits at that base into a shortest even prefix and a shortest
relative segment. No confinement or disjoint-extension hypothesis is assumed. -/
theorem IsBase.shortest_relative {v b : V} (hb : IsBase M v b)
    (p : AltPath M) (hpv : p.last = v) (hp : p.Shortest) :
    ∃ (i : Fin (p.length + 1)) (hie : i.val % 2 = 0),
      p.vertex i = b ∧ (p.take i.val (by omega)).Shortest ∧
      (p.segment i.val (by omega) hie).Shortest := by
  have hdata := hb
  obtain ⟨t, hvt, _⟩ := hdata
  obtain ⟨e, o, he, ho, he0, ho1, heo⟩ := finite_levels_of_tenacity v t hvt
  have hother : ∃ q : AltPath M, q.last = v ∧ q.Shortest ∧ p.length + q.length = t := by
    by_cases hp0 : p.length % 2 = 0
    · have hpl : evenlevel M v = some p.length :=
        (level_eq_some_iff M 0 v p.length).2 (by simpa only [AltPath.Shortest, hp0, hpv] using hp)
      have hlen : e = p.length := Option.some.inj (he.symm.trans hpl)
      have hs := (level_eq_some_iff M 1 v o).1 ho
      obtain ⟨q, hqv, hql, _⟩ := hs.1
      refine ⟨q, hqv, ?_, by omega⟩
      simpa only [AltPath.Shortest, hql, ho1, hqv] using hs
    · have hp1 : p.length % 2 = 1 := by omega
      have hpl : oddlevel M v = some p.length :=
        (level_eq_some_iff M 1 v p.length).2 (by simpa only [AltPath.Shortest, hp1, hpv] using hp)
      have hlen : o = p.length := Option.some.inj (ho.symm.trans hpl)
      have hs := (level_eq_some_iff M 0 v e).1 he
      obtain ⟨q, hqv, hql, _⟩ := hs.1
      refine ⟨q, hqv, ?_, by omega⟩
      simpa only [AltPath.Shortest, hql, he0, hqv] using hs
  obtain ⟨q, hqv, hq, hpq⟩ := hother
  obtain ⟨i, hi, hie, _, himin, hip⟩ := hb.on_shortest p hpv hp
  obtain ⟨j, _, _, hjlt, hjmin, _⟩ := hb.on_shortest q hqv hq
  have hij : i.val = j.val := Option.some.inj (himin.symm.trans hjmin)
  refine ⟨i, hie, hi, hip, p.segment_shortest_of_high hp i hie t ?_ ?_ (by omega)⟩
  · rw [hi]
    exact (minlevel_eq_even_of_outer b hb.outer).symm.trans himin
  · rw [hi]
    simpa only [hvt] using hb.high

end MaximumMatching

end RelativeShortest

section RelativeJoin

/-! Converse of the relative-path decomposition: any shortest even path to an
actual common base can be joined to any shortest relative path to its child.
The proof derives disjointness, rather than assuming it. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Finite tenacity supplies a globally shortest path of either requested parity. -/
theorem finite_tenacity_shortest_parity (v : V) (t k : Nat)
    (ht : tenacity M v = some t) :
    ∃ r : AltPath M, r.last = v ∧ r.Shortest ∧ r.length % 2 = k % 2 := by
  obtain ⟨e, o, he, ho, hep, hop, _⟩ := finite_levels_of_tenacity v t ht
  by_cases hk : k % 2 = 0
  · have hs := (level_eq_some_iff M 0 v e).1 he
    obtain ⟨r, hrv, hrl, _⟩ := hs.1
    refine ⟨r, hrv, ?_, by omega⟩
    simpa only [AltPath.Shortest, hrl, hep, hrv] using hs
  · have hs := (level_eq_some_iff M 1 v o).1 ho
    obtain ⟨r, hrv, hrl, _⟩ := hs.1
    refine ⟨r, hrv, ?_, by omega⟩
    simpa only [AltPath.Shortest, hrl, hop, hrv] using hs

/-- The length of an arbitrary shortest relative segment is the corresponding
global parity level minus the base's evenlevel. An opposite global path through
the same base supplies the tenacity budget needed for disjoint concatenation. -/
theorem IsBase.relative_length_formula {v b : V} (hb : IsBase M v b)
    (p : AltPath M) (hp : p.Shortest) (hpe : p.length % 2 = 0) (hpb : p.last = b)
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v)
    (t : Nat) (hvt : tenacity M v = some t) :
    IsShortest M (q.length % 2) v (p.length + q.length) ∧
      2 * p.length + q.length ≤ t := by
  have hplevel : evenlevel M b = some p.length :=
    (level_eq_some_iff M 0 b p.length).2 (by simpa only [AltPath.Shortest, hpe, hpb] using hp)
  obtain ⟨r, hrv, hr, hrpar⟩ := finite_tenacity_shortest_parity v t q.length hvt
  obtain ⟨i, hie, hib, hip, his⟩ := hb.shortest_relative r hrv hr
  have hilevel : evenlevel M b = some i.val :=
    (level_eq_some_iff M 0 b i.val).2 (by
      simpa only [AltPath.Shortest, AltPath.take_length, AltPath.take_last, hie, hib] using hip)
  have hilen : i.val = p.length := Option.some.inj (hilevel.symm.trans hplevel)
  let s := r.segment i.val (by omega) hie
  have hsf : s.first = b := (r.segment_first i.val (by omega) hie).trans hib
  have hsl : s.last = v := (r.segment_last i.val (by omega) hie).trans hrv
  have hspar : s.length % 2 = q.length % 2 := by
    change (r.length - i.val) % 2 = q.length % 2
    omega
  have hqs : q.length ≤ s.length := hq s (hsf.trans hqb.symm) (hsl.trans hqv.symm) hspar
  have hsq : s.length ≤ q.length := his q (hqb.trans hsf.symm) (hqv.trans hsl.symm) hspar.symm
  have hqlen : q.length = r.length - i.val := Nat.le_antisymm hqs hsq
  have hrlen : r.length = p.length + q.length := by omega
  have hsumpar : (p.length + q.length) % 2 = q.length % 2 := by omega
  have hshort : IsShortest M (q.length % 2) v (p.length + q.length) := by
    simpa only [AltPath.Shortest, hrv, hrlen, hsumpar] using hr
  refine ⟨hshort, ?_⟩
  obtain ⟨u, huv, hu, hupar⟩ := finite_tenacity_shortest_parity v t (q.length + 1) hvt
  obtain ⟨j, _, _, hjlt, hjmin, _⟩ := hb.on_shortest u huv hu
  have hpmin : minlevel M b = some p.length := (minlevel_eq_even_of_outer b hb.outer).trans hplevel
  have hjlen : j.val = p.length := Option.some.inj (hjmin.symm.trans hpmin)
  have hsum : r.length + u.length = t := by
    have ht' : tenacity M v = some (r.length + u.length) := by
      by_cases hqeven : q.length % 2 = 0
      · have hre : r.length % 2 = 0 := hrpar.trans hqeven
        have huo : u.length % 2 = 1 := by omega
        have hten := r.opposite_shortest_tenacity u hr hu (hrv.trans huv.symm) hre huo
        simpa only [hrv] using hten
      · have hro : r.length % 2 = 1 := by omega
        have hue : u.length % 2 = 0 := by omega
        have hten := u.opposite_shortest_tenacity r hu hr (huv.trans hrv.symm) hue hro
        simpa only [huv, Nat.add_comm] using hten
    exact Option.some.inj (ht'.symm.trans hvt)
  omega

/-- Any shortest relative path avoids every vertex of any shortest even prefix
to the base, apart from the shared base endpoint. -/
theorem IsBase.relative_avoids_prefix {v b : V} (hb : IsBase M v b)
    (p : AltPath M) (hp : p.Shortest) (hpe : p.length % 2 = 0) (hpb : p.last = b)
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v) :
    ∀ (i : Fin (p.length + 1)) (j : Fin (q.length + 1)),
      0 < j.val → p.vertex i ≠ q.vertex j := by
  obtain ⟨t, hvt, _⟩ := (show IsBase M v b from hb)
  obtain ⟨hshort, hbound⟩ := hb.relative_length_formula p hp hpe hpb q hq hqb hqv t hvt
  apply p.segment_avoids_prefix q (hpb.trans hqb.symm) (by simpa only [hqv] using hshort)
    t ?_ ?_ hbound
  · exact (level_eq_some_iff M 0 p.last p.length).2
      (by simpa only [AltPath.Shortest, hpe] using hp)
  · rw [hpb]
    simpa only [hvt] using hb.high

/-- Proposition 6.17 in the joining direction: the actual concatenation of
arbitrary shortest component paths is a shortest global alternating path.
Disjointness comes from `relative_avoids_prefix`, not from the caller. -/
theorem IsBase.append_relative_shortest {v b : V} (hb : IsBase M v b)
    (p : AltPath M) (hp : p.Shortest) (hpe : p.length % 2 = 0) (hpb : p.last = b)
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v) :
    (p.appendSegment q hpe (hpb.trans hqb.symm)
      (hb.relative_avoids_prefix p hp hpe hpb q hq hqb hqv)).Shortest := by
  obtain ⟨t, hvt, _⟩ := (show IsBase M v b from hb)
  have hshort := (hb.relative_length_formula p hp hpe hpb q hq hqb hqv t hvt).1
  have hpar : (p.length + q.length) % 2 = q.length % 2 := by omega
  simpa only [AltPath.Shortest, AltPath.appendSegment_length, AltPath.appendSegment_last,
    hqv, hpar] using hshort

end MaximumMatching

end RelativeJoin

section MinimumRelative

/-! Arbitrary shortest relative paths inside a minimum-tenacity blossom. Such
paths are joined to an actual shortest even prefix using proved disjointness;
the global shortest-path confinement and edge-tenacity theorems then apply. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

namespace AltPath

/-- The relative segment occurs literally as the suffix of concatenation. -/
theorem appendSegment_vertex_suffix (p : AltPath M) (q : AltSegment M)
    (hpe : p.length % 2 = 0) (hjoin : p.last = q.first) (hdis)
    (j : Fin (q.length + 1)) :
    (p.appendSegment q hpe hjoin hdis).vertex
      ⟨p.length + j.val, by change p.length + j.val < p.length + q.length + 1; omega⟩ =
      q.vertex j := by
  by_cases hj : j.val = 0
  · have hj0 : j = ⟨0, by omega⟩ := Fin.ext hj
    rw [hj0]
    simpa only [appendSegment, Nat.add_zero, Nat.le_refl, dite_true,
      AltSegment.first, last] using hjoin
  · simp only [appendSegment, dite_eq_right (show ¬p.length + j.val ≤ p.length by omega),
      Nat.add_sub_cancel_left]

end AltPath

/-- At minimum eligible tenacity, every shortest relative path from an actual
base to its child stays inside the source blossom (apart from the base), and
every edge of that path has exactly the minimum tenacity. The path is arbitrary;
it need not have been extracted from an existing global path. -/
theorem IsBase.minimum_relative_properties {v b : V} (hb : IsBase M v b)
    (t : Nat) (ht : EligibleTenacity M t) (hvt : tenacity M v = some t)
    (hmin : ∀ w : V, levelLE (some t) (tenacity M w))
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v) :
    (∀ j : Fin (q.length + 1), 0 < j.val → Blossom M t b (q.vertex j)) ∧
      (∀ k : Fin q.length, edgeTenacity M (q.vertex ⟨k.val, by omega⟩)
        (q.vertex ⟨k.val + 1, by omega⟩) = some t) := by
  obtain ⟨s, r, _, hrv, hr, _⟩ := hb.path
  obtain ⟨i, hib, hie, _, _, hip⟩ := hb.on_shortest r hrv hr
  let p := r.take i.val (by omega)
  have hp : p.Shortest := hip
  have hpe : p.length % 2 = 0 := hie
  have hpb : p.last = b := hib
  let hdis := hb.relative_avoids_prefix p hp hpe hpb q hq hqb hqv
  let joined := p.appendSegment q hpe (hpb.trans hqb.symm) hdis
  have hjshort : joined.Shortest := hb.append_relative_shortest p hp hpe hpb q hq hqb hqv
  have hjend : joined.last = v := (p.appendSegment_last q hpe (hpb.trans hqb.symm) hdis).trans hqv
  have hjten : tenacity M joined.last = some t := hjend ▸ hvt
  have hjbase : joined.BaseOnPath t b := (isBase_iff_common t hvt).1 hb joined hjend hjshort
  let baseIndex : Fin (joined.length + 1) := ⟨p.length, by change p.length < p.length + q.length + 1; omega⟩
  have hbase : joined.vertex baseIndex = b := by
    change (if h : p.length ≤ p.length then p.vertex ⟨p.length, _⟩ else _) = b
    simpa only [Nat.le_refl, dite_true, AltPath.last] using hpb
  have hvertex (j : Fin (q.length + 1)) :
      joined.vertex ⟨p.length + j.val, by change p.length + j.val < p.length + q.length + 1; omega⟩ =
        q.vertex j := p.appendSegment_vertex_suffix q hpe (hpb.trans hqb.symm) hdis j
  constructor
  · intro j hj
    have hc := joined.minimum_suffix_in_blossom hjshort t ht hjten hmin b hjbase baseIndex
      ⟨p.length + j.val, by change p.length + j.val < p.length + q.length + 1; omega⟩ hbase
      (by change p.length < p.length + j.val; omega)
    rwa [hvertex] at hc
  · intro k
    have hc := joined.minimum_suffix_edge_tenacity hjshort t hjten hmin b hjbase baseIndex
      hbase ⟨p.length + k.val, by change p.length + k.val < p.length + q.length; omega⟩
      (by change p.length ≤ p.length + k.val; omega)
    have hv0 := hvertex ⟨k.val, by omega⟩
    have hv1 := hvertex ⟨k.val + 1, by omega⟩
    simpa only [Nat.add_assoc, hv0, hv1] using hc

/-- The set-theoretic confinement statement for an arbitrary shortest relative
path in a minimum-tenacity blossom. -/
theorem IsBase.minimum_relative_confined {v b : V} (hb : IsBase M v b)
    (t : Nat) (ht : EligibleTenacity M t) (hvt : tenacity M v = some t)
    (hmin : ∀ w : V, levelLE (some t) (tenacity M w))
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v) :
    ∀ w, q.Contains w → w = b ∨ Blossom M t b w := by
  intro w hw
  obtain ⟨j, rfl⟩ := hw
  by_cases hj : j.val = 0
  · have hj0 : j = ⟨0, by omega⟩ := Fin.ext hj
    exact Or.inl (by rw [hj0]; exact hqb)
  · exact Or.inr ((hb.minimum_relative_properties t ht hvt hmin q hq hqb hqv).1 j (by omega))

/-- Theorem 6.19(4), confinement and edge-tenacity parts of the minimum-tenacity
basis, stated for any member of a source blossom and any shortest relative path. -/
theorem minimum_blossom_relative_paths (t : Nat) (ht : EligibleTenacity M t)
    (hmin : ∀ w : V, levelLE (some t) (tenacity M w)) (b v : V)
    (hv : Blossom M t b v) (q : AltSegment M) (hq : q.Shortest)
    (hqb : q.first = b) (hqv : q.last = v) :
    (∀ w, q.Contains w → w = b ∨ Blossom M t b w) ∧
      (∀ k : Fin q.length, edgeTenacity M (q.vertex ⟨k.val, by omega⟩)
        (q.vertex ⟨k.val + 1, by omega⟩) = some t) := by
  have htwo : 2 ≤ t := by
    cases t with
    | zero => exact False.elim hv
    | succ t =>
      cases t with
      | zero => exact False.elim hv
      | succ t => omega
  have hs := (minimum_blossom_iff t htwo hmin b v).1 hv
  exact ⟨hs.2.minimum_relative_confined t ht hs.1 hmin q hq hqb hqv,
    (hs.2.minimum_relative_properties t ht hs.1 hmin q hq hqb hqv).2⟩

end MaximumMatching

end MinimumRelative
