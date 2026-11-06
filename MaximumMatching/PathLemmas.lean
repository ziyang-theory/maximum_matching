import MaximumMatching.Basic

namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The matched neighbor of an odd-indexed, nonterminal path vertex is its successor. -/
theorem mate_next (p : AltPath M) (i : Nat) (hi : i < p.length) (hodd : i % 2 = 1) :
    M.mate (p.vertex ⟨i, by omega⟩) = some (p.vertex ⟨i + 1, by omega⟩) :=
  (p.alternating ⟨i, hi⟩).2 hodd

/-- The matched neighbor of a positive even-indexed path vertex is its predecessor. -/
theorem mate_previous (p : AltPath M) (i : Nat) (hi : i ≤ p.length)
    (hpos : 0 < i) (heven : i % 2 = 0) :
    M.mate (p.vertex ⟨i, by omega⟩) = some (p.vertex ⟨i - 1, by omega⟩) := by
  have h := M.symm (p.mate_next (i - 1) (by omega) (by omega))
  simpa only [show i - 1 + 1 = i by omega] using h

/-- Appending the matched neighbor of an odd terminal vertex does not repeat a vertex.
This is the nontrivial simplicity step in the proof of Lemma 5.2. -/
theorem matched_last_fresh (p : AltPath M) (hodd : p.length % 2 = 1)
    {v : V} (hv : M.mate p.last = some v) : ∀ i, p.vertex i ≠ v := by
  intro i heq
  have hvback : M.mate (p.vertex i) = some p.last := by
    simpa only [heq] using M.symm hv
  by_cases hz : i.val = 0
  · have hi : i = ⟨0, by omega⟩ := Fin.ext hz
    have hfree := p.start_free
    rw [hi] at hvback
    unfold Matching.Free at hfree
    rw [hfree] at hvback
    contradiction
  · by_cases hpar : i.val % 2 = 0
    · have hp := p.mate_previous i.val (by omega) (by omega) hpar
      have he := M.mate_unique hp hvback
      have he' := p.injective ⟨i.val - 1, by omega⟩ ⟨p.length, by omega⟩ he
      have hval : i.val - 1 = p.length := congrArg Fin.val he'
      omega
    · by_cases hlast : i.val = p.length
      · have hi : i = ⟨p.length, by omega⟩ := Fin.ext hlast
        have hl : p.last = v := by simpa only [hi, last] using heq
        exact M.mate_ne_self (hl ▸ hv)
      · have hn := p.mate_next i.val (by omega) (by omega)
        have he := M.mate_unique hn hvback
        have he' := p.injective ⟨i.val + 1, by omega⟩ ⟨p.length, by omega⟩ he
        have hval : i.val + 1 = p.length := congrArg Fin.val he'
        omega

/-- Restrict an alternating simple path to an initial segment. -/
def take (p : AltPath M) (k : Nat) (hk : k ≤ p.length) : AltPath M where
  length := k
  vertex := fun i => p.vertex ⟨i.val, by omega⟩
  injective := by
    intro i j he
    have hh := p.injective ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ he
    apply Fin.ext
    have hv : i.val = j.val := congrArg (fun x : Fin (p.length + 1) => x.val) hh
    exact hv
  adjacent := fun i => p.adjacent ⟨i.val, by omega⟩
  start_free := p.start_free
  alternating := fun i => p.alternating ⟨i.val, by omega⟩

@[simp] theorem take_length (p : AltPath M) (k : Nat) (hk : k ≤ p.length) :
    (p.take k hk).length = k := rfl

@[simp] theorem take_last (p : AltPath M) (k : Nat) (hk : k ≤ p.length) :
    (p.take k hk).last = p.vertex ⟨k, by omega⟩ := rfl

/-- Append a fresh adjacent vertex with the edge parity required by alternation. -/
def append (p : AltPath M) (v : V) (hfresh : ∀ i, p.vertex i ≠ v)
    (hadj : G.Adj p.last v)
    (hpar : (M.mate p.last = some v) ↔ p.length % 2 = 1) : AltPath M where
  length := p.length + 1
  vertex := fun i => if h : i.val ≤ p.length then p.vertex ⟨i.val, by omega⟩ else v
  injective := by
    intro i j he
    split at he <;> split at he
    · rename_i hi hj
      have hh := p.injective ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ he
      apply Fin.ext
      have hv : i.val = j.val := congrArg (fun x : Fin (p.length + 1) => x.val) hh
      exact hv
    · exact False.elim (hfresh _ he)
    · exact False.elim (hfresh _ he.symm)
    · exact Fin.ext (by omega)
  adjacent := by
    intro i
    by_cases hi : i.val < p.length
    · simpa only [dite_eq_left (show i.val ≤ p.length by omega),
        dite_eq_left (show i.val + 1 ≤ p.length by omega)] using p.adjacent ⟨i.val, hi⟩
    · have he : i.val = p.length := by omega
      simp only [he, Nat.le_refl, dite_true,
        show ¬p.length + 1 ≤ p.length by omega, dite_false]
      exact hadj
  start_free := by simpa using p.start_free
  alternating := by
    intro i
    by_cases hi : i.val < p.length
    · simpa only [dite_eq_left (show i.val ≤ p.length by omega),
        dite_eq_left (show i.val + 1 ≤ p.length by omega)] using p.alternating ⟨i.val, hi⟩
    · have he : i.val = p.length := by omega
      simp only [he, Nat.le_refl, dite_true,
        show ¬p.length + 1 ≤ p.length by omega, dite_false]
      exact hpar

@[simp] theorem append_length (p : AltPath M) (v : V) (hfresh : ∀ i, p.vertex i ≠ v)
    (hadj : G.Adj p.last v) (hpar : (M.mate p.last = some v) ↔ p.length % 2 = 1) :
    (p.append v hfresh hadj hpar).length = p.length + 1 := rfl

@[simp] theorem append_last (p : AltPath M) (v : V) (hfresh : ∀ i, p.vertex i ≠ v)
    (hadj : G.Adj p.last v) (hpar : (M.mate p.last = some v) ↔ p.length % 2 = 1) :
    (p.append v hfresh hadj hpar).last = v := by
  simp only [last, append]
  split
  · omega
  · rfl

/-- Extend an odd path by its terminal matched edge. -/
def appendMatched (p : AltPath M) (hodd : p.length % 2 = 1)
    {v : V} (hv : M.mate p.last = some v) : AltPath M :=
  p.append v (p.matched_last_fresh hodd hv) (M.edge hv) ⟨fun _ => hodd, fun _ => hv⟩

@[simp] theorem appendMatched_length (p : AltPath M) (hodd : p.length % 2 = 1)
    {v : V} (hv : M.mate p.last = some v) :
    (p.appendMatched hodd hv).length = p.length + 1 := rfl

@[simp] theorem appendMatched_last (p : AltPath M) (hodd : p.length % 2 = 1)
    {v : V} (hv : M.mate p.last = some v) :
    (p.appendMatched hodd hv).last = v := by simp [appendMatched]

end AltPath
end MaximumMatching
