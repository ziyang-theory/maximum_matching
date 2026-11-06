import MaximumMatching.DDFS

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
