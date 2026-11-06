import MaximumMatching.DDFSPaths

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
