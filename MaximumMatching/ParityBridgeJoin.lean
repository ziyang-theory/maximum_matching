import MaximumMatching.WeightedTopExpansion

/-! Relative bridge joining inside a recorded petal, without requiring a
free boundary. Simplicity is derived from the two arms' actual disjointness. -/
namespace MaximumMatching.ParitySegment
variable {V : Type} {G : Graph V} {M : Matching G}

theorem bridge_join_segment (a b : ParitySegment M)
    (hdis : ∀ i j, b.vertex i ≠ a.vertex j)
    (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1) :
    ∃ z : ParitySegment M, z.first = b.last ∧ z.last = a.last ∧
      z.length = b.length + 1 + a.length ∧
      z.phase = b.phase + b.length + 1 ∧
      (∀ w, z.Contains w → a.Contains w ∨ b.Contains w) ∧
      ∃ i : Fin z.length, z.vertex ⟨i.val, by omega⟩ = b.first ∧
        z.vertex ⟨i.val + 1, by omega⟩ = a.first := by
  let e := ofEdge b.first a.first (b.phase + 1) hedge hmatch
  have hp : (b.reverse.phase + b.reverse.length) % 2 = e.phase % 2 := by
    change (b.phase + b.length + 1 + b.length) % 2 = (b.phase + 1) % 2
    omega
  have hj : b.reverse.last = e.first := b.reverse_last
  have hd : ∀ (i : Fin (b.reverse.length + 1)) (j : Fin (e.length + 1)),
      0 < j.val → b.reverse.vertex i ≠ e.vertex j := by
    intro i j hpos he
    have hj1 : j.val = 1 := by have hjb := j.isLt; change j.val < 1 + 1 at hjb; omega
    have he' : b.vertex ⟨b.length - i.val, by have hib := i.isLt; change i.val < b.length + 1 at hib; omega⟩ = a.first := by
      simpa only [e, ofEdge, hj1, Nat.one_ne_zero, ite_false, reverse] using he
    exact hdis _ ⟨0, by omega⟩ he'
  let c := b.reverse.append e hp hj hd
  have hcp : (c.phase + c.length) % 2 = a.phase % 2 := by
    change (b.phase + b.length + 1 + (b.length + 1)) % 2 = a.phase % 2
    omega
  have hcj : c.last = a.first := b.reverse.append_last e hp hj hd
  have hcd : ∀ (i : Fin (c.length + 1)) (j : Fin (a.length + 1)),
      0 < j.val → c.vertex i ≠ a.vertex j := by
    intro i j hpos he
    have hc : c.Contains (a.vertex j) := ⟨i, he⟩
    rcases (b.reverse.contains_append_iff e hp hj hd (a.vertex j)).mp hc with hb | he
    · obtain ⟨k, hk⟩ := (b.contains_reverse_iff _).mp hb
      exact hdis k j hk
    · obtain ⟨k, hk⟩ := he
      by_cases hk0 : k.val = 0
      · have hh : b.first = a.vertex j := by simpa [e, ofEdge, hk0] using hk
        exact hdis ⟨0, by omega⟩ j hh
      · have hh : a.first = a.vertex j := by simpa [e, ofEdge, hk0] using hk
        have hh' := congrArg Fin.val (a.injective ⟨0, by omega⟩ j hh)
        change 0 = j.val at hh'
        omega
  let d := c.append a hcp hcj hcd
  have hdf : d.first = b.last :=
    (c.append_first a hcp hcj hcd).trans ((b.reverse.append_first e hp hj hd).trans b.reverse_first)
  refine ⟨d, hdf, c.append_last a hcp hcj hcd, rfl, rfl, ?_, ?_⟩
  · intro w hw
    rcases (c.contains_append_iff a hcp hcj hcd w).1 hw with hcw | haw
    · rcases (b.reverse.contains_append_iff e hp hj hd w).1 hcw with hbw | hew
      · exact Or.inr ((b.contains_reverse_iff w).1 hbw)
      · obtain ⟨i, hi⟩ := hew
        by_cases hz : i.val = 0
        · have hbw : b.first = w := by simpa only [e, ofEdge, hz, ite_true] using hi
          exact Or.inr ⟨⟨0, by omega⟩, hbw⟩
        · have haw : a.first = w := by simpa only [e, ofEdge, hz, ite_false] using hi
          exact Or.inl ⟨⟨0, by omega⟩, haw⟩
    · exact Or.inl haw
  · refine ⟨⟨b.length, by change b.length < b.length + 1 + a.length; omega⟩, ?_, ?_⟩
    · change d.vertex ⟨b.length, _⟩ = b.first
      simp only [d, append, c, reverse, e, ofEdge, show b.length ≤ b.length + 1 by omega,
        dite_true, Nat.le_refl, Nat.sub_self, first]
    · change d.vertex ⟨b.length + 1, _⟩ = a.first
      simp only [d, append, c, reverse, e, ofEdge, Nat.le_refl, dite_true,
        show ¬b.length + 1 ≤ b.length by omega, dite_false,
        Nat.add_sub_cancel_left, Nat.one_ne_zero, ite_false]

/-- When the reverse arm starts unmatched at its boundary, the construction
is an ordinary relative alternating segment even if that boundary is matched. -/
theorem bridge_join_relative (a b : ParitySegment M)
    (hdis : ∀ i j, b.vertex i ≠ a.vertex j)
    (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1)
    (hboundary : (b.phase + b.length) % 2 = 1) :
    ∃ z : AltSegment M, z.first = b.last ∧ z.last = a.last ∧
      z.length = b.length + 1 + a.length ∧
      (∀ w, z.Contains w → a.Contains w ∨ b.Contains w) ∧
      ∃ i : Fin z.length, z.vertex ⟨i.val, by omega⟩ = b.first ∧
        z.vertex ⟨i.val + 1, by omega⟩ = a.first := by
  obtain ⟨z, hf, hl, hn, hp, hc, he⟩ := a.bridge_join_segment b hdis hphase hedge hmatch
  have hz : z.phase % 2 = 0 := by rw [hp]; omega
  exact ⟨z.toAltSegment hz, hf, hl, hn, hc, he⟩

end MaximumMatching.ParitySegment
