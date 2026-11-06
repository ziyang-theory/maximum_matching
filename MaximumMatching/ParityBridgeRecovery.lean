import MaximumMatching.ParityBridgeJoin

/-! Executable bridge joins. The vertex sequence is built by reversing one
supplied arm, inserting the actual bridge edge, and appending the other arm;
all simplicity, phase, and coverage certificates are erased proofs. -/
namespace MaximumMatching.ParitySegment
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Construct the actual relative bridge detour without a free-boundary
hypothesis and without choosing a semantic path witness. -/
def recoverBridgeJoinExact (a b : ParitySegment M)
    (hdis : ∀ i j, b.vertex i ≠ a.vertex j)
    (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1) :
    { z : ParitySegment M // z.first = b.last ∧ z.last = a.last ∧
      z.length = b.length + 1 + a.length ∧
      z.phase = b.phase + b.length + 1 ∧
      (∀ w, z.Contains w ↔ a.Contains w ∨ b.Contains w) ∧
      ∃ i : Fin z.length, z.vertex ⟨i.val, by omega⟩ = b.first ∧
        z.vertex ⟨i.val + 1, by omega⟩ = a.first } := by
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
  · intro w
    constructor
    · intro hw
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
    · intro hw
      apply (c.contains_append_iff a hcp hcj hcd w).2
      rcases hw with haw | hbw
      · exact Or.inr haw
      · exact Or.inl ((b.reverse.contains_append_iff e hp hj hd w).2
          (Or.inl ((b.contains_reverse_iff w).2 hbw)))
  · refine ⟨⟨b.length, by change b.length < b.length + 1 + a.length; omega⟩, ?_, ?_⟩
    · change d.vertex ⟨b.length, _⟩ = b.first
      simp only [d, append, c, reverse, e, ofEdge, show b.length ≤ b.length + 1 by omega,
        dite_true, Nat.le_refl, Nat.sub_self, first]
    · change d.vertex ⟨b.length + 1, _⟩ = a.first
      simp only [d, append, c, reverse, e, ofEdge, Nat.le_refl, dite_true,
        show ¬b.length + 1 ≤ b.length by omega, dite_false,
        Nat.add_sub_cancel_left, Nat.one_ne_zero, ite_false]

/-- Compatibility interface for the same computed bridge join. -/
def recoverBridgeJoin (a b : ParitySegment M)
    (hdis : ∀ i j, b.vertex i ≠ a.vertex j)
    (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1) :
    { z : ParitySegment M // z.first = b.last ∧ z.last = a.last ∧
      z.length = b.length + 1 + a.length ∧
      z.phase = b.phase + b.length + 1 ∧
      (∀ w, z.Contains w → a.Contains w ∨ b.Contains w) ∧
      ∃ i : Fin z.length, z.vertex ⟨i.val, by omega⟩ = b.first ∧
        z.vertex ⟨i.val + 1, by omega⟩ = a.first } := by
  let z := a.recoverBridgeJoinExact b hdis hphase hedge hmatch
  exact ⟨z.val, z.property.1, z.property.2.1, z.property.2.2.1,
    z.property.2.2.2.1, fun w hw => (z.property.2.2.2.2.1 w).1 hw,
    z.property.2.2.2.2.2⟩

/-- The same computed bridge join is an alternating path when its starting
boundary is free. -/
def recoverBridgeJoinFreeExact (a b : ParitySegment M)
    (hfree : M.Free b.last) (hdis : ∀ i j, b.vertex i ≠ a.vertex j)
    (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1) :
    { z : AltPath M // z.first = b.last ∧ z.last = a.last ∧
      z.length = b.length + 1 + a.length ∧ z.ContainsEdge b.first a.first ∧
      (∀ w, (∃ i, z.vertex i = w) ↔ a.Contains w ∨ b.Contains w) } := by
  have hend : (b.phase + b.length) % 2 = 1 := by
    by_cases hz : b.length = 0
    · have hends : b.first = b.last := congrArg b.vertex (Fin.ext (by omega))
      have hn : ¬(b.phase + 1) % 2 = 1 := by
        intro hp
        have hm := hmatch.mpr hp
        rw [hends, hfree] at hm
        contradiction
      omega
    · have hn : ¬(b.phase + (b.length - 1)) % 2 = 1 := by
        intro hp
        have hm := (b.alternating ⟨b.length - 1, by omega⟩).mpr hp
        have he : b.length - 1 + 1 = b.length := by omega
        simp only [he] at hm
        have hm' := M.symm hm
        change M.mate b.last = some _ at hm'
        rw [hfree] at hm'
        contradiction
      omega
  obtain ⟨z, hzf, hzl, hzn, hzp, hcover, hbridge⟩ :=
    a.recoverBridgeJoinExact b hdis hphase hedge hmatch
  have hzero : z.phase % 2 = 0 := by rw [hzp]; omega
  let p := (z.toAltSegment hzero).fromFree (by change M.Free z.first; rw [hzf]; exact hfree)
  refine ⟨p, hzf, hzl, hzn, ?_, hcover⟩
  obtain ⟨i, hi, hj⟩ := hbridge
  exact ⟨i, Or.inl ⟨hi, hj⟩⟩

/-- Compatibility interface for the same computed free-boundary join. -/
def recoverBridgeJoinFree (a b : ParitySegment M)
    (hfree : M.Free b.last) (hdis : ∀ i j, b.vertex i ≠ a.vertex j)
    (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1) :
    { z : AltPath M // z.first = b.last ∧ z.last = a.last ∧
      z.length = b.length + 1 + a.length ∧ z.ContainsEdge b.first a.first } := by
  let z := a.recoverBridgeJoinFreeExact b hfree hdis hphase hedge hmatch
  exact ⟨z.val, z.property.1, z.property.2.1, z.property.2.2.1, z.property.2.2.2.1⟩

end MaximumMatching.ParitySegment
