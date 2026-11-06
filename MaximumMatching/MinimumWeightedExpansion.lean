import MaximumMatching.WeightedExpansion
import MaximumMatching.MinimumRelative

/-! Construct compressed-edge realizations from actual minimum-tenacity
blossom paths and an exit edge. Freshness follows from the blossom's tenacity
bound; it is not an input disjointness premise. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A shortest relative path in a minimum-tenacity blossom extends through
any phase-compatible exit edge to a different high-tenacity vertex. -/
theorem IsBase.minimum_exit_segment {u b v : V} (hb : IsBase M u b)
    (t : Nat) (ht : EligibleTenacity M t) (hut : tenacity M u = some t)
    (hmin : ∀ w : V, levelLE (some t) (tenacity M w))
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqu : q.last = u)
    (hv : levelLT (some t) (tenacity M v)) (hvb : v ≠ b)
    (hadj : G.Adj u v) (hmatch : (M.mate u = some v) ↔ q.length % 2 = 1) :
    ∃ s : AltSegment M, s.first = b ∧ s.last = v ∧ s.length = q.length + 1 ∧
      BlossomEdgeExpansion M t s := by
  let a := ParitySegment.ofAltSegment q
  let e := ParitySegment.ofEdge u v q.length hadj hmatch
  have hphase : (a.phase + a.length) % 2 = e.phase % 2 := by
    simp [a, e, ParitySegment.ofAltSegment, ParitySegment.ofEdge]
  have hjoin : a.last = e.first := hqu
  have hfresh (i : Fin (q.length + 1)) : q.vertex i ≠ v := by
    intro he
    have hc := hb.minimum_relative_confined t ht hut hmin q hq hqb hqu
      (q.vertex i) ⟨i, rfl⟩
    rcases hc with hc | hc
    · exact hvb (he.symm.trans hc)
    · obtain ⟨k, hk, hkt⟩ := blossom_tenacity_bound t b (q.vertex i) hc
      rw [he] at hk
      rw [hk] at hv
      change t < k at hv
      omega
  have hdis : ∀ (i : Fin (a.length + 1)) (j : Fin (e.length + 1)),
      0 < j.val → a.vertex i ≠ e.vertex j := by
    intro i j hj
    change q.vertex i ≠ (if j.val = 0 then u else v)
    simpa only [ite_eq_right (show ¬j.val = 0 by omega)] using hfresh i
  let r := a.append e hphase hjoin hdis
  let s := r.toAltSegment (by rfl)
  have hsf : s.first = b := (a.append_first e hphase hjoin hdis).trans hqb
  have hsl : s.last = v := (a.append_last e hphase hjoin hdis).trans rfl
  have hsn : s.length = q.length + 1 := rfl
  refine ⟨s, hsf, hsl, hsn, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hsf]
    simpa only [hut] using hb.high
  · rw [hsl]
    exact hv
  · intro i hi hil
    have hil' : i.val ≤ q.length := by change i.val < q.length + 1 at hil; omega
    have hc := (hb.minimum_relative_properties t ht hut hmin q hq hqb hqu).1
      ⟨i.val, by omega⟩ hi
    change Blossom M t s.first (r.vertex i)
    rw [hsf]
    simpa only [r, ParitySegment.append, dite_eq_left hil', a, ParitySegment.ofAltSegment] using hc

/-- Reverse the constructed base-to-exit path. The lower blossom is now at
the target of the directed edge, as required by ordinary downward H_v edges.
The starting matching phase uses the actual expanded length. -/
theorem IsBase.minimum_exit_reverse {u b v : V} (hb : IsBase M u b)
    (t : Nat) (ht : EligibleTenacity M t) (hut : tenacity M u = some t)
    (hmin : ∀ w : V, levelLE (some t) (tenacity M w))
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqu : q.last = u)
    (hv : levelLT (some t) (tenacity M v)) (hvb : v ≠ b)
    (hadj : G.Adj u v) (hmatch : (M.mate u = some v) ↔ q.length % 2 = 1) :
    ∃ s : ParitySegment M, s.first = v ∧ s.last = b ∧ s.length = q.length + 1 ∧
      s.phase % 2 = (q.length + 2) % 2 ∧
      (∀ i : Fin (s.length + 1), 0 < i.val → i.val < s.length →
        Blossom M t b (s.vertex i)) := by
  obtain ⟨a, haf, hal, han, hax⟩ :=
    hb.minimum_exit_segment t ht hut hmin q hq hqb hqu hv hvb hadj hmatch
  let s := (ParitySegment.ofAltSegment a).reverse
  refine ⟨s, ?_, ?_, han, ?_, ?_⟩
  · exact (ParitySegment.ofAltSegment a).reverse_first.trans hal
  · exact (ParitySegment.ofAltSegment a).reverse_last.trans haf
  · change (0 + a.length + 1) % 2 = (q.length + 2) % 2
    rw [han]
    omega
  · intro i hi hil
    have hi' : i.val < a.length := hil
    have hpos : 0 < a.length - i.val := by omega
    have hlt : a.length - i.val < a.length := by omega
    have ha := hax.2.2 ⟨a.length - i.val, by omega⟩ hpos hlt
    rw [haf] at ha
    exact ha

end MaximumMatching
