import MaximumMatching.MinTenacityGeometry

/-! The long parity path to a minimum-tenacity inner vertex has minimum tenacity
at every index from the short path's length onward. This strengthens the midpoint
geometry and supplies the suffix fact needed in the minimum-tenacity base case. -/
namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A first hit on an odd suffix beginning no earlier than the short path's
length must occur at an even index of the long path. An odd hit would give a
shorter same-parity replacement prefix; equality would identify the endpoint
with a strictly earlier vertex, violating simplicity. -/
theorem FirstHit.even_long_index {p q : AltPath M} {cut : Nat}
    (h : FirstHit q p cut) (hp : p.Shortest) (hpe : p.length % 2 = 0)
    (hcut : cut % 2 = 1) (hql : q.length ≤ cut)
    (hend : q.last = p.last) (_hinner : q.length < p.length) : h.pi.val % 2 = 0 := by
  by_cases he : h.pi.val % 2 = 0
  · exact he
  · have hpo : h.pi.val % 2 = 1 := by omega
    have hqo := h.odd hpe hcut
    have hb := p.no_shorter_disjoint_prefix hp h.pi.val (by omega)
      (q.take h.qi.val (by omega)) h.hit
      (by simp only [take_length, hqo, hpo]) h.forward_disjoint
    change h.pi.val ≤ h.qi.val at hb
    have hs := h.in_suffix
    have hi : h.qi.val = q.length := by omega
    have hj : h.pi.val = q.length := by omega
    have hqi : h.qi = ⟨q.length, by omega⟩ := Fin.ext hi
    have hlast : p.vertex h.pi = p.last := by
      rw [← h.hit, hqi]
      exact hend
    have heq := congrArg Fin.val (p.injective h.pi ⟨p.length, by omega⟩ hlast)
    change h.pi.val = p.length at heq
    omega

/-- After the short path's length, a first-hit splice supplies an opposite-parity
path of complementary length. The conclusion has no midpoint restriction. -/
theorem beyond_shorter_opposite (p q : AltPath M) (hp : p.Shortest)
    (hpe : p.length % 2 = 0) (hend : q.last = p.last)
    (hinner : q.length < p.length) (i : Fin (p.length + 1))
    (hi : q.length < i.val) :
    ∃ k, HasPathLength M ((i.val + 1) % 2) (p.vertex i) k ∧
      k ≤ p.length + q.length - i.val := by
  let cut := if i.val % 2 = 0 then i.val - 1 else i.val
  have hcodd : cut % 2 = 1 := by dsimp [cut]; split <;> omega
  have hcil : cut ≤ i.val := by dsimp [cut]; split <;> omega
  have hqcut : q.length ≤ cut := by dsimp [cut]; split <;> omega
  obtain ⟨h⟩ := firstHit_exists q p cut
    ⟨⟨q.length, by omega⟩, ⟨p.length, by omega⟩, by change cut ≤ p.length; omega, hend⟩
  have hqo := h.odd hpe hcodd
  have hpeven := h.even_long_index hp hpe hcodd hqcut hend hinner
  have hkj : i.val ≤ h.pi.val := by
    have hs := h.in_suffix
    dsimp [cut] at hs
    split at hs <;> omega
  let r := (q.take h.qi.val (by omega)).spliceReverse p i.val h.pi.val hkj
    (by omega) h.hit hqo hpeven (h.reverse_disjoint i.val hcil)
  have hrlen : r.length = h.qi.val + (h.pi.val - i.val) := rfl
  have hrend : r.last = p.vertex i := spliceReverse_last _ _ _ _ _ _ _ _ _ _
  refine ⟨r.length, ⟨r, hrend, rfl, by rw [hrlen]; omega⟩, ?_⟩
  rw [hrlen]
  omega

/-- Every vertex strictly after the short path's length has the same minimum
finite tenacity as the common endpoint. -/
theorem tenacity_beyond_shorter (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (hmin : ∀ v : V, levelLE (some (p.length + q.length)) (tenacity M v))
    (i : Fin (p.length + 1)) (hi : q.length < i.val) :
    tenacity M (p.vertex i) = some (p.length + q.length) := by
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hhon := p.prefixes_honest_at_minimum hp (p.length + q.length) hten hmin i
  exact (levels_of_opposite_bound (p.vertex i) i.val (p.length + q.length)
    ((p.honest_iff_level i).1 hhon) (by omega) (hmin _)
    (p.beyond_shorter_opposite q hp hpe hend hinner i hi)).1

/-- The whole suffix beginning at the short path's length has minimum tenacity.
The boundary index is odd and inherits tenacity from its matched successor. -/
theorem tenacity_suffix_minimum (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (hmin : ∀ v : V, levelLE (some (p.length + q.length)) (tenacity M v))
    (i : Fin (p.length + 1)) (hi : q.length ≤ i.val) :
    tenacity M (p.vertex i) = some (p.length + q.length) := by
  by_cases hlt : q.length < i.val
  · exact p.tenacity_beyond_shorter q hp hq hpe hqo hend hinner hmin i hlt
  · have he : i.val = q.length := by omega
    have hmatch := p.mate_next i.val (by omega) (by omega)
    have hnext := p.tenacity_beyond_shorter q hp hq hpe hqo hend hinner hmin
      ⟨i.val + 1, by omega⟩ (by change q.length < i.val + 1; omega)
    exact (matched_tenacity M hmatch).1.trans hnext

end AltPath
end MaximumMatching
