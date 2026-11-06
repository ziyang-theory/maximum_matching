import MaximumMatching.MinimumSuffix

/-! Tenacity bounds on the suffix of a long even shortest path, without a global
minimum-tenacity assumption. The proof constructs both parity witnesses using
the proved simple first-hit splice, then bounds their semantic minima. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Two opposite-parity path witnesses bound the finite vertex tenacity by
the sum of their lengths. -/
theorem tenacity_bound_of_opposite_witnesses (v : V) (i k : Nat)
    (hi : HasPathLength M (i % 2) v i)
    (hk : HasPathLength M ((i + 1) % 2) v k) :
    ∃ t, tenacity M v = some t ∧ t ≤ i + k := by
  have finite_bound (parity len : Nat) (h : HasPathLength M parity v len) :
      ∃ a, level M parity v = some a ∧ a ≤ len := by
    cases ha : level M parity v with
    | none => exact False.elim ((level_eq_none_iff M parity v).1 ha ⟨len, h⟩)
    | some a => exact ⟨a, rfl, ((level_eq_some_iff M parity v a).1 ha).2 len h⟩
  obtain ⟨a, ha, hai⟩ := finite_bound (i % 2) i hi
  obtain ⟨b, hb, hbk⟩ := finite_bound ((i + 1) % 2) k hk
  by_cases hie : i % 2 = 0
  · have hio : (i + 1) % 2 = 1 := by omega
    refine ⟨a + b, ?_, by omega⟩
    simpa only [tenacity, evenlevel, oddlevel, hie, hio, levelAdd] using
      (show levelAdd (level M (i % 2) v) (level M ((i + 1) % 2) v) = some (a + b) by rw [ha, hb]; rfl)
  · have hio : i % 2 = 1 := by omega
    have hie' : (i + 1) % 2 = 0 := by omega
    refine ⟨b + a, ?_, by omega⟩
    simpa only [tenacity, evenlevel, oddlevel, hio, hie', levelAdd] using
      (show levelAdd (level M ((i + 1) % 2) v) (level M (i % 2) v) = some (b + a) by rw [hb, ha]; rfl)

namespace AltPath

/-- After the short path's length, vertex tenacity is finite and no greater
than the sum of the two endpoint path lengths. Only the long path needs to
be shortest; the short path supplies an actual opposite-parity witness. -/
theorem tenacity_bound_beyond_shorter (p q : AltPath M) (hp : p.Shortest)
    (hpe : p.length % 2 = 0) (hend : q.last = p.last)
    (hinner : q.length < p.length) (i : Fin (p.length + 1))
    (hi : q.length < i.val) :
    ∃ t, tenacity M (p.vertex i) = some t ∧ t ≤ p.length + q.length := by
  obtain ⟨k, hk, hkt⟩ := p.beyond_shorter_opposite q hp hpe hend hinner i hi
  obtain ⟨t, ht, hti⟩ := tenacity_bound_of_opposite_witnesses (p.vertex i) i.val k
    (p.prefix_witness i) hk
  exact ⟨t, ht, by omega⟩

/-- The tenacity bound extends to the boundary index, which is odd and paired
with its successor. This includes every vertex from the short path's length. -/
theorem tenacity_bound_suffix (p q : AltPath M) (hp : p.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (i : Fin (p.length + 1)) (hi : q.length ≤ i.val) :
    ∃ t, tenacity M (p.vertex i) = some t ∧ t ≤ p.length + q.length := by
  by_cases hlt : q.length < i.val
  · exact p.tenacity_bound_beyond_shorter q hp hpe hend hinner i hlt
  · have he : i.val = q.length := by omega
    have hmatch := p.mate_next i.val (by omega) (by omega)
    obtain ⟨t, ht, htb⟩ := p.tenacity_bound_beyond_shorter q hp hpe hend hinner
      ⟨i.val + 1, by omega⟩ (by change q.length < i.val + 1; omega)
    exact ⟨t, (matched_tenacity M hmatch).1.trans ht, htb⟩

/-- No suffix vertex is above the endpoint path-length sum in tenacity. For
opposite shortest endpoint paths this sum is exactly the endpoint's tenacity. -/
theorem suffix_not_high_tenacity (p q : AltPath M) (hp : p.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (i : Fin (p.length + 1)) (hi : q.length ≤ i.val) :
    ¬ levelLT (some (p.length + q.length)) (tenacity M (p.vertex i)) := by
  obtain ⟨t, ht, htb⟩ := p.tenacity_bound_suffix q hp hpe hqo hend hinner i hi
  rw [ht]
  change ¬ p.length + q.length < t
  omega

end AltPath
end MaximumMatching
