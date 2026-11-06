import MaximumMatching.SameRoot

/-! Layer geometry at the minimum finite tenacity, for Lemma 6.13. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A witnessed parity level below half the global minimum tenacity is the
minimum of the two parity levels. Infinite opposite levels are included. -/
theorem minlevel_of_below_half (v : V) (i t : Nat)
    (hi : level M (i % 2) v = some i) (hhalf : 2 * i < t)
    (hmin : levelLE (some t) (tenacity M v)) : minlevel M v = some i := by
  by_cases hie : i % 2 = 0
  · have he : evenlevel M v = some i := by simpa only [hie] using hi
    unfold minlevel
    rw [he]
    cases ho : oddlevel M v with
    | none => rfl
    | some k =>
      have ht : t ≤ i + k := by simpa only [tenacity, he, ho, levelAdd, levelLE] using hmin
      change some (min i k) = some i
      rw [Nat.min_eq_left (by omega)]
  · have hio : i % 2 = 1 := by omega
    have ho : oddlevel M v = some i := by simpa only [hio] using hi
    unfold minlevel
    rw [ho]
    cases he : evenlevel M v with
    | none => rfl
    | some k =>
      have ht : t ≤ k + i := by simpa only [tenacity, he, ho, levelAdd, levelLE] using hmin
      change some (min k i) = some i
      rw [Nat.min_eq_right (by omega)]

/-- An opposite-parity path of length at most `t-i`, together with honesty at
index i and the global tenacity lower bound, pins down both levels exactly. -/
theorem levels_of_opposite_bound (v : V) (i t : Nat)
    (hi : level M (i % 2) v = some i) (hit : i ≤ t)
    (hmin : levelLE (some t) (tenacity M v))
    (hw : ∃ k, HasPathLength M ((i + 1) % 2) v k ∧ k ≤ t - i) :
    tenacity M v = some t ∧ minlevel M v = some (min i (t - i)) := by
  obtain ⟨k, hk, hkt⟩ := hw
  have hother : ∃ j, level M ((i + 1) % 2) v = some j ∧ j ≤ k := by
    cases ho : level M ((i + 1) % 2) v with
    | none => exact False.elim ((level_eq_none_iff M ((i + 1) % 2) v).1 ho ⟨k, hk⟩)
    | some j => exact ⟨j, rfl, ((level_eq_some_iff M ((i + 1) % 2) v j).1 ho).2 k hk⟩
  obtain ⟨j, hj, hjk⟩ := hother
  by_cases hie : i % 2 = 0
  · have hio : (i + 1) % 2 = 1 := by omega
    have he : evenlevel M v = some i := by simpa only [hie] using hi
    have ho : oddlevel M v = some j := by simpa only [hio] using hj
    have ht : t ≤ i + j := by simpa only [tenacity, he, ho, levelAdd, levelLE] using hmin
    have hjt : j = t - i := by omega
    simp only [tenacity, minlevel, he, ho, levelAdd, levelMin, hjt]
    exact ⟨congrArg some (by omega), trivial⟩
  · have hio : i % 2 = 1 := by omega
    have hie' : (i + 1) % 2 = 0 := by omega
    have ho : oddlevel M v = some i := by simpa only [hio] using hi
    have he : evenlevel M v = some j := by simpa only [hie'] using hj
    have ht : t ≤ j + i := by simpa only [tenacity, he, ho, levelAdd, levelLE] using hmin
    have hjt : j = t - i := by omega
    simp only [tenacity, minlevel, he, ho, levelAdd, levelMin, hjt]
    exact ⟨congrArg some (by omega), congrArg some (Nat.min_comm _ _)⟩

namespace AltPath

/-- Past the midpoint of a shortest even path to an inner endpoint, the other
shortest endpoint path gives an opposite-parity path of the complementary length.
The first-hit construction enforces simplicity; no walk erasure is assumed. -/
theorem above_half_opposite (p q : AltPath M) (hp : p.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (i : Fin (p.length + 1)) (hhalf : p.length + q.length < 2 * i.val) :
    ∃ k, HasPathLength M ((i.val + 1) % 2) (p.vertex i) k ∧
      k ≤ p.length + q.length - i.val := by
  have hiq : q.length < i.val := by omega
  by_cases hie : i.val % 2 = 0
  · rcases p.odd_terminal_comparison hp hpe i.val (by omega) (by omega) hie q hend with hw | hl
    · obtain ⟨k, hk, hkb⟩ := hw
      refine ⟨k, ?_, by omega⟩
      simpa only [show (i.val + 1) % 2 = 1 by omega] using hk
    · have hilast : i.val = p.length := by omega
      have hi : i = ⟨p.length, by omega⟩ := Fin.ext hilast
      refine ⟨q.length, ⟨q, ?_, rfl, by omega⟩, by omega⟩
      rw [hi]
      exact hend
  · have hio : i.val % 2 = 1 := by omega
    obtain ⟨h⟩ := firstHit_exists q p i.val
      ⟨⟨q.length, by omega⟩, ⟨p.length, by omega⟩, by change i.val ≤ p.length; omega, hend⟩
    have hqi := h.odd hpe hio
    have hpi : h.pi.val % 2 = 0 := by
      by_cases hpi : h.pi.val % 2 = 0
      · exact hpi
      · have hpip : h.pi.val % 2 = 1 := by omega
        have hbound := p.no_shorter_disjoint_prefix hp h.pi.val (by omega)
          (q.take h.qi.val (by omega)) h.hit (by simp only [take_length, hqi, hpip])
          h.forward_disjoint
        change h.pi.val ≤ h.qi.val at hbound
        have := h.in_suffix
        omega
    let r := (q.take h.qi.val (by omega)).spliceReverse p i.val h.pi.val h.in_suffix
      (by omega) h.hit hqi hpi (h.reverse_disjoint i.val (by omega))
    have hsuffix := h.in_suffix
    have hrlen : r.length = h.qi.val + (h.pi.val - i.val) := rfl
    have hrend : r.last = p.vertex i := spliceReverse_last _ _ _ _ _ _ _ _ _ _
    refine ⟨r.length, ⟨r, hrend, rfl, by rw [hrlen]; omega⟩, ?_⟩
    rw [hrlen]
    omega

/-- Every shortest even path to an inner minimum-tenacity vertex rises one layer
per edge to the middle bridge, then falls one layer per edge. -/
theorem minlevel_triangle (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (hmin : ∀ v : V, levelLE (some (p.length + q.length)) (tenacity M v))
    (i : Fin (p.length + 1)) :
    minlevel M (p.vertex i) = some (min i.val (p.length + q.length - i.val)) := by
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hhon := p.prefixes_honest_at_minimum hp (p.length + q.length) hten hmin i
  have hlevel := (p.honest_iff_level i).1 hhon
  by_cases hhalf : 2 * i.val < p.length + q.length
  · have hm := minlevel_of_below_half (p.vertex i) i.val (p.length + q.length)
      hlevel hhalf (hmin _)
    rw [hm, Nat.min_eq_left (by omega)]
  · have hstrict : p.length + q.length < 2 * i.val := by omega
    exact (levels_of_opposite_bound (p.vertex i) i.val (p.length + q.length)
      hlevel (by omega) (hmin _) (p.above_half_opposite q hp hpe hqo hend hinner i hstrict)).2

/-- Vertices after the middle bridge have exactly the minimum tenacity. -/
theorem tenacity_above_half (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (hmin : ∀ v : V, levelLE (some (p.length + q.length)) (tenacity M v))
    (i : Fin (p.length + 1)) (hhalf : p.length + q.length < 2 * i.val) :
    tenacity M (p.vertex i) = some (p.length + q.length) := by
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hhon := p.prefixes_honest_at_minimum hp (p.length + q.length) hten hmin i
  exact (levels_of_opposite_bound (p.vertex i) i.val (p.length + q.length)
    ((p.honest_iff_level i).1 hhon) (by omega) (hmin _)
    (p.above_half_opposite q hp hpe hqo hend hinner i hhalf)).1

/-- Every prefix of the odd minlevel path reaches its own minlevel. -/
theorem odd_minlevel_prefix (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (hmin : ∀ v : V, levelLE (some (p.length + q.length)) (tenacity M v))
    (i : Fin (q.length + 1)) : minlevel M (q.vertex i) = some i.val := by
  have hten : tenacity M q.last = some (p.length + q.length) := by
    rw [hend]
    exact p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hhon := q.prefixes_honest_at_minimum hq (p.length + q.length) hten hmin i
  exact minlevel_of_below_half (q.vertex i) i.val (p.length + q.length)
    ((q.honest_iff_level i).1 hhon) (by omega) (hmin _)

end AltPath
end MaximumMatching
