import MaximumMatching.GeneralSuffix
import MaximumMatching.BaseUnique

/-! A general-tenacity common-base step that needs no global minimum premise.
The remaining predecessor case is the one inside a lower-tenacity blossom. -/
namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A predecessor above the endpoint tenacity must occur on every even shortest
path to that inner endpoint; otherwise its fresh extension supplies an opposite
path with tenacity at most the endpoint's. -/
theorem high_predecessor_occurs (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last)
    (hhigh : levelLT (some (p.length + q.length))
      (tenacity M (q.vertex ⟨q.length - 1, by omega⟩))) :
    ∃ i : Fin (p.length + 1), p.vertex i = q.vertex ⟨q.length - 1, by omega⟩ ∧
      i.val = q.length - 1 := by
  classical
  let u := q.vertex ⟨q.length - 1, by omega⟩
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hqten : tenacity M q.last = some (p.length + q.length) := by rw [hend]; exact hten
  have hum : minlevel M u = some (q.length - 1) := by
    exact (q.limited_bfs_honesty hq ⟨q.length - 1, by omega⟩ (by
      rw [hqten]; exact levelLT_le hhigh)).2 (by rw [hqten]; exact hhigh)
  have hon : ∃ i : Fin (p.length + 1), p.vertex i = u := by
    by_cases hon : ∃ i : Fin (p.length + 1), p.vertex i = u
    · exact hon
    apply False.elim
    have hfresh : ∀ i, p.vertex i ≠ u := by intro i hi; exact hon ⟨i, hi⟩
    have hadj : G.Adj p.last u := by
      rw [← hend]
      have he : q.length - 1 + 1 = q.length := by omega
      simpa only [he, last, u] using G.symm (q.adjacent ⟨q.length - 1, by omega⟩)
    let r := p.append u hfresh hadj (p.inner_predecessor_append_parity q hpe hqo hend)
    have hw0 : HasPathLength M ((q.length - 1) % 2) u (q.length - 1) :=
      q.prefix_witness ⟨q.length - 1, by omega⟩
    have hw1 : HasPathLength M ((q.length - 1 + 1) % 2) u (p.length + 1) :=
      ⟨r, append_last _ _ _ _ _, rfl, by omega⟩
    obtain ⟨s, hs, hsb⟩ := tenacity_bound_of_opposite_witnesses u (q.length - 1) (p.length + 1) hw0 hw1
    have hh : levelLT (some (p.length + q.length)) (tenacity M u) := hhigh
    have ht : p.length + q.length < s := by simpa only [hs, levelLT] using hh
    omega
  obtain ⟨i, hi⟩ := hon
  have him : minlevel M (p.vertex i) = some i.val :=
    (p.limited_bfs_honesty hp i (by rw [hten, hi]; exact levelLT_le hhigh)).2
      (by rw [hten, hi]; exact hhigh)
  rw [hi] at him
  exact ⟨i, hi, Option.some.inj (him.symm.trans hum)⟩

/-- When the last predecessor of an odd minlevel path has tenacity greater than
the endpoint's, it is the base on both parity paths. All later vertices on the
even path are bounded by `GeneralSuffix`, without any minimum-tenacity premise. -/
theorem high_predecessor_bases (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (hhigh : levelLT (some (p.length + q.length))
      (tenacity M (q.vertex ⟨q.length - 1, by omega⟩))) :
    p.BaseOnPath (p.length + q.length) (q.vertex ⟨q.length - 1, by omega⟩) ∧
      q.BaseOnPath (p.length + q.length) (q.vertex ⟨q.length - 1, by omega⟩) := by
  obtain ⟨i, hi, hil⟩ := p.high_predecessor_occurs q hp hq hpe hqo hend hhigh
  constructor
  · refine ⟨i, hi, hhigh, ?_⟩
    intro j hj
    exact p.suffix_not_high_tenacity q hp hpe hqo hend hinner j (by omega)
  · refine ⟨⟨q.length - 1, by omega⟩, rfl, hhigh, ?_⟩
    intro j hj
    have he : j = ⟨q.length, by omega⟩ := Fin.ext (by
      change j.val = q.length
      change q.length - 1 < j.val at hj
      omega)
    rw [he]
    change ¬levelLT (some (p.length + q.length)) (tenacity M q.last)
    have ht := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
    rw [hend, ht]
    change ¬ p.length + q.length < p.length + q.length
    omega

end AltPath
end MaximumMatching
