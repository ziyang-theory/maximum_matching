import MaximumMatching.GeneralBaseChain
import MaximumMatching.RelativeJoin

/-! Relative shortest paths through iterated actual bases. These facts apply to
source-recursive blossoms without assuming general base existence or confinement.
They extend the direct-base decomposition to an entire established base chain. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A blossom boundary is the last vertex above its threshold on every shortest
path to a member. This follows from the actual common-base chain. -/
theorem blossom_baseOnPath (t : Nat) (b v : V) (h : Blossom M t b v)
    (hb : levelLT (some t) (tenacity M b))
    (p : AltPath M) (hpv : p.last = v) (hp : p.Shortest) : p.BaseOnPath t b := by
  obtain ⟨i, hi, _, _, _, _, hpreserve⟩ :=
    blossom_threshold_prefix t t (Nat.le_refl _) b v h p hpv hp
  apply (hpreserve b).2
  refine ⟨⟨i.val, by change i.val < i.val + 1; omega⟩, hi, hb, ?_⟩
  intro j hj
  change i.val < j.val at hj
  have := j.isLt
  change j.val < i.val + 1 at this
  omega

/-- The suffix after an established blossom boundary is shortest among relative
paths of its parity. The opposite global path supplies the length budget. -/
theorem blossom_shortest_relative (t : Nat) (b v : V) (h : Blossom M t b v)
    (hb : levelLT (some t) (tenacity M b))
    (p : AltPath M) (hpv : p.last = v) (hp : p.Shortest) :
    ∃ i : Fin (p.length + 1), ∃ hie : i.val % 2 = 0, p.vertex i = b ∧
      (p.take i.val (by omega)).Shortest ∧
      (p.segment i.val (by omega) hie).Shortest := by
  obtain ⟨s, hvs, hst⟩ := blossom_tenacity_bound t b v h
  obtain ⟨i, hi, hie, _, himin, hip⟩ := blossom_on_shortest t b v h p hpv hp
  obtain ⟨q, hqv, hq, hqpar⟩ := finite_tenacity_shortest_parity v s (p.length + 1) hvs
  obtain ⟨j, _, _, hjlt, hjmin, _⟩ := blossom_on_shortest t b v h q hqv hq
  have hji : j.val = i.val := Option.some.inj (hjmin.symm.trans himin)
  have hsum : p.length + q.length = s := by
    have hten : tenacity M v = some (p.length + q.length) := by
      by_cases hpe : p.length % 2 = 0
      · simpa only [hpv] using p.opposite_shortest_tenacity q hp hq
          (hpv.trans hqv.symm) hpe (by omega)
      · have hqe : q.length % 2 = 0 := by omega
        simpa only [hqv, Nat.add_comm] using q.opposite_shortest_tenacity p hq hp
          (hqv.trans hpv.symm) hqe (by omega)
    exact Option.some.inj (hten.symm.trans hvs)
  refine ⟨i, hie, hi, hip, ?_⟩
  apply p.segment_shortest_of_high hp i hie t
  · exact (level_eq_some_iff M 0 (p.vertex i) i.val).2
      (by simpa only [AltPath.Shortest, AltPath.take_length, AltPath.take_last, hie] using hip)
  · simpa only [hi] using hb
  · omega

/-- Every vertex strictly after the boundary has tenacity at most the blossom
threshold, even when that prefix is not itself shortest. Membership in the
blossom is a stronger statement and is not concluded here. -/
theorem blossom_suffix_tenacity_bound (t : Nat) (b v : V) (h : Blossom M t b v)
    (hb : levelLT (some t) (tenacity M b))
    (p : AltPath M) (hpv : p.last = v) (hp : p.Shortest)
    (i j : Fin (p.length + 1)) (hi : p.vertex i = b) (hij : i.val < j.val) :
    ∃ s, tenacity M (p.vertex j) = some s ∧ s ≤ t := by
  obtain ⟨k, hk, _, htail⟩ := blossom_baseOnPath t b v h hb p hpv hp
  have hik := p.injective i k (hi.trans hk.symm)
  have hn := htail j (by simpa only [hik] using hij)
  cases hs : tenacity M (p.vertex j) with
  | none => exact False.elim (hn (by rw [hs]; trivial))
  | some s =>
    have hn' : ¬t < s := by simpa only [hs, levelLT] using hn
    exact ⟨s, rfl, by omega⟩

end MaximumMatching
