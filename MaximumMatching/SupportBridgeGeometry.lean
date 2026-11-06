import MaximumMatching.SupportBridgeAbsence
import MaximumMatching.SupportMaxHighBound

/-! Actual minimum/maximum level geometry on the two sides of the unique current bridge. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A finite parity level is either the minimum or the maximum of the two
parity levels. An infinite opposite level forces the minimum branch. -/
theorem parity_level_min_or_max (v : V) (k : Nat)
    (hk : level M (k % 2) v = some k) :
    minlevel M v = some k ∨ maxlevel M v = some k := by
  by_cases hke : k % 2 = 0
  · have he : evenlevel M v = some k := by simpa only [hke] using hk
    cases ho : oddlevel M v with
    | none => exact Or.inl (by simp only [minlevel, he, ho, levelMin])
    | some j =>
      by_cases hkj : k ≤ j
      · exact Or.inl (by simp only [minlevel, he, ho, levelMin, Nat.min_eq_left hkj])
      · exact Or.inr (by simp only [maxlevel, he, ho, levelMax, Nat.max_eq_left (by omega : j ≤ k)])
  · have hko : k % 2 = 1 := by omega
    have ho : oddlevel M v = some k := by simpa only [hko] using hk
    cases he : evenlevel M v with
    | none => exact Or.inl (by simp only [minlevel, he, ho, levelMin])
    | some j =>
      by_cases hkj : k ≤ j
      · exact Or.inl (by simp only [minlevel, he, ho, levelMin, Nat.min_eq_right hkj])
      · exact Or.inr (by simp only [maxlevel, he, ho, levelMax, Nat.max_eq_right (by omega : j ≤ k)])

namespace AltPath

/-- Every high-core vertex before the current bridge is reached at its
minimum level. A maximum-level prefix there would contain an earlier
current bridge, contradicting the proved unique-bridge theorem. -/
theorem current_bridge_before_minlevel (p : AltPath M) (t : Nat)
    (ht : AtMostShortestAugmenting M t) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length) (I : Fin p.length)
    (hIb : Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩))
    (hIt : edgeTenacity M (p.vertex ⟨I.val, by omega⟩)
      (p.vertex ⟨I.val + 1, by omega⟩) = some t)
    (K : Fin (p.length + 1)) (hKI : K.val ≤ I.val)
    (hKhigh : levelLE (some t) (tenacity M (p.vertex K))) :
    minlevel M (p.vertex K) = some K.val := by
  have hp := p.shortest_of_maxlevel hmax
  obtain ⟨hKhon, hKmin⟩ := p.limited_bfs_honesty hp K (by rw [hpt]; exact hKhigh)
  by_cases hstrict : levelLT (some t) (tenacity M (p.vertex K))
  · exact hKmin (by rw [hpt]; exact hstrict)
  · have hKt : tenacity M (p.vertex K) = some t := by
      cases he : tenacity M (p.vertex K) with
      | none => exact False.elim (hstrict (by rw [he]; trivial))
      | some k =>
        have htk : t ≤ k := by simpa only [he, levelLE] using hKhigh
        have hkt : ¬t < k := by simpa only [he, levelLT] using hstrict
        have hke : k = t := by omega
        exact congrArg some hke
    rcases parity_level_min_or_max (p.vertex K) K.val ((p.honest_iff_level K).1 hKhon) with hmin | hmaxK
    · exact hmin
    · let q := p.take K.val (by omega)
      obtain ⟨J, hJb, hJt, _⟩ := q.general_maxlevel_path_unique_bridge t ht hKt hmaxK
      obtain ⟨Z, _, _, huniq⟩ := p.general_maxlevel_path_unique_bridge t ht hpt hmax
      have hJp : J.val < p.length := by have := J.isLt; change J.val < K.val at this; omega
      have he := (huniq I hIb hIt).trans (huniq ⟨J.val, hJp⟩ hJb hJt).symm
      have hv := congrArg Fin.val he
      have := J.isLt
      change J.val < K.val at this
      dsimp only at hv
      omega

/-- A same-tenacity vertex after the current bridge is reached at its
maximum level. Its minimum-level prefix would be too short to contain the
already traversed current bridge. -/
theorem current_bridge_after_maxlevel (p : AltPath M) (t : Nat)
    (ht : AtMostShortestAugmenting M t) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length) (I : Fin p.length)
    (hIb : Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩))
    (hIt : edgeTenacity M (p.vertex ⟨I.val, by omega⟩)
      (p.vertex ⟨I.val + 1, by omega⟩) = some t)
    (K : Fin (p.length + 1)) (hIK : I.val < K.val)
    (hKt : tenacity M (p.vertex K) = some t) :
    maxlevel M (p.vertex K) = some K.val := by
  have hp := p.shortest_of_maxlevel hmax
  have htodd := tenacity_odd M p.last t hpt
  have hKhon := (p.limited_bfs_honesty hp K (by rw [hpt, hKt]; exact Nat.le_refl _)).1
  rcases parity_level_min_or_max (p.vertex K) K.val ((p.honest_iff_level K).1 hKhon) with hmin | hmaxK
  · have hbound := twice_minlevel_le_tenacity (p.vertex K) K.val t hmin hKt
    have hshort : 2 * K.val < t := by omega
    have hn := (p.take K.val (by omega)).short_shortest_no_current_bridge hKhon t ht htodd hshort
    exact False.elim (hn ⟨I.val, hIK⟩ hIb hIt)
  · exact hmaxK

/-- Any vertex above the current threshold occurs before the current
bridge. Its actual common-base prefix is shorter than half the threshold. -/
theorem current_bridge_after_high_vertex (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (ht : EligibleTenacity M t) (hpt : tenacity M p.last = some t)
    (I : Fin p.length)
    (hIb : Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩))
    (hIt : edgeTenacity M (p.vertex ⟨I.val, by omega⟩)
      (p.vertex ⟨I.val + 1, by omega⟩) = some t)
    (K : Fin (p.length + 1)) (hKhigh : levelLT (some t) (tenacity M (p.vertex K))) :
    K.val ≤ I.val := by
  obtain ⟨b, hb, _⟩ := general_unique_base M t ht p.last hpt
  have hbase : IsBase M p.last b := ⟨t, hpt, hb⟩
  obtain ⟨B, hB, hBhigh, hBlast⟩ := hb p rfl hp
  obtain ⟨k, hk, _⟩ := minlevel_finite_of_path p
  obtain ⟨j, hj, hjk⟩ := hbase.minlevel_lt k hk
  have hhigh : levelLT (tenacity M p.last) (tenacity M (p.vertex B)) := by
    rw [hpt, hB]; exact hBhigh
  obtain ⟨hBhon, hBmin⟩ := p.limited_bfs_honesty hp B (levelLT_le hhigh)
  have hBm : minlevel M b = some B.val := by simpa only [hB] using hBmin hhigh
  have hBj : B.val = j := Option.some.inj (hBm.symm.trans hj)
  have hbound := twice_minlevel_le_tenacity p.last k t hk hpt
  have hshort : 2 * B.val < t := by omega
  have hKB : K.val ≤ B.val := by
    by_cases hh : K.val ≤ B.val
    · exact hh
    · exact False.elim (hBlast K (by omega) hKhigh)
  by_cases hKI : K.val ≤ I.val
  · exact hKI
  · have htop : AtMostShortestAugmenting M t := fun q hq => Nat.le_of_lt (ht.2.2 q hq)
    have hn := (p.take B.val (by omega)).short_shortest_no_current_bridge hBhon t htop ht.1 hshort
    exact False.elim (hn ⟨I.val, by change I.val < B.val; omega⟩ hIb hIt)

/-- On a maximum-level path the same exclusion holds at the shortest
augmenting threshold; a common base is not required. -/
theorem maxlevel_current_bridge_after_high_vertex (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (ht : AtMostShortestAugmenting M t) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length) (I : Fin p.length)
    (hIb : Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩))
    (hIt : edgeTenacity M (p.vertex ⟨I.val, by omega⟩)
      (p.vertex ⟨I.val + 1, by omega⟩) = some t)
    (K : Fin (p.length + 1)) (hKhigh : levelLT (some t) (tenacity M (p.vertex K))) :
    K.val ≤ I.val := by
  have hshort := p.maxlevel_strict_high_index_below_half hp t hpt hmax K hKhigh
  have hhon := (p.limited_bfs_honesty hp K (by rw [hpt]; exact levelLT_le hKhigh)).1
  by_cases hKI : K.val ≤ I.val
  · exact hKI
  · have hn := (p.take K.val (by omega)).short_shortest_no_current_bridge hhon t ht
      (tenacity_odd M p.last t hpt) hshort
    exact False.elim (hn ⟨I.val, by change I.val < K.val; omega⟩ hIb hIt)

/-- The descending high core has exactly the current tenacity and the
complementary minimum index, without a supplied level-shape invariant. -/
theorem current_bridge_after_geometry (p : AltPath M) (t : Nat)
    (ht : AtMostShortestAugmenting M t) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length) (I : Fin p.length)
    (hIb : Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩))
    (hIt : edgeTenacity M (p.vertex ⟨I.val, by omega⟩)
      (p.vertex ⟨I.val + 1, by omega⟩) = some t)
    (K : Fin (p.length + 1)) (hIK : I.val < K.val)
    (hKhigh : levelLE (some t) (tenacity M (p.vertex K))) :
    tenacity M (p.vertex K) = some t ∧
      minlevel M (p.vertex K) = some (t - K.val) ∧ K.val ≤ t ∧ t < 2 * K.val := by
  have hp := p.shortest_of_maxlevel hmax
  have htop : AtMostShortestAugmenting M t := ht
  have hKt : tenacity M (p.vertex K) = some t := by
    cases he : tenacity M (p.vertex K) with
    | none =>
      have hi := p.maxlevel_current_bridge_after_high_vertex hp t ht hpt hmax I hIb hIt K (by rw [he]; trivial)
      omega
    | some k =>
      have htk : t ≤ k := by simpa only [he, levelLE] using hKhigh
      by_cases hkt : k = t
      · exact congrArg some hkt
      · have hi := p.maxlevel_current_bridge_after_high_vertex hp t ht hpt hmax I hIb hIt K
          (by rw [he]; change t < k; omega)
        omega
  have hKm := p.current_bridge_after_maxlevel t htop hpt hmax I hIb hIt K hIK hKt
  obtain ⟨k, hk, _⟩ := minlevel_finite_of_path (p.take K.val (by omega))
  change minlevel M (p.vertex K) = some k at hk
  have hsum := minlevel_add_maxlevel M (p.vertex K)
  rw [hk, hKm, hKt] at hsum
  have hsum' : k + K.val = t := by simpa only [levelAdd, Option.some.injEq] using hsum
  have htwice := twice_minlevel_le_tenacity (p.vertex K) k t hk hKt
  have hodd := tenacity_odd M p.last t hpt
  exact ⟨hKt, hk.trans (congrArg some (by omega)), by omega, by omega⟩

end AltPath
end MaximumMatching
