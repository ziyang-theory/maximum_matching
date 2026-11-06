import MaximumMatching.GeneralBaseInduction
import MaximumMatching.GeneralBridgeStructure
import MaximumMatching.GeneralPathGeometry
import MaximumMatching.MatchingSearchGraph

section SupportHighBound

/-! Relevant original path vertices are already covered by MIN at the current
tenacity stage. The bound for vertices above the endpoint tenacity uses the
actual common base, its last occurrence, and its strictly smaller minimum level. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A high vertex on any shortest path to an eligible-tenacity endpoint has
minimum level strictly below half the endpoint tenacity. -/
theorem high_vertex_minlevel_lt_half (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (ht : EligibleTenacity M t) (hpt : tenacity M p.last = some t)
    (I : Fin (p.length + 1))
    (hhigh : levelLE (some t) (tenacity M (p.vertex I))) :
    ∃ k, minlevel M (p.vertex I) = some k ∧ 2 * k < t := by
  by_cases heq : tenacity M (p.vertex I) = some t
  · obtain ⟨e, o, he, ho, _, _, hsum⟩ := finite_levels_of_tenacity (p.vertex I) t heq
    refine ⟨min e o, by simp only [minlevel, he, ho, levelMin], ?_⟩
    have hle := Nat.min_le_left e o
    have hle' := Nat.min_le_right e o
    have hodd := ht.1
    omega
  · have hstrict : levelLT (some t) (tenacity M (p.vertex I)) := by
      cases hi : tenacity M (p.vertex I) with
      | none => trivial
      | some s =>
        have hs : t ≤ s := by simpa only [hi, levelLE] using hhigh
        have hne : s ≠ t := by intro h; apply heq; rw [hi, h]
        change t < s
        omega
    have hImin := (p.limited_bfs_honesty hp I (by rw [hpt]; exact hhigh)).2
      (by rw [hpt]; exact hstrict)
    obtain ⟨b, hb, _⟩ := general_unique_base M t ht p.last hpt
    obtain ⟨B, hBb, hBhigh, hBlast⟩ := hb p rfl hp
    have hIB : I.val ≤ B.val := by
      by_cases hle : I.val ≤ B.val
      · exact hle
      · exact False.elim (hBlast I (by omega) hstrict)
    have hBmin := (p.limited_bfs_honesty hp B (by rw [hpt, hBb]; exact levelLT_le hBhigh)).2
      (by rw [hpt, hBb]; exact hBhigh)
    obtain ⟨e, o, he, ho, _, _, hsum⟩ := finite_levels_of_tenacity p.last t hpt
    have hvmin : minlevel M p.last = some (min e o) := by
      simp only [minlevel, he, ho, levelMin]
    have hbbase : IsBase M p.last b := ⟨t, hpt, hb⟩
    obtain ⟨j, hj, hjlt⟩ := hbbase.minlevel_lt (min e o) hvmin
    have hBj : B.val = j := by
      rw [hBb, hj] at hBmin
      exact Option.some.inj hBmin.symm
    refine ⟨I.val, hImin, ?_⟩
    have hle := Nat.min_le_left e o
    have hle' := Nat.min_le_right e o
    omega

end MaximumMatching.AltPath

namespace MaximumMatching.Search.BudGraphInvariant
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}
variable {cap : Nat} {s : State V} {F : BudForest V}

/-- Actual MIN coverage labels every relevant high vertex of an original
shortest path; callers need no separate assignment oracle for compression. -/
theorem high_path_vertex_assigned (h : BudGraphInvariant M cap s F)
    (p : AltPath M) (hp : p.Shortest) (t : Nat) (ht : EligibleTenacity M t)
    (hpt : tenacity M p.last = some t) (hcap : t ≤ 2 * cap + 1)
    (I : Fin (p.length + 1))
    (hhigh : levelLE (some t) (tenacity M (p.vertex I))) :
    ∃ k, s.minLabel (p.vertex I) = some k ∧
      minlevel M (p.vertex I) = some k ∧ 2 * k < t ∧ k ≤ cap := by
  obtain ⟨k, hk, hkt⟩ := p.high_vertex_minlevel_lt_half hp t ht hpt I hhigh
  have hkc : k ≤ cap := by omega
  exact ⟨k, h.minInvariant.2.1 _ _ hk hkc, hk, hkt, hkc⟩

end MaximumMatching.Search.BudGraphInvariant

end SupportHighBound

section SupportMaxHighBound

/-! High-core bounds for maximum-level paths, including the shortest
augmenting-path threshold where a common base need not exist. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

private theorem even_maxlevel_strict_high_index_below_half (p : AltPath M)
    (hp : p.Shortest) (hpe : p.length % 2 = 0) (t : Nat)
    (hpt : tenacity M p.last = some t) (hmax : maxlevel M p.last = some p.length)
    (I : Fin (p.length + 1))
    (hhigh : levelLT (some t) (tenacity M (p.vertex I))) : 2 * I.val < t := by
  obtain ⟨e, o, he, ho, hep, hop, hsum⟩ := finite_levels_of_tenacity p.last t hpt
  have hpel : evenlevel M p.last = some p.length :=
    (level_eq_some_iff M 0 p.last p.length).2 (by simpa only [Shortest, hpe] using hp)
  have heq : e = p.length := Option.some.inj (he.symm.trans hpel)
  have hmax' : max e o = p.length := by
    simpa only [maxlevel, he, ho, levelMax, Option.some.injEq] using hmax
  have hqshort := (level_eq_some_iff M 1 p.last o).1 ho
  obtain ⟨q, hqend, hqlen, hqo⟩ := hqshort.1
  have hq : q.Shortest := by simpa only [Shortest, hqlen, hqo, hqend] using hqshort
  have htotal : p.length + q.length = t := by omega
  have htriangle := p.high_minlevel_triangle q hp hq hpe (by omega) hqend (by omega) I
    (by rw [htotal]; exact levelLT_le hhigh)
  have hmin := (p.limited_bfs_honesty hp I
    (by rw [hpt]; exact levelLT_le hhigh)).2 (by rw [hpt]; exact hhigh)
  rw [htotal, hmin, Option.some.injEq] at htriangle
  have htodd := tenacity_odd M p.last t hpt
  have hle := Nat.min_le_right I.val (t - I.val)
  have hIt : I.val ≤ t := by have := I.isLt; omega
  omega

/-- Strictly higher-tenacity vertices lie before the midpoint on any actual
maximum-level path. No strict augmentation threshold or common base is needed. -/
theorem maxlevel_strict_high_index_below_half (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length) (I : Fin (p.length + 1))
    (hhigh : levelLT (some t) (tenacity M (p.vertex I))) : 2 * I.val < t := by
  by_cases hpe : p.length % 2 = 0
  · exact p.even_maxlevel_strict_high_index_below_half hp hpe t hpt hmax I hhigh
  · have hpo : p.length % 2 = 1 := by omega
    have hpol : oddlevel M p.last = some p.length :=
      (level_eq_some_iff M 1 p.last p.length).2 (by simpa only [Shortest, hpo] using hp)
    cases hm : M.mate p.last with
    | none =>
      have he : evenlevel M p.last = some 0 := (evenlevel_zero_iff_free M p.last).2 hm
      have hlen : p.length = t := by
        simpa only [tenacity, he, hpol, levelAdd, Nat.zero_add, Option.some.injEq] using hpt
      obtain ⟨s, hs, hsl⟩ := p.augmenting_tenacity_bound ⟨hpo, hm⟩ I
      rw [hs] at hhigh
      change t < s at hhigh
      omega
    | some v =>
      obtain ⟨e, o, he, ho, hep, hop, hsum⟩ := finite_levels_of_tenacity p.last t hpt
      have hopeq : o = p.length := Option.some.inj (ho.symm.trans hpol)
      have hmax' : max e o = p.length := by
        simpa only [maxlevel, he, ho, levelMax, Option.some.injEq] using hmax
      let r := p.appendMatched hpo hm
      have hrlen : r.length = p.length + 1 := rfl
      have hrend : r.last = v := appendMatched_last _ _ _
      have hre : r.length % 2 = 0 := by omega
      have hr : r.Shortest := by
        unfold Shortest
        rw [hre, hrend, hrlen]
        exact (matched_shortest_iff M hm p.length).2
          (by simpa only [Shortest, hpo] using hp)
      have hrt : tenacity M r.last = some t := by
        rw [hrend]
        exact (matched_tenacity M hm).1.symm.trans hpt
      have hve : evenlevel M v = some (p.length + 1) := by
        rw [evenlevel_matched M hm, hpol]
        rfl
      have hvo : ∃ k, oddlevel M v = some k ∧ k + 1 = e := by
        have h := evenlevel_matched M (M.symm hm)
        rw [he] at h
        cases hv : oddlevel M v with
        | none => simp [hv] at h
        | some k => exact ⟨k, rfl, (by simpa only [hv, Option.map_some, Option.some.injEq] using h.symm)⟩
      obtain ⟨k, hvk, hke⟩ := hvo
      have hrmax : maxlevel M r.last = some r.length := by
        rw [hrend, hrlen]
        simp only [maxlevel, hve, hvk, levelMax, Nat.max_eq_left (by omega : k ≤ p.length + 1)]
      let J : Fin (r.length + 1) := ⟨I.val, by have := I.isLt; omega⟩
      have hvertex : r.vertex J = p.vertex I := by
        simp only [r, J, appendMatched, append, dite_eq_left (show I.val ≤ p.length by omega), Fin.eta]
      exact r.even_maxlevel_strict_high_index_below_half hr hre t hrt hrmax J
        (by rw [hvertex]; exact hhigh)

/-- Every high vertex of a maximum-level path has a finite minimum level
strictly below half the endpoint tenacity, including at the augmenting bound. -/
theorem maxlevel_high_vertex_minlevel_lt_half (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length) (I : Fin (p.length + 1))
    (hhigh : levelLE (some t) (tenacity M (p.vertex I))) :
    ∃ k, minlevel M (p.vertex I) = some k ∧ 2 * k < t := by
  by_cases heq : tenacity M (p.vertex I) = some t
  · obtain ⟨e, o, he, ho, _, _, hsum⟩ := finite_levels_of_tenacity (p.vertex I) t heq
    refine ⟨min e o, by simp only [minlevel, he, ho, levelMin], ?_⟩
    have hle := Nat.min_le_left e o
    have hle' := Nat.min_le_right e o
    have hodd := tenacity_odd M p.last t hpt
    omega
  · have hstrict : levelLT (some t) (tenacity M (p.vertex I)) := by
      cases hi : tenacity M (p.vertex I) with
      | none => trivial
      | some s =>
        have hs : t ≤ s := by simpa only [hi, levelLE] using hhigh
        have hne : s ≠ t := by intro h; apply heq; rw [hi, h]
        change t < s
        omega
    exact ⟨I.val, (p.limited_bfs_honesty hp I (by rw [hpt]; exact hhigh)).2
      (by rw [hpt]; exact hstrict),
      p.maxlevel_strict_high_index_below_half hp t hpt hmax I hstrict⟩

end MaximumMatching.AltPath

end SupportMaxHighBound

section SupportBridgeAbsence

namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A shortest path shorter than half a permitted odd threshold contains no
bridge of that threshold. Lower structural facts are discharged internally. -/
theorem short_shortest_no_current_bridge (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (ht : AtMostShortestAugmenting M t) (hodd : t % 2 = 1)
    (hshort : 2 * p.length < t) : p.NoBridgeOfTenacity t := by
  have hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b := by
    intro v s hs hst
    have helig : EligibleTenacity M s := by
      refine ⟨tenacity_odd M v s hs, ⟨v, ?_⟩, ?_⟩
      · rw [hs]; exact Nat.le_refl _
      · intro q hq; have := ht q hq; omega
    obtain ⟨b, hb, _⟩ := general_unique_base M s helig v hs
    exact ⟨b, s, hs, hb⟩
  apply short_shortest_no_bridge t hodd hexists ?_ p hp hshort
  intro b v hv hb q hq hqb hqv k
  obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound (t - 2) b v hv
  have hsodd := tenacity_odd M v s hs
  have helig : EligibleTenacity M (t - 2) := by
    refine ⟨by omega, ⟨v, ?_⟩, ?_⟩
    · rw [hs]; exact hst
    · intro r hr; have := ht r hr; omega
  exact general_blossom_relative_edge_bound M (t - 2) helig b v hv hb q hq hqb hqv k

end MaximumMatching.AltPath

end SupportBridgeAbsence

section SupportBridgeGeometry

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

end SupportBridgeGeometry

section SupportBridgePrefix

/-! The first endpoint of the unique current-tenacity bridge on an actual
maximum-level path has an honest prefix, including when that endpoint lies
inside a lower blossom. This follows the proved terminal/first-entry
decomposition, rather than assuming honesty at low vertices. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

theorem current_bridge_prefix_honest (p : AltPath M) (t : Nat)
    (ht : AtMostShortestAugmenting M t) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length) (I : Fin p.length)
    (hIb : Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩))
    (hIt : edgeTenacity M (p.vertex ⟨I.val, by omega⟩)
      (p.vertex ⟨I.val + 1, by omega⟩) = some t) : p.BFSHonest ⟨I.val, by omega⟩ := by
  have htodd := tenacity_odd M p.last t hpt
  have hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b := by
    intro v s hs hst
    have helig : EligibleTenacity M s := by
      refine ⟨tenacity_odd M v s hs, ⟨v, ?_⟩, ?_⟩
      · rw [hs]; exact Nat.le_refl _
      · intro q hq; have := ht q hq; omega
    obtain ⟨b, hb, _⟩ := general_unique_base M s helig v hs
    exact ⟨b, s, hs, hb⟩
  have hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w := by
    intro b v hv hb q hq hqb hqv
    obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound (t - 2) b v hv
    have hsodd := tenacity_odd M v s hs
    have helig : EligibleTenacity M (t - 2) := by
      refine ⟨by omega, ⟨v, ?_⟩, ?_⟩
      · rw [hs]; exact hst
      · intro r hr; have := ht r hr; omega
    exact general_blossom_relative_confined M (t - 2) helig b v hv hb q hq hqb hqv
  have aux : ∀ L (p : AltPath M), p.length = L → tenacity M p.last = some t →
      maxlevel M p.last = some p.length → ∀ I : Fin p.length,
      Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩) →
      edgeTenacity M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩) = some t →
      p.BFSHonest ⟨I.val, by omega⟩ := by
    intro L
    induction L using Nat.strongRecOn with
    | ind L ih =>
      intro p hpL hpt hmax I hIb hIt
      have hp := p.shortest_of_maxlevel hmax
      have hpos : 0 < p.length := by have := I.isLt; omega
      obtain ⟨Z, _, _, huniq⟩ := p.general_maxlevel_path_unique_bridge t ht hpt hmax
      have unique (J : Fin p.length)
          (hJb : Bridge M (p.vertex ⟨J.val, by omega⟩) (p.vertex ⟨J.val + 1, by omega⟩))
          (hJt : edgeTenacity M (p.vertex ⟨J.val, by omega⟩) (p.vertex ⟨J.val + 1, by omega⟩) = some t) :
          I.val = J.val := congrArg Fin.val ((huniq I hIb hIt).trans (huniq J hJb hJt).symm)
      have recurse (K : Nat) (hK : K < p.length)
          (hKt : tenacity M (p.vertex ⟨K, by omega⟩) = some t)
          (hKm : maxlevel M (p.vertex ⟨K, by omega⟩) = some K) : p.BFSHonest ⟨I.val, by omega⟩ := by
        let r := p.take K (by omega)
        obtain ⟨J, hJb, hJt, _⟩ := r.general_maxlevel_path_unique_bridge t ht hKt hKm
        have hJp : J.val < p.length := by have := J.isLt; change J.val < K at this; omega
        have hIJ := unique ⟨J.val, hJp⟩ hJb hJt
        have hrhon := ih K (by omega) r rfl hKt hKm J hJb hJt
        apply (p.honest_iff_level ⟨I.val, by omega⟩).2
        have hh := (r.honest_iff_level ⟨J.val, by omega⟩).1 hrhon
        change level M (J.val % 2) (p.vertex ⟨J.val, by omega⟩) = some J.val at hh
        simpa only [hIJ] using hh
      let pred : Fin (p.length + 1) := ⟨p.length - 1, by omega⟩
      by_cases hpred : p.BFSHonest pred
      · obtain ⟨hfinal, hcases⟩ := p.honest_terminal_bridge_cases hp t hpt hmax hpos hpred
        have hnext : p.length - 1 + 1 = p.length := by omega
        rcases hcases with ⟨hbridge, _⟩ | ⟨_, hten, hmaxpred⟩
        · have hI := unique ⟨p.length - 1, by omega⟩
            (by simpa only [hnext, last] using hbridge) (by simpa only [hnext, last] using hfinal)
          have hiFin : (⟨I.val, by omega⟩ : Fin (p.length + 1)) = pred := Fin.ext hI
          simpa only [hiFin] using hpred
        · exact recurse (p.length - 1) (by omega) hten hmaxpred
      · obtain ⟨hpo, houter⟩ := p.dishonest_last_predecessor_outer hp t hpt hpos hpred
        have hlow : ∃ s, tenacity M (p.vertex pred) = some s ∧ s < t := by
          by_cases hhigh : levelLE (some t) (tenacity M (p.vertex pred))
          · exact False.elim (hpred (p.limited_bfs_honesty hp pred (by rw [hpt]; exact hhigh)).1)
          · cases hs : tenacity M (p.vertex pred) with
            | none => exact False.elim (hhigh (by rw [hs]; trivial))
            | some s =>
              refine ⟨s, rfl, ?_⟩
              have hn : ¬t ≤ s := by simpa only [hs, levelLE] using hhigh
              omega
        obtain ⟨s, hs, hst⟩ := hlow
        have hsodd := tenacity_odd M (p.vertex pred) s hs
        have hmember := (p.dishonest_outer_predecessor_base hp hpo houter t s hpt hs hst
          (hexists (p.vertex pred) s hs (by omega)) hpred).2
        have hc : levelLT (some (t - 2)) (tenacity M p.last) := by rw [hpt]; change t - 2 < t; omega
        obtain ⟨D, hDo, hDmem, hfirst, htail, _⟩ := p.exists_first_entry_confined_tail hp hpo (t - 2) hc
          (by intro v hv q hq hqf hql; exact hconf p.last v hv hc q hq hqf hql) ⟨pred, hmember⟩
        have hprefix := p.first_entry_prefix_honest hp hpo t hpt hexists hconf D hDo hDmem hfirst htail
        have hentry := p.first_entry_edge_tenacity hp hpo t hpt D hDo hDmem htail hprefix
        have hnext : D.val - 1 + 1 = D.val := by omega
        let r := p.take (D.val - 1) (by have := D.isLt; omega)
        have hrLast : r.last = p.vertex ⟨D.val - 1, by omega⟩ := rfl
        by_cases hprop : PropEdge M r.last (p.vertex D)
        · obtain ⟨hrten, hrmax⟩ := p.first_entry_prop_prefix_maxlevel hp hpo t hpt hconf D hDo hDmem
            hfirst htail hprefix hprop
          exact recurse (D.val - 1) (by have := D.isLt; omega) hrten hrmax
        · have hadj : G.Adj r.last (p.vertex D) := by
            have hh := p.adjacent ⟨D.val - 1, by have := D.isLt; omega⟩
            simpa only [hnext, hrLast, Fin.eta] using hh
          have hI := unique ⟨D.val - 1, by have := D.isLt; omega⟩
            (by simpa only [hnext, hrLast, Fin.eta] using (show Bridge M r.last (p.vertex D) from ⟨hadj, hprop⟩))
            (by simpa only [hnext] using hentry)
          have hiFin : (⟨I.val, by omega⟩ : Fin (p.length + 1)) = ⟨D.val - 1, by omega⟩ := Fin.ext hI
          simpa only [hiFin] using hprefix
  exact aux p.length p rfl hpt hmax I hIb hIt

end MaximumMatching.AltPath

end SupportBridgePrefix

section SupportBridgeRight

/-! The interval after a current-tenacity bridge lies in the lower blossom
of its next high vertex. The actual terminal/first-entry decomposition
identifies that boundary without reversing a crossing-midpoint stretch. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

theorem current_bridge_right_blossom (p : AltPath M) (t : Nat)
    (ht : AtMostShortestAugmenting M t) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length) (I : Fin p.length)
    (hIb : Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩))
    (hIt : edgeTenacity M (p.vertex ⟨I.val, by omega⟩)
      (p.vertex ⟨I.val + 1, by omega⟩) = some t) : ∃ J : Fin (p.length + 1), I.val < J.val ∧ tenacity M (p.vertex J) = some t ∧
        ∀ K : Fin (p.length + 1), I.val < K.val → K.val < J.val →
          Blossom M (t - 2) (p.vertex J) (p.vertex K) := by
  have htodd := tenacity_odd M p.last t hpt
  have hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b := by
    intro v s hs hst
    have helig : EligibleTenacity M s := by
      refine ⟨tenacity_odd M v s hs, ⟨v, ?_⟩, ?_⟩
      · rw [hs]; exact Nat.le_refl _
      · intro q hq; have := ht q hq; omega
    obtain ⟨b, hb, _⟩ := general_unique_base M s helig v hs
    exact ⟨b, s, hs, hb⟩
  have hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w := by
    intro b v hv hb q hq hqb hqv
    obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound (t - 2) b v hv
    have hsodd := tenacity_odd M v s hs
    have helig : EligibleTenacity M (t - 2) := by
      refine ⟨by omega, ⟨v, ?_⟩, ?_⟩
      · rw [hs]; exact hst
      · intro r hr; have := ht r hr; omega
    exact general_blossom_relative_confined M (t - 2) helig b v hv hb q hq hqb hqv
  have aux : ∀ L (p : AltPath M), p.length = L → tenacity M p.last = some t →
      maxlevel M p.last = some p.length → ∀ I : Fin p.length,
      Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩) →
      edgeTenacity M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩) = some t →
      ∃ J : Fin (p.length + 1), I.val < J.val ∧ tenacity M (p.vertex J) = some t ∧
        ∀ K : Fin (p.length + 1), I.val < K.val → K.val < J.val →
          Blossom M (t - 2) (p.vertex J) (p.vertex K) := by
    intro L
    induction L using Nat.strongRecOn with
    | ind L ih =>
      intro p hpL hpt hmax I hIb hIt
      have hp := p.shortest_of_maxlevel hmax
      have hpos : 0 < p.length := by have := I.isLt; omega
      obtain ⟨Z, _, _, huniq⟩ := p.general_maxlevel_path_unique_bridge t ht hpt hmax
      have unique (J : Fin p.length)
          (hJb : Bridge M (p.vertex ⟨J.val, by omega⟩) (p.vertex ⟨J.val + 1, by omega⟩))
          (hJt : edgeTenacity M (p.vertex ⟨J.val, by omega⟩) (p.vertex ⟨J.val + 1, by omega⟩) = some t) :
          I.val = J.val := congrArg Fin.val ((huniq I hIb hIt).trans (huniq J hJb hJt).symm)
      have recurse (K : Nat) (hK : K < p.length)
          (hKt : tenacity M (p.vertex ⟨K, by omega⟩) = some t)
          (hKm : maxlevel M (p.vertex ⟨K, by omega⟩) = some K) : ∃ J : Fin (p.length + 1), I.val < J.val ∧ tenacity M (p.vertex J) = some t ∧
        ∀ K : Fin (p.length + 1), I.val < K.val → K.val < J.val →
          Blossom M (t - 2) (p.vertex J) (p.vertex K) := by
        let r := p.take K (by omega)
        obtain ⟨J, hJb, hJt, _⟩ := r.general_maxlevel_path_unique_bridge t ht hKt hKm
        have hJp : J.val < p.length := by have := J.isLt; change J.val < K at this; omega
        have hIJ := unique ⟨J.val, hJp⟩ hJb hJt
        change I.val = J.val at hIJ
        obtain ⟨Q, hJQ, hQt, hQbl⟩ := ih K (by omega) r rfl hKt hKm J hJb hJt
        have hQbound : Q.val ≤ K := by have := Q.isLt; change Q.val < K + 1 at this; omega
        refine ⟨⟨Q.val, by omega⟩, by change I.val < Q.val; omega, hQt, ?_⟩
        intro A hIA hAQ
        change A.val < Q.val at hAQ
        exact hQbl ⟨A.val, by change A.val < K + 1; omega⟩
          (by change J.val < A.val; omega) hAQ
      let pred : Fin (p.length + 1) := ⟨p.length - 1, by omega⟩
      by_cases hpred : p.BFSHonest pred
      · obtain ⟨hfinal, hcases⟩ := p.honest_terminal_bridge_cases hp t hpt hmax hpos hpred
        have hnext : p.length - 1 + 1 = p.length := by omega
        rcases hcases with ⟨hbridge, _⟩ | ⟨_, hten, hmaxpred⟩
        · have hI := unique ⟨p.length - 1, by omega⟩
            (by simpa only [hnext, last] using hbridge) (by simpa only [hnext, last] using hfinal)
          change I.val = p.length - 1 at hI
          refine ⟨⟨p.length, by omega⟩, by have := I.isLt; omega, hpt, ?_⟩
          intro K hIK hKL
          change K.val < p.length at hKL
          omega
        · exact recurse (p.length - 1) (by omega) hten hmaxpred
      · obtain ⟨hpo, houter⟩ := p.dishonest_last_predecessor_outer hp t hpt hpos hpred
        have hlow : ∃ s, tenacity M (p.vertex pred) = some s ∧ s < t := by
          by_cases hhigh : levelLE (some t) (tenacity M (p.vertex pred))
          · exact False.elim (hpred (p.limited_bfs_honesty hp pred (by rw [hpt]; exact hhigh)).1)
          · cases hs : tenacity M (p.vertex pred) with
            | none => exact False.elim (hhigh (by rw [hs]; trivial))
            | some s =>
              refine ⟨s, rfl, ?_⟩
              have hn : ¬t ≤ s := by simpa only [hs, levelLE] using hhigh
              omega
        obtain ⟨s, hs, hst⟩ := hlow
        have hsodd := tenacity_odd M (p.vertex pred) s hs
        have hmember := (p.dishonest_outer_predecessor_base hp hpo houter t s hpt hs hst
          (hexists (p.vertex pred) s hs (by omega)) hpred).2
        have hc : levelLT (some (t - 2)) (tenacity M p.last) := by rw [hpt]; change t - 2 < t; omega
        obtain ⟨D, hDo, hDmem, hfirst, htail, htailmem⟩ := p.exists_first_entry_confined_tail hp hpo (t - 2) hc
          (by intro v hv q hq hqf hql; exact hconf p.last v hv hc q hq hqf hql) ⟨pred, hmember⟩
        have hprefix := p.first_entry_prefix_honest hp hpo t hpt hexists hconf D hDo hDmem hfirst htail
        have hentry := p.first_entry_edge_tenacity hp hpo t hpt D hDo hDmem htail hprefix
        have hnext : D.val - 1 + 1 = D.val := by omega
        let r := p.take (D.val - 1) (by have := D.isLt; omega)
        have hrLast : r.last = p.vertex ⟨D.val - 1, by omega⟩ := rfl
        by_cases hprop : PropEdge M r.last (p.vertex D)
        · obtain ⟨hrten, hrmax⟩ := p.first_entry_prop_prefix_maxlevel hp hpo t hpt hconf D hDo hDmem
            hfirst htail hprefix hprop
          exact recurse (D.val - 1) (by have := D.isLt; omega) hrten hrmax
        · have hadj : G.Adj r.last (p.vertex D) := by
            have hh := p.adjacent ⟨D.val - 1, by have := D.isLt; omega⟩
            simpa only [hnext, hrLast, Fin.eta] using hh
          have hI := unique ⟨D.val - 1, by have := D.isLt; omega⟩
            (by simpa only [hnext, hrLast, Fin.eta] using (show Bridge M r.last (p.vertex D) from ⟨hadj, hprop⟩))
            (by simpa only [hnext] using hentry)
          change I.val = D.val - 1 at hI
          refine ⟨⟨p.length, by omega⟩, by have := I.isLt; omega, hpt, ?_⟩
          intro K hIK hKL
          change K.val < p.length at hKL
          rcases htailmem K (by omega) with hKeq | hKbl
          · have hh := congrArg Fin.val (p.injective K ⟨p.length, by omega⟩ hKeq)
            dsimp only at hh
            omega
          · exact hKbl
  exact aux p.length p rfl hpt hmax I hIb hIt

/-- The boundary constructed above is precisely any independently selected
first high vertex after the bridge, so the entire initial low stretch has
that actual lower-blossom boundary. -/
theorem current_bridge_first_high_right (p : AltPath M) (t : Nat)
    (ht : AtMostShortestAugmenting M t) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length) (I : Fin p.length)
    (hIb : Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩))
    (hIt : edgeTenacity M (p.vertex ⟨I.val, by omega⟩)
      (p.vertex ⟨I.val + 1, by omega⟩) = some t)
    (J : Fin (p.length + 1)) (hIJ : I.val < J.val)
    (hJ : levelLT (some (t - 2)) (tenacity M (p.vertex J)))
    (hfirst : ∀ K : Fin (p.length + 1), I.val < K.val → K.val < J.val →
      levelLE (tenacity M (p.vertex K)) (some (t - 2))) :
    tenacity M (p.vertex J) = some t ∧
      ∀ K : Fin (p.length + 1), I.val < K.val → K.val < J.val →
        Blossom M (t - 2) (p.vertex J) (p.vertex K) := by
  obtain ⟨L, hIL, hLt, hLbl⟩ := p.current_bridge_right_blossom t ht hpt hmax I hIb hIt
  have htodd := tenacity_odd M p.last t hpt
  have hJL : J.val = L.val := by
    by_cases hlt : J.val < L.val
    · obtain ⟨s, hs, hsc⟩ := blossom_tenacity_bound (t - 2) (p.vertex L) (p.vertex J) (hLbl J hIJ hlt)
      rw [hs] at hJ
      change t - 2 < s at hJ
      omega
    · by_cases hgt : L.val < J.val
      · have hh := hfirst L hIL hgt
        rw [hLt] at hh
        change t ≤ t - 2 at hh
        omega
      · omega
  have heq : J = L := Fin.ext hJL
  rw [heq]
  exact ⟨hLt, hLbl⟩

end MaximumMatching.AltPath

end SupportBridgeRight
