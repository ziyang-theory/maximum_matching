import MaximumMatching.LimitedHonesty

/-! Checked consequences toward Claim 6.4 and Lemma 6.13.
These results do not assert existence of a path-independent base. -/
namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A last vertex above the endpoint tenacity has even index: an odd occurrence
would have a matched successor of the same tenacity. -/
theorem baseOnPath_even (p : AltPath M) (t : Nat) {b : V}
    (hv : tenacity M p.last = some t) (hb : p.BaseOnPath t b) :
    ∃ i : Fin (p.length + 1), p.vertex i = b ∧ i.val % 2 = 0 := by
  obtain ⟨i, hi, hhigh, hlast⟩ := hb
  refine ⟨i, hi, ?_⟩
  by_cases he : i.val % 2 = 0
  · exact he
  · have ho : i.val % 2 = 1 := by omega
    have hilast : i.val < p.length := by
      by_cases hlt : i.val < p.length
      · exact hlt
      · have hie : i = ⟨p.length, by omega⟩ := Fin.ext (by change i.val = p.length; omega)
        have hbe : b = p.last := by rw [← hi, hie]; rfl
        rw [hbe, hv] at hhigh
        change t < t at hhigh
        omega
    let j : Fin (p.length + 1) := ⟨i.val + 1, by omega⟩
    have hm : M.mate (p.vertex i) = some (p.vertex j) := p.mate_next i.val hilast ho
    have hten := (matched_tenacity M hm).1
    have hjhigh : levelLT (some t) (tenacity M (p.vertex j)) := by
      rw [← hten, hi]
      exact hhigh
    exact False.elim (hlast j (by change i.val < i.val + 1; omega) hjhigh)

/-- Definition 6.2's path-relative base is an outer vertex. This uses the proved
strict-tenacity part of Theorem 5.3, without assuming uniqueness across paths. -/
theorem baseOnPath_outer (p : AltPath M) (hp : p.Shortest) (t : Nat) {b : V}
    (hv : tenacity M p.last = some t) (hb : p.BaseOnPath t b) : Outer M b := by
  obtain ⟨i, hi, hie⟩ := p.baseOnPath_even t hv hb
  have hhigh : levelLT (tenacity M p.last) (tenacity M (p.vertex i)) := by
    rw [hv, hi]
    exact hb.choose_spec.2.1
  obtain ⟨hhon, hmin⟩ := p.limited_bfs_honesty hp i (levelLT_le hhigh)
  have he : evenlevel M b = some i.val := by
    have hh := (p.honest_iff_level i).1 hhon
    simpa only [hie, hi] using hh
  have hm : minlevel M b = some i.val := by simpa only [hi] using hmin hhigh
  unfold Outer
  rw [he]
  cases ho : oddlevel M b with
  | none => trivial
  | some k =>
    have hmin' : min i.val k = i.val := by
      simpa only [minlevel, he, ho, levelMin, Option.some.injEq] using hm
    have hkpar := level_parity M 1 b k ho
    change i.val < k
    omega

/-- At globally minimum finite tenacity, every shortest-path prefix is honest.
This is the precise premise used to build the layered graph in Lemma 6.13. -/
theorem prefixes_honest_at_minimum (p : AltPath M) (hp : p.Shortest) (t : Nat)
    (hv : tenacity M p.last = some t)
    (hmin : ∀ v : V, levelLE (some t) (tenacity M v)) :
    ∀ i : Fin (p.length + 1), p.BFSHonest i := by
  intro i
  exact (p.limited_bfs_honesty hp i (by rw [hv]; exact hmin _)).1

/-- Removing a suffix whose vertices are not above the threshold preserves the
path-relative base. The two paths share an initial segment, not a proof of uniqueness. -/
theorem baseOnPath_initial_iff (p q : AltPath M) (hpq : p.length ≤ q.length)
    (hvertices : ∀ i : Fin (p.length + 1), p.vertex i = q.vertex ⟨i.val, by omega⟩)
    (t : Nat) (htail : ∀ j : Fin (q.length + 1), p.length < j.val →
      ¬levelLT (some t) (tenacity M (q.vertex j))) (b : V) :
    p.BaseOnPath t b ↔ q.BaseOnPath t b := by
  constructor
  · rintro ⟨i, hi, hh, hlast⟩
    refine ⟨⟨i.val, by omega⟩, (hvertices i).symm.trans hi, hh, ?_⟩
    intro j hij hjhigh
    by_cases hj : j.val ≤ p.length
    · have he := hvertices ⟨j.val, by omega⟩
      have hh' : levelLT (some t) (tenacity M (p.vertex ⟨j.val, by omega⟩)) := by
        rw [he]
        exact hjhigh
      exact hlast ⟨j.val, by omega⟩ (by change i.val < j.val; exact hij) hh'
    · exact htail j (by omega) hjhigh
  · rintro ⟨i, hi, hh, hlast⟩
    have hip : i.val ≤ p.length := by
      by_cases hip : i.val ≤ p.length
      · exact hip
      · have hh' : levelLT (some t) (tenacity M (q.vertex i)) := by rw [hi]; exact hh
        exact False.elim (htail i (by omega) hh')
    refine ⟨⟨i.val, by omega⟩, (hvertices ⟨i.val, by omega⟩).trans hi, hh, ?_⟩
    intro j hij hjhigh
    have he := hvertices j
    have hh' : levelLT (some t) (tenacity M (q.vertex ⟨j.val, by omega⟩)) := by
      rw [← he]
      exact hjhigh
    exact hlast ⟨j.val, by omega⟩ (by change i.val < j.val; exact hij) hh'

/-- Adding a matched endpoint of the same tenacity leaves all path-relative bases
unchanged. This is one direction of Lemma 6.12's correspondence. -/
theorem baseOnPath_appendMatched_iff (p : AltPath M) (hodd : p.length % 2 = 1)
    {v : V} (hm : M.mate p.last = some v) (t : Nat)
    (hvt : tenacity M v = some t) (b : V) :
    p.BaseOnPath t b ↔ (p.appendMatched hodd hm).BaseOnPath t b := by
  apply p.baseOnPath_initial_iff (p.appendMatched hodd hm) (by simp)
  · intro i
    change p.vertex i = (if h : i.val ≤ p.length then p.vertex ⟨i.val, _⟩ else v)
    simp only [dite_eq_left (show i.val ≤ p.length by omega)]
  · intro j hj
    have hjv : (p.appendMatched hodd hm).vertex j = v := by
      change (if h : j.val ≤ p.length then p.vertex ⟨j.val, _⟩ else v) = v
      simp only [dite_eq_right (show ¬ j.val ≤ p.length by omega)]
    rw [hjv, hvt]
    change ¬t < t
    omega

/-- Truncating a terminal vertex of threshold tenacity leaves all bases unchanged. -/
theorem baseOnPath_take_pred_iff (p : AltPath M) (hpos : 0 < p.length)
    (t : Nat) (hvt : tenacity M p.last = some t) (b : V) :
    (p.take (p.length - 1) (by omega)).BaseOnPath t b ↔ p.BaseOnPath t b := by
  apply (p.take (p.length - 1) (by omega)).baseOnPath_initial_iff p (by simp)
  · intro i
    rfl
  · intro j hj
    have hv : j.val = p.length := by change p.length - 1 < j.val at hj; omega
    have hj' : j = ⟨p.length, by omega⟩ := Fin.ext hv
    rw [hj']
    change ¬levelLT (some t) (tenacity M p.last)
    rw [hvt]
    change ¬t < t
    omega

/-- A shortest path to one endpoint of a matched edge transfers to a shortest
path to the other endpoint, preserving every path-relative base at their tenacity. -/
theorem matched_shortest_path_transfer (M : Matching G) {u v : V}
    (hm : M.mate u = some v) (t : Nat) (hut : tenacity M u = some t)
    (p : AltPath M) (hpend : p.last = u) (hp : p.Shortest) :
    ∃ q : AltPath M, q.last = v ∧ q.Shortest ∧
      ∀ b : V, p.BaseOnPath t b ↔ q.BaseOnPath t b := by
  have hvt : tenacity M v = some t := (matched_tenacity M hm).1.symm.trans hut
  have hpm : M.mate p.last = some v := by rw [hpend]; exact hm
  by_cases heven : p.length % 2 = 0
  · have hpos := p.even_matched_pos hpm
    let q := p.take (p.length - 1) (by omega)
    have hqlen : q.length = p.length - 1 := rfl
    have hqend : q.last = v := by
      have hlast := p.even_last_mate heven hpos
      exact M.mate_unique hlast hpm
    have hqodd : q.length % 2 = 1 := by omega
    have hqshort : q.Shortest := by
      unfold Shortest
      rw [hqodd, hqend, hqlen]
      apply (matched_shortest_iff M (M.symm hm) (p.length - 1)).1
      have he : p.length - 1 + 1 = p.length := by omega
      rw [he]
      simpa only [Shortest, heven, hpend] using hp
    refine ⟨q, hqend, hqshort, ?_⟩
    intro b
    exact (p.baseOnPath_take_pred_iff hpos t (by rw [hpend]; exact hut) b).symm
  · have hodd : p.length % 2 = 1 := by omega
    let q := p.appendMatched hodd hpm
    have hqlen : q.length = p.length + 1 := rfl
    have hqend : q.last = v := appendMatched_last _ _ _
    have hqeven : q.length % 2 = 0 := by omega
    have hqshort : q.Shortest := by
      unfold Shortest
      rw [hqeven, hqend, hqlen]
      apply (matched_shortest_iff M hm p.length).2
      simpa only [Shortest, hodd, hpend] using hp
    exact ⟨q, hqend, hqshort, p.baseOnPath_appendMatched_iff hodd hpm t hvt⟩

end AltPath

variable {V : Type} {G : Graph V}

/-- The equality of base-value sets across a matched edge, the `B(u)=B(v)`
component of Lemma 6.12. This does not assert either set is a singleton. -/
theorem matched_base_values_iff (M : Matching G) {u v : V}
    (hm : M.mate u = some v) (t : Nat) (hut : tenacity M u = some t) (b : V) :
    (∃ p : AltPath M, p.last = u ∧ p.Shortest ∧ p.BaseOnPath t b) ↔
    (∃ q : AltPath M, q.last = v ∧ q.Shortest ∧ q.BaseOnPath t b) := by
  constructor
  · rintro ⟨p, hpend, hp, hb⟩
    obtain ⟨q, hqend, hq, hbase⟩ := AltPath.matched_shortest_path_transfer M hm t hut p hpend hp
    exact ⟨q, hqend, hq, (hbase b).1 hb⟩
  · rintro ⟨q, hqend, hq, hb⟩
    have hvt : tenacity M v = some t := (matched_tenacity M hm).1.symm.trans hut
    obtain ⟨p, hpend, hp, hbase⟩ := AltPath.matched_shortest_path_transfer M (M.symm hm) t hvt q hqend hq
    exact ⟨p, hpend, hp, (hbase b).1 hb⟩

/-- The common-base predicate transfers across a matched edge. -/
theorem matched_common_base_iff (M : Matching G) {u v : V}
    (hm : M.mate u = some v) (t : Nat) (hut : tenacity M u = some t) (b : V) :
    (∀ p : AltPath M, p.last = u → p.Shortest → p.BaseOnPath t b) ↔
    (∀ q : AltPath M, q.last = v → q.Shortest → q.BaseOnPath t b) := by
  constructor
  · intro hu q hqend hq
    have hvt : tenacity M v = some t := (matched_tenacity M hm).1.symm.trans hut
    obtain ⟨p, hpend, hp, hbase⟩ := AltPath.matched_shortest_path_transfer M (M.symm hm) t hvt q hqend hq
    exact (hbase b).2 (hu p hpend hp)
  · intro hv p hpend hp
    obtain ⟨q, hqend, hq, hbase⟩ := AltPath.matched_shortest_path_transfer M hm t hut p hpend hp
    exact (hbase b).2 (hv q hqend hq)

/-- A verified reduction of base uniqueness between matched endpoints. The
nontrivial global assertion that either endpoint has a unique base remains open. -/
theorem matched_unique_base_iff (M : Matching G) {u v : V}
    (hm : M.mate u = some v) (t : Nat) (hut : tenacity M u = some t) :
    HasUniqueBase M u t ↔ HasUniqueBase M v t := by
  constructor
  · rintro ⟨b, hb, huniq⟩
    refine ⟨b, (matched_common_base_iff M hm t hut b).1 hb, ?_⟩
    intro c hc
    exact huniq c ((matched_common_base_iff M hm t hut c).2 hc)
  · rintro ⟨b, hb, huniq⟩
    refine ⟨b, (matched_common_base_iff M hm t hut b).2 hb, ?_⟩
    intro c hc
    exact huniq c ((matched_common_base_iff M hm t hut c).1 hc)

/-- Eligible-tenacity vertices are matched, since a free vertex has tenacity
strictly above every eligible threshold. -/
theorem eligible_vertex_matched (M : Matching G) (t : Nat) (ht : EligibleTenacity M t)
    (v : V) (hvt : tenacity M v = some t) : ∃ u, M.mate v = some u := by
  cases hm : M.mate v with
  | none =>
    have hh := free_tenacity_above M t v hm ht.2.2
    rw [hvt] at hh
    change t < t at hh
    omega
  | some u => exact ⟨u, rfl⟩

/-- An outer vertex's matched neighbor is inner (the reduction used in Lemma 6.13,
Claim 1). The reverse implication is not asserted. -/
theorem matched_outer_inner (M : Matching G) {u v : V} (hm : M.mate u = some v)
    (hu : Outer M u) : Inner M v := by
  have hue := evenlevel_matched M (M.symm hm)
  have hve := evenlevel_matched M hm
  unfold Outer at hu
  rw [hue] at hu
  cases hvo : oddlevel M v with
  | none => simp only [hvo, Option.map_none, levelLT] at hu
  | some b =>
    cases huo : oddlevel M u with
    | none =>
      refine ⟨⟨b, ?_⟩, ?_⟩
      · simp only [minlevel, hve, huo, Option.map_none, hvo, levelMin]
      · simp only [Outer, hve, huo, Option.map_none, hvo, levelLT, not_false_eq_true]
    | some a =>
      have hba : b + 1 < a := by simpa only [hvo, huo, Option.map_some, levelLT] using hu
      refine ⟨⟨b, ?_⟩, ?_⟩
      · simp only [minlevel, hve, huo, Option.map_some, hvo, levelMin]
        exact congrArg some (Nat.min_eq_right (by omega))
      · simp only [Outer, hve, huo, Option.map_some, hvo, levelLT]
        omega

end MaximumMatching
