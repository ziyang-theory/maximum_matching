import MaximumMatching.Structure

section Base

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
global common-base theorem is proved separately in GeneralStructureInduction. -/
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

end Base

section MatchedLevels

/-! Exact minlevel decrease in the matched outer-to-inner reduction. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

theorem minlevel_eq_even_of_outer (u : V) (hu : Outer M u) :
    minlevel M u = evenlevel M u := by
  unfold Outer at hu
  unfold minlevel
  cases he : evenlevel M u with
  | none => simp only [he, levelLT] at hu
  | some e =>
    cases ho : oddlevel M u with
    | none => rfl
    | some o =>
      have heo : e < o := by simpa only [he, ho, levelLT] using hu
      exact congrArg some (Nat.min_eq_left (by omega))

/-- The mate of a matched outer vertex has strictly smaller minlevel, even if
the larger parity level is infinite. This justifies the outer case of induction
on minlevel in the minimum-tenacity base proof. -/
theorem matched_outer_minlevel {u v : V} (hm : M.mate u = some v)
    (hu : Outer M u) (k : Nat) (huk : minlevel M u = some k) :
    0 < k ∧ minlevel M v = some (k - 1) := by
  have hue : evenlevel M u = some k := (minlevel_eq_even_of_outer u hu).symm.trans huk
  have hmate := evenlevel_matched M (M.symm hm)
  rw [hue] at hmate
  cases hvo : oddlevel M v with
  | none => simp only [hvo, Option.map_none] at hmate; contradiction
  | some o =>
    have hk : k = o + 1 := by simpa only [hvo, Option.map_some, Option.some.injEq] using hmate
    have hve := evenlevel_matched M hm
    refine ⟨by omega, ?_⟩
    unfold Outer at hu
    rw [hue] at hu
    unfold minlevel
    rw [hve, hvo]
    cases huo : oddlevel M u with
    | none => simp only [Option.map_none, levelMin]; exact congrArg some (by omega)
    | some a =>
      have hka : k < a := by simpa only [huo, levelLT] using hu
      simp only [Option.map_some, levelMin, Nat.min_eq_right (by omega : o ≤ a + 1)]
      exact congrArg some (by omega)

end MaximumMatching

end MatchedLevels

section SameRoot

/-! Same-free-root paths of opposite parity, for Lemma 6.9. -/
namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Strict prefix of p before i avoids the prefix of q through j. -/
def PrefixAvoids (p q : AltPath M) (i : Fin (p.length + 1))
    (j : Fin (q.length + 1)) : Prop :=
  ∀ (a : Fin (p.length + 1)) (b : Fin (q.length + 1)),
    a.val < i.val → b.val ≤ j.val → p.vertex a ≠ q.vertex b

theorem prefix_reverse_disjoint_right (p q : AltPath M)
    (i : Fin (p.length + 1)) (j : Fin (q.length + 1))
    (hd : p.PrefixAvoids q i j) :
    (q.take j.val (by omega)).ReverseDisjoint p 0 i.val := by
  intro a b _ hb he
  have ha : a.val ≤ j.val := by have := a.isLt; change a.val < j.val + 1 at this; omega
  exact hd b ⟨a.val, by omega⟩ hb ha he.symm

theorem prefix_reverse_disjoint_left (p q : AltPath M)
    (i : Fin (p.length + 1)) (j : Fin (q.length + 1))
    (hj : p.vertex i = q.vertex j) (hd : p.PrefixAvoids q i j) :
    (p.take i.val (by omega)).ReverseDisjoint q 0 j.val := by
  intro a b _ hb he
  have ha : a.val ≤ i.val := by have := a.isLt; change a.val < i.val + 1 at this; omega
  change p.vertex ⟨a.val, _⟩ = q.vertex b at he
  by_cases hal : a.val < i.val
  · exact hd ⟨a.val, by omega⟩ b hal (by omega) he
  · have hai : (⟨a.val, by omega⟩ : Fin (p.length + 1)) = i := Fin.ext (by change a.val = i.val; omega)
    rw [hai, hj] at he
    have hbi : j.val = b.val := congrArg Fin.val (q.injective _ _ he)
    omega

/-- If disjoint prefixes meet at opposite parities, reversing one gives a short
augmenting path. Excluding such paths forces equal parity at the meeting point. -/
theorem intersection_parity (p q : AltPath M)
    (i : Fin (p.length + 1)) (j : Fin (q.length + 1))
    (hj : p.vertex i = q.vertex j) (hd : p.PrefixAvoids q i j)
    (t : Nat) (hbound : i.val + j.val ≤ t)
    (hno : ∀ r : AltPath M, r.Augmenting → t < r.length) :
    i.val % 2 = j.val % 2 := by
  by_cases hi : i.val % 2 = 0
  · by_cases hje : j.val % 2 = 0
    · omega
    · have hjo : j.val % 2 = 1 := by omega
      let r := (q.take j.val (by omega)).spliceReverse p 0 i.val (by omega) (by omega)
        hj.symm hjo hi (p.prefix_reverse_disjoint_right q i j hd)
      have hrlen : r.length = j.val + i.val := by rfl
      have hrend : r.last = p.first := by
        simpa only [first] using spliceReverse_last (q.take j.val (by omega)) p 0 i.val
          (by omega) (by omega) hj.symm hjo hi (p.prefix_reverse_disjoint_right q i j hd)
      have hra : r.Augmenting := ⟨by omega, by rw [hrend]; exact p.start_free⟩
      have := hno r hra
      omega
  · have hio : i.val % 2 = 1 := by omega
    by_cases hjo : j.val % 2 = 1
    · omega
    · have hje : j.val % 2 = 0 := by omega
      let r := (p.take i.val (by omega)).spliceReverse q 0 j.val (by omega) (by omega)
        hj hio hje (p.prefix_reverse_disjoint_left q i j hj hd)
      have hrlen : r.length = i.val + j.val := by rfl
      have hrend : r.last = q.first := by
        simpa only [first] using spliceReverse_last (p.take i.val (by omega)) q 0 j.val
          (by omega) (by omega) hj hio hje (p.prefix_reverse_disjoint_left q i j hj hd)
      have hra : r.Augmenting := ⟨by omega, by rw [hrend]; exact q.start_free⟩
      have := hno r hra
      omega

/-- The prefix before the first intersection avoids the other path completely. -/
theorem FirstHit.prefix_avoids {q p : AltPath M} (h : FirstHit q p 0) :
    q.PrefixAvoids p h.qi h.pi := by
  intro a b ha _
  exact h.first a b ha (by omega)

/-- A first hit cannot beat a shortest path's prefix when short augmenting paths
are excluded, even when the two free roots differ. -/
theorem FirstHit.index_le {q p : AltPath M} (h : FirstHit q p 0)
    (hp : p.Shortest) (t : Nat) (hbound : p.length + q.length ≤ t)
    (hno : ∀ r : AltPath M, r.Augmenting → t < r.length) : h.pi.val ≤ h.qi.val := by
  have hpar := q.intersection_parity p h.qi h.pi h.hit h.prefix_avoids t (by omega) hno
  let r := (q.take h.qi.val (by omega)).splice p h.pi.val (by omega)
    h.hit hpar h.forward_disjoint
  have hrlen : r.length = h.qi.val + (p.length - h.pi.val) := rfl
  have hrend : r.last = p.last := splice_last _ _ _ _ _ _ _
  have hrpar : r.length % 2 = p.length % 2 := splice_parity _ _ _ _ _ _ _
  have hle := hp.2 r.length ⟨r, hrend, rfl, hrpar⟩
  omega

/-- Shortest paths meeting at the same endpoint can exchange roots if their total
length is below every augmenting-path length. The constructed path retains the
second path's length/parity and the first path's free root. -/
theorem shortest_root_transfer (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hend : p.last = q.last)
    (hno : ∀ r : AltPath M, r.Augmenting → p.length + q.length < r.length) :
    ∃ r : AltPath M, r.first = p.first ∧ r.last = q.last ∧
      r.length = q.length ∧ r.Shortest := by
  obtain ⟨a⟩ := firstHit_exists q p 0
    ⟨⟨q.length, by omega⟩, ⟨p.length, by omega⟩, by omega, hend.symm⟩
  obtain ⟨b⟩ := firstHit_exists p q 0
    ⟨⟨p.length, by omega⟩, ⟨q.length, by omega⟩, by omega, hend⟩
  have hab : a.qi.val ≤ b.pi.val := by
    by_cases hlt : b.pi.val < a.qi.val
    · exact False.elim (a.first b.pi b.qi hlt (by omega) b.hit.symm)
    · omega
  have hba : b.qi.val ≤ a.pi.val := by
    by_cases hlt : a.pi.val < b.qi.val
    · exact False.elim (b.first a.pi a.qi hlt (by omega) a.hit.symm)
    · omega
  have ha := a.index_le hp (p.length + q.length) (by omega) hno
  have hle : b.qi.val ≤ b.pi.val := by omega
  have hpar := p.intersection_parity q b.qi b.pi b.hit b.prefix_avoids
    (p.length + q.length) (by omega) hno
  let r := (p.take b.qi.val (by omega)).splice q b.pi.val (by omega)
    b.hit hpar b.forward_disjoint
  have hrlen : r.length = b.qi.val + (q.length - b.pi.val) := rfl
  have hrpar : r.length % 2 = q.length % 2 := splice_parity _ _ _ _ _ _ _
  have hrend : r.last = q.last := splice_last _ _ _ _ _ _ _
  have hmin := hq.2 r.length ⟨r, hrend, rfl, hrpar⟩
  have hlength : r.length = q.length := by omega
  refine ⟨r, ?_, hrend, hlength, ?_⟩
  · simp only [r, first, splice, take, Nat.zero_le, dite_true]
  · unfold Shortest
    rw [hlength, hrend]
    exact hq

/-- Opposite-parity shortest paths account exactly for the endpoint tenacity. -/
theorem opposite_shortest_tenacity (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hend : p.last = q.last) (hp0 : p.length % 2 = 0) (hq1 : q.length % 2 = 1) :
    tenacity M p.last = some (p.length + q.length) := by
  have he : evenlevel M p.last = some p.length :=
    (level_eq_some_iff M 0 p.last p.length).2 (by simpa only [Shortest, hp0] using hp)
  have ho : oddlevel M p.last = some q.length :=
    (level_eq_some_iff M 1 p.last q.length).2 (by simpa only [Shortest, hq1, hend] using hq)
  simp only [tenacity, he, ho, levelAdd]

end AltPath

variable {V : Type} {G : Graph V}

/-- A globally shortest parity path from the specified free root. -/
def RootedShortest (M : Matching G) (parity : Nat) (f v : V) : Prop :=
  ∃ p : AltPath M, p.first = f ∧ p.last = v ∧ p.Shortest ∧ p.length % 2 = parity

/-- Lemma 6.9: for an eligible-tenacity vertex, each free root supplies shortest
paths of both parities or of neither parity. -/
theorem rooted_shortest_even_iff_odd (M : Matching G) (t : Nat)
    (ht : EligibleTenacity M t) (v : V) (hvt : tenacity M v = some t) (f : V) :
    RootedShortest M 0 f v ↔ RootedShortest M 1 f v := by
  have hlevels : ∃ e o, evenlevel M v = some e ∧ oddlevel M v = some o ∧ e + o = t := by
    unfold tenacity at hvt
    cases he : evenlevel M v with
    | none => simp [he, levelAdd] at hvt
    | some e =>
      cases ho : oddlevel M v with
      | none => simp [he, ho, levelAdd] at hvt
      | some o =>
        have hsum : e + o = t := by simpa [he, ho, levelAdd] using hvt
        exact ⟨e, o, rfl, rfl, hsum⟩
  obtain ⟨e, o, he, ho, hsum⟩ := hlevels
  have hes := (level_eq_some_iff M 0 v e).1 he
  have hos := (level_eq_some_iff M 1 v o).1 ho
  constructor
  · rintro ⟨p, hpf, hpv, hp, hp0⟩
    obtain ⟨q, hqv, hql, hq1⟩ := hos.1
    have hq : q.Shortest := by simpa only [AltPath.Shortest, hql, hqv, hq1] using hos
    have htlen := p.opposite_shortest_tenacity q hp hq (hpv.trans hqv.symm) hp0 (by omega)
    have hsum' : p.length + q.length = t := by rw [hpv, hvt] at htlen; exact (Option.some.inj htlen).symm
    obtain ⟨r, hrf, hrv, hrl, hrs⟩ := p.shortest_root_transfer q hp hq
      (hpv.trans hqv.symm) (by intro r hr; rw [hsum']; exact ht.2.2 r hr)
    exact ⟨r, hrf.trans hpf, hrv.trans hqv, hrs, by omega⟩
  · rintro ⟨p, hpf, hpv, hp, hp1⟩
    obtain ⟨q, hqv, hql, hq0⟩ := hes.1
    have hq : q.Shortest := by simpa only [AltPath.Shortest, hql, hqv, hq0] using hes
    have htlen := q.opposite_shortest_tenacity p hq hp (hqv.trans hpv.symm) (by omega) hp1
    have hsum' : p.length + q.length = t := by
      rw [hqv, hvt] at htlen
      have := Option.some.inj htlen
      omega
    obtain ⟨r, hrf, hrv, hrl, hrs⟩ := p.shortest_root_transfer q hp hq
      (hpv.trans hqv.symm) (by intro r hr; rw [hsum']; exact ht.2.2 r hr)
    exact ⟨r, hrf.trans hpf, hrv.trans hqv, hrs, by omega⟩
end MaximumMatching

end SameRoot

section MinTenacityGeometry

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

end MinTenacityGeometry
