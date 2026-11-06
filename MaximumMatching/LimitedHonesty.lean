import MaximumMatching.Splice
import MaximumMatching.Structure

namespace MaximumMatching

theorem levelLT_le {a b : Option Nat} (h : levelLT a b) : levelLE a b := by
  cases a <;> cases b <;> simp only [levelLT, levelLE] at h ⊢
  omega

namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A first hit strictly beyond a replacement path's target still permits reversal
all the way to that target: the target occurs only at the replacement path's end. -/
theorem FirstHit.reverse_disjoint_to_target {q p : AltPath M} {k : Nat}
    (h : FirstHit q p (k + 1)) (hk : k ≤ p.length)
    (hend : q.last = p.vertex ⟨k, by omega⟩) :
    (q.take h.qi.val (by omega)).ReverseDisjoint p k h.pi.val := by
  have hqi : h.qi.val < q.length := by
    by_cases hlt : h.qi.val < q.length
    · exact hlt
    · have he : h.qi = ⟨q.length, by omega⟩ := Fin.ext (by change h.qi.val = q.length; omega)
      have hh : p.vertex ⟨k, by omega⟩ = p.vertex h.pi := by
        have hhit := h.hit
        rw [he] at hhit
        exact hend.symm.trans hhit
      have hh' := p.injective _ _ hh
      have hv : k = h.pi.val := congrArg (fun x : Fin (p.length + 1) => x.val) hh'
      have := h.in_suffix
      omega
  intro a b hb hb' he
  have habound : a.val ≤ h.qi.val := by
    have ha := a.isLt
    change a.val < h.qi.val + 1 at ha
    omega
  change q.vertex ⟨a.val, _⟩ = p.vertex b at he
  by_cases hkb : k < b.val
  · exact h.reverse_disjoint (k + 1) (by omega) a b (by omega) hb' he
  · have hbk : b = ⟨k, by omega⟩ := Fin.ext (by change b.val = k; omega)
    rw [hbk, ← hend] at he
    have hh := q.injective ⟨a.val, by omega⟩ ⟨q.length, by omega⟩ he
    have hv : a.val = q.length := congrArg (fun x : Fin (q.length + 1) => x.val) hh
    omega

/-- Core first-intersection argument from Theorem 5.3: if an even vertex on a
shortest even path has a shorter even path, it has an odd path shorter than the
original path. This does not assume BFS-honesty of intermediate vertices. -/
theorem shorter_even_prefix_opposite (p : AltPath M) (hp : p.Shortest)
    (heven : p.length % 2 = 0) (k : Nat) (hk : k ≤ p.length) (hke : k % 2 = 0)
    (q : AltPath M) (hend : q.last = p.vertex ⟨k, by omega⟩)
    (hqe : q.length % 2 = 0) (hlt : q.length < k) :
    ∃ l, HasPathLength M 1 (p.vertex ⟨k, by omega⟩) l ∧ l < p.length := by
  have hinter := p.shorter_prefix_intersects hp k hk q hend (by omega) hlt
  have hh : Nonempty (FirstHit q p (k + 1)) := firstHit_exists q p (k + 1) (by
    obtain ⟨a, b, hb, hab⟩ := hinter
    exact ⟨a, b, by omega, hab⟩)
  obtain ⟨h⟩ := hh
  have hqo := h.odd heven (by omega)
  have hj : h.pi.val % 2 = 0 := by
    by_cases hje : h.pi.val % 2 = 0
    · exact hje
    · have hjo : h.pi.val % 2 = 1 := by omega
      have hjoin : (q.take h.qi.val (by omega)).last = p.vertex h.pi := h.hit
      have hpar : (q.take h.qi.val (by omega)).length % 2 = h.pi.val % 2 := by
        simp only [take_length, hqo, hjo]
      have hbound := p.no_shorter_disjoint_prefix hp h.pi.val (by omega)
        (q.take h.qi.val (by omega)) hjoin hpar h.forward_disjoint
      change h.pi.val ≤ h.qi.val at hbound
      have := h.in_suffix
      omega
  have hjoin : (q.take h.qi.val (by omega)).last = p.vertex h.pi := h.hit
  have hkj : k ≤ h.pi.val := by have := h.in_suffix; omega
  have hdisj := h.reverse_disjoint_to_target hk hend
  let r := (q.take h.qi.val (by omega)).spliceReverse p k h.pi.val hkj
    (by omega) hjoin hqo hj hdisj
  have hrlen : r.length = h.qi.val + (h.pi.val - k) := rfl
  have hrend : r.last = p.vertex ⟨k, by omega⟩ := spliceReverse_last _ _ _ _ _ _ _ _ _ _
  refine ⟨r.length, ⟨r, hrend, rfl, by rw [hrlen]; omega⟩, ?_⟩
  rw [hrlen]
  omega

/-- Comparison with an odd path to the terminal vertex. The first-intersection
case split yields either a bounded odd path to the interior vertex or a lower
bound on the odd terminal path's length. -/
theorem odd_terminal_comparison (p : AltPath M) (hp : p.Shortest)
    (heven : p.length % 2 = 0) (k : Nat) (hk : k ≤ p.length)
    (hkpos : 0 < k) (hke : k % 2 = 0)
    (r : AltPath M) (hrend : r.last = p.last) :
    (∃ l, HasPathLength M 1 (p.vertex ⟨k, by omega⟩) l ∧
      l ≤ r.length + (p.length - k)) ∨ k - 1 ≤ r.length := by
  have hh : Nonempty (FirstHit r p (k - 1)) := firstHit_exists r p (k - 1)
    ⟨⟨r.length, by omega⟩, ⟨p.length, by omega⟩, by change k - 1 ≤ p.length; omega, hrend⟩
  obtain ⟨h⟩ := hh
  have hqo := h.odd heven (by omega)
  have hjoin : (r.take h.qi.val (by omega)).last = p.vertex h.pi := h.hit
  by_cases hje : h.pi.val % 2 = 0
  · have hkj : k ≤ h.pi.val := by have := h.in_suffix; omega
    have hd := h.reverse_disjoint k (by omega)
    let z := (r.take h.qi.val (by omega)).spliceReverse p k h.pi.val hkj
      (by omega) hjoin hqo hje hd
    have hzlen : z.length = h.qi.val + (h.pi.val - k) := rfl
    have hzend : z.last = p.vertex ⟨k, by omega⟩ := spliceReverse_last _ _ _ _ _ _ _ _ _ _
    left
    refine ⟨z.length, ⟨z, hzend, rfl, by rw [hzlen]; omega⟩, ?_⟩
    rw [hzlen]
    omega
  · have hjo : h.pi.val % 2 = 1 := by omega
    have hpar : (r.take h.qi.val (by omega)).length % 2 = h.pi.val % 2 := by
      simp only [take_length, hqo, hjo]
    have hb := p.no_shorter_disjoint_prefix hp h.pi.val (by omega)
      (r.take h.qi.val (by omega)) hjoin hpar h.forward_disjoint
    change h.pi.val ≤ h.qi.val at hb
    right
    have := h.in_suffix
    omega

private theorem level_bound_of_witness (parity : Nat) (v : V) (l : Nat)
    (hl : HasPathLength M parity v l) :
    ∃ k, level M parity v = some k ∧ k ≤ l := by
  cases he : level M parity v with
  | none => exact False.elim ((level_eq_none_iff M parity v).1 he ⟨l, hl⟩)
  | some k => exact ⟨k, rfl, ((level_eq_some_iff M parity v k).1 he).2 l hl⟩

/-- The even-terminal/even-interior core of Theorem 5.3, with infinite levels
included. The order premise uses infinity as the greatest element. -/
theorem even_vertex_honest (p : AltPath M) (hp : p.Shortest)
    (heven : p.length % 2 = 0) (k : Nat) (hk : k ≤ p.length) (hke : k % 2 = 0)
    (ht : levelLE (tenacity M p.last) (tenacity M (p.vertex ⟨k, by omega⟩))) :
    p.BFSHonest ⟨k, by omega⟩ := by
  obtain ⟨a, hae, hak⟩ := p.prefix_level_bound ⟨k, by omega⟩
  change level M (k % 2) (p.vertex ⟨k, by omega⟩) = some a at hae
  rw [hke] at hae
  change a ≤ k at hak
  have hve : evenlevel M p.last = some p.length :=
    (level_eq_some_iff M 0 p.last p.length).2 (by simpa only [Shortest, heven] using hp)
  apply (p.honest_iff_level ⟨k, by omega⟩).2
  change level M (k % 2) (p.vertex ⟨k, by omega⟩) = some k
  rw [hke]
  by_cases heq : a = k
  · exact heq ▸ hae
  · have hlt : a < k := by omega
    obtain ⟨q, hqend, hqlen, hqpar⟩ := ((level_eq_some_iff M 0 _ a).1 hae).1
    have hqe : q.length % 2 = 0 := by omega
    obtain ⟨l, hl, hlL⟩ := p.shorter_even_prefix_opposite hp heven k hk hke q hqend hqe (by omega)
    obtain ⟨b, hbo, hbl⟩ := level_bound_of_witness 1 _ l hl
    have htb : tenacity M (p.vertex ⟨k, by omega⟩) = some (a + b) := by
      simp only [tenacity, evenlevel, oddlevel, hae, hbo, levelAdd]
    rw [htb] at ht
    cases hvo : oddlevel M p.last with
    | none =>
      simp only [tenacity, hve, hvo, levelAdd, levelLE] at ht
    | some s =>
      have hsum : p.length + s ≤ a + b := by
        simpa only [tenacity, hve, hvo, levelAdd, levelLE] using ht
      obtain ⟨r, hrend, hrlen, _⟩ := ((level_eq_some_iff M 1 p.last s).1 hvo).1
      rcases p.odd_terminal_comparison hp heven k hk (by omega) hke r hrend with hb | hs
      · obtain ⟨c, hc, hcl⟩ := hb
        have hbc := ((level_eq_some_iff M 1 _ b).1 hbo).2 c hc
        omega
      · omega

/-- The strict-tenacity conclusion of Theorem 5.3 for even paths and even indices. -/
theorem even_vertex_minlevel (p : AltPath M) (hp : p.Shortest)
    (heven : p.length % 2 = 0) (k : Nat) (hk : k ≤ p.length) (hke : k % 2 = 0)
    (ht : levelLT (tenacity M p.last) (tenacity M (p.vertex ⟨k, by omega⟩))) :
    minlevel M (p.vertex ⟨k, by omega⟩) = some k := by
  have hhon := p.even_vertex_honest hp heven k hk hke (levelLT_le ht)
  have hue : evenlevel M (p.vertex ⟨k, by omega⟩) = some k := by
    have hh := (p.honest_iff_level ⟨k, by omega⟩).1 hhon
    simpa only [hke] using hh
  have hve : evenlevel M p.last = some p.length :=
    (level_eq_some_iff M 0 p.last p.length).2 (by simpa only [Shortest, heven] using hp)
  unfold minlevel
  rw [hue]
  cases huo : oddlevel M (p.vertex ⟨k, by omega⟩) with
  | none => rfl
  | some b =>
    change some (min k b) = some k
    by_cases hkb : k ≤ b
    · exact congrArg some (Nat.min_eq_left hkb)
    · have hblt : b < k := by omega
      cases hvo : oddlevel M p.last with
      | none =>
        simp only [tenacity, hue, huo, hve, hvo, levelAdd, levelLT] at ht
      | some s =>
        have hsum : p.length + s < k + b := by
          simpa only [tenacity, hue, huo, hve, hvo, levelAdd, levelLT] using ht
        obtain ⟨r, hrend, hrlen, _⟩ := ((level_eq_some_iff M 1 p.last s).1 hvo).1
        rcases p.odd_terminal_comparison hp heven k hk (by omega) hke r hrend with hb | hs
        · obtain ⟨c, hc, hcl⟩ := hb
          have hbc := ((level_eq_some_iff M 1 _ b).1 huo).2 c hc
          omega
        · omega

/-- Limited BFS-honesty for even-terminal paths, at both parities of interior vertex. -/
theorem limited_honesty_even (p : AltPath M) (hp : p.Shortest)
    (heven : p.length % 2 = 0) (i : Fin (p.length + 1))
    (ht : levelLE (tenacity M p.last) (tenacity M (p.vertex i))) :
    p.BFSHonest i ∧
      (levelLT (tenacity M p.last) (tenacity M (p.vertex i)) →
        minlevel M (p.vertex i) = some i.val) := by
  by_cases hie : i.val % 2 = 0
  · exact ⟨p.even_vertex_honest hp heven i.val (by omega) hie ht,
      p.even_vertex_minlevel hp heven i.val (by omega) hie⟩
  · have hio : i.val % 2 = 1 := by omega
    let j : Fin (p.length + 1) := ⟨i.val + 1, by omega⟩
    have hje : j.val % 2 = 0 := by change (i.val + 1) % 2 = 0; omega
    have hm : M.mate (p.vertex i) = some (p.vertex j) := p.mate_next i.val (by omega) hio
    have hten := (matched_tenacity M hm).1
    have htj : levelLE (tenacity M p.last) (tenacity M (p.vertex j)) := by rwa [← hten]
    have hhon := p.even_vertex_honest hp heven j.val (by omega) hje htj
    have hjelevel : evenlevel M (p.vertex j) = some j.val := by
      have hh := (p.honest_iff_level j).1 hhon
      simpa only [hje] using hh
    have hueq := evenlevel_matched M hm
    have huolevel : oddlevel M (p.vertex i) = some i.val := by
      rw [hjelevel] at hueq
      cases huo : oddlevel M (p.vertex i) with
      | none => simp [huo] at hueq
      | some a =>
        have he : j.val = a + 1 := by simpa only [huo, Option.map_some, Option.some.injEq] using hueq
        have hv : a = i.val := by change i.val + 1 = a + 1 at he; omega
        exact congrArg some hv
    refine ⟨?_, ?_⟩
    · apply (p.honest_iff_level i).2
      simpa only [hio] using huolevel
    · intro hstrict
      have hstrictj : levelLT (tenacity M p.last) (tenacity M (p.vertex j)) := by rwa [← hten]
      have hminj := p.even_vertex_minlevel hp heven j.val (by omega) hje hstrictj
      have hue := evenlevel_matched M (M.symm hm)
      unfold minlevel
      rw [huolevel, hue]
      cases hjo : oddlevel M (p.vertex j) with
      | none => rfl
      | some b =>
        have hmin : min j.val b = j.val := by
          simpa only [minlevel, hjelevel, hjo, levelMin, Option.some.injEq] using hminj
        have hbj : j.val ≤ b := by omega
        change some (min (b + 1) i.val) = some i.val
        exact congrArg some (Nat.min_eq_right (by change i.val + 1 ≤ b at hbj; omega))

/-- Theorem 5.3 of the supplied paper: limited BFS-honesty. The formal statement
includes both endpoint parities, free endpoints, and infinite levels. The strict
comparison gives the paper's additional minlevel conclusion. -/
theorem limited_bfs_honesty (p : AltPath M) (hp : p.Shortest)
    (i : Fin (p.length + 1))
    (ht : levelLE (tenacity M p.last) (tenacity M (p.vertex i))) :
    p.BFSHonest i ∧
      (levelLT (tenacity M p.last) (tenacity M (p.vertex i)) →
        minlevel M (p.vertex i) = some i.val) := by
  by_cases heven : p.length % 2 = 0
  · exact p.limited_honesty_even hp heven i ht
  · have hodd : p.length % 2 = 1 := by omega
    cases hm : M.mate p.last with
    | none =>
      have ha : p.Augmenting := ⟨hodd, hm⟩
      have hve : evenlevel M p.last = some 0 := (evenlevel_zero_iff_free M p.last).2 hm
      have hvo : oddlevel M p.last = some p.length :=
        (level_eq_some_iff M 1 p.last p.length).2 (by simpa only [Shortest, hodd] using hp)
      have hvt : tenacity M p.last = some p.length := by
        simp only [tenacity, hve, hvo, levelAdd, Nat.zero_add]
      obtain ⟨t, hut, htL⟩ := p.augmenting_tenacity_bound ha i
      have hLt : p.length ≤ t := by simpa only [hvt, hut, levelLE] using ht
      refine ⟨p.honest_on_augmenting_of_tenacity_ge ha i t hut hLt, ?_⟩
      intro hstrict
      have hh : p.length < t := by simpa only [hvt, hut, levelLT] using hstrict
      omega
    | some v =>
      let q := p.appendMatched hodd hm
      have hqlen : q.length = p.length + 1 := rfl
      have hqend : q.last = v := appendMatched_last _ _ _
      have hqeven : q.length % 2 = 0 := by omega
      have hqshort : q.Shortest := by
        unfold Shortest
        rw [hqeven, hqend, hqlen]
        exact (matched_shortest_iff M hm p.length).2 (by simpa only [Shortest, hodd] using hp)
      let j : Fin (q.length + 1) := ⟨i.val, by omega⟩
      have hvertex : q.vertex j = p.vertex i := by
        change (if h : i.val ≤ p.length then p.vertex ⟨i.val, _⟩ else v) = p.vertex i
        simp only [dite_eq_left (show i.val ≤ p.length by omega)]
      have htend : tenacity M q.last = tenacity M p.last := by
        rw [hqend]
        exact (matched_tenacity M hm).1.symm
      have htq : levelLE (tenacity M q.last) (tenacity M (q.vertex j)) := by
        simpa only [htend, hvertex] using ht
      obtain ⟨hhon, hmin⟩ := q.limited_honesty_even hqshort hqeven j htq
      refine ⟨?_, ?_⟩
      · simpa only [BFSHonest, hvertex] using hhon
      · intro hstrict
        have hstrictq : levelLT (tenacity M q.last) (tenacity M (q.vertex j)) := by
          simpa only [htend, hvertex] using hstrict
        simpa only [hvertex] using hmin hstrictq

end AltPath
end MaximumMatching
