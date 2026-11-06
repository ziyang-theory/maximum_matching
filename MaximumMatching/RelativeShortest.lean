import MaximumMatching.SegmentSplice
import MaximumMatching.Base
import MaximumMatching.BasePaths
import MaximumMatching.MatchedLevels

/-! Relative shortestness at a high-tenacity even vertex. The argument compares
all relative alternating paths, including ones intersecting the free-root prefix.
-/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Relative minimality quantifies over all simple alternating segments of the
same parity and with the same endpoints; no extension or confinement is assumed. -/
def AltSegment.Shortest (s : AltSegment M) : Prop :=
  ∀ q : AltSegment M, q.first = s.first → q.last = s.last →
    q.length % 2 = s.length % 2 → s.length ≤ q.length

private theorem least_segment_hit (P : Nat → Prop) (n : Nat) (hn : P n) :
    ∃ m, P m ∧ ∀ l, l < m → ¬P l := by
  classical
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hs : ∃ m, m < n ∧ P m
    · obtain ⟨m, hm, hp⟩ := hs
      exact ih m hm hp
    · exact ⟨n, hn, fun l hl hp => hs ⟨l, hl, hp⟩⟩

namespace AltPath

/-- The earliest vertex of an ordinary path meeting a relative path. Its strict
prefix avoids the entire relative path, in both traversal directions. -/
theorem first_segment_hit (p : AltPath M) (q : AltSegment M)
    (k : Fin (p.length + 1)) (hk : p.vertex k = q.first) :
    ∃ (i : Fin (p.length + 1)) (j : Fin (q.length + 1)), i.val ≤ k.val ∧
      p.vertex i = q.vertex j ∧
      ∀ (a : Fin (p.length + 1)) (b : Fin (q.length + 1)),
        a.val < i.val → p.vertex a ≠ q.vertex b := by
  let P (i : Nat) := ∃ (hi : i < p.length + 1) (j : Fin (q.length + 1)),
    p.vertex ⟨i, hi⟩ = q.vertex j
  obtain ⟨m, ⟨hm, j, hh⟩, hmin⟩ := least_segment_hit P k.val ⟨k.isLt, ⟨0, by omega⟩, hk⟩
  have hmk : m ≤ k.val := by
    by_cases h : m ≤ k.val
    · exact h
    · exact False.elim (hmin k.val (by omega) ⟨k.isLt, ⟨0, by omega⟩, hk⟩)
  refine ⟨⟨m, hm⟩, j, hmk, hh, ?_⟩
  intro a b ha he
  exact hmin a.val ha ⟨a.isLt, b, he⟩

/-- If a shortest path passes an even vertex of tenacity greater than `t`, and
its length plus that vertex's evenlevel is at most `t`, its remaining segment
is a shortest relative path. A competing segment may intersect the prefix:
the first-intersection proof either shortens the original path or gives a
forbidden short odd path to the high-tenacity vertex. -/
theorem segment_shortest_of_high (p : AltPath M) (hp : p.Shortest)
    (k : Fin (p.length + 1)) (hke : k.val % 2 = 0) (t : Nat)
    (hlevel : evenlevel M (p.vertex k) = some k.val)
    (hhigh : levelLT (some t) (tenacity M (p.vertex k)))
    (hbound : p.length + k.val ≤ t) :
    (p.segment k.val (by omega) hke).Shortest := by
  intro q hqfirst hqlast hqpar
  change p.length - k.val ≤ q.length
  apply Nat.le_of_not_gt
  intro hshort
  have hqf : q.first = p.vertex k := by simpa only [segment_first, Fin.eta] using hqfirst
  have hql : q.last = p.last := by simpa only [segment_last] using hqlast
  have hqp : q.length % 2 = p.length % 2 := by
    change q.length % 2 = (p.length - k.val) % 2 at hqpar
    omega
  obtain ⟨i, j, hik, hij, hfirst⟩ := p.first_segment_hit q k hqf.symm
  have hpj : (p.take i.val (by omega)).last = q.vertex j := hij
  have hdis : ∀ (a : Fin ((p.take i.val (by omega)).length + 1))
      (b : Fin (q.length + 1)), b.val ≠ j.val →
      (p.take i.val (by omega)).vertex a ≠ q.vertex b := by
    intro a b hb he
    have ha : a.val ≤ i.val := by have := a.isLt; change a.val < i.val + 1 at this; omega
    change p.vertex ⟨a.val, by omega⟩ = q.vertex b at he
    by_cases hal : a.val < i.val
    · exact hfirst ⟨a.val, by omega⟩ b hal he
    · have hai : (⟨a.val, by omega⟩ : Fin (p.length + 1)) = i := Fin.ext (by change a.val = i.val; omega)
      rw [hai, hij] at he
      have heq := congrArg (fun x : Fin (q.length + 1) => x.val) (q.injective _ _ he)
      exact hb heq.symm
  have noOdd (r : AltPath M) (hre : r.last = p.vertex k) (hro : r.length % 2 = 1)
      (hrb : k.val + r.length ≤ t) : False := by
    have hw : HasPathLength M 1 (p.vertex k) r.length := ⟨r, hre, rfl, hro⟩
    cases ho : oddlevel M (p.vertex k) with
    | none => exact (level_eq_none_iff M 1 _).1 ho ⟨r.length, hw⟩
    | some a =>
      have ha := ((level_eq_some_iff M 1 _ a).1 ho).2 r.length hw
      have ht : t < k.val + a := by
        simpa only [tenacity, hlevel, ho, levelAdd, levelLT] using hhigh
      omega
  by_cases hpar : i.val % 2 = j.val % 2
  · have hd : (p.take i.val (by omega)).SegmentSuffixDisjoint q j.val := by
      intro a b hb
      exact hdis a b (by omega)
    let r := (p.take i.val (by omega)).spliceSegment q j.val (by omega) hpj hpar hd
    have hrl : r.length = i.val + (q.length - j.val) := rfl
    have hre : r.last = p.last := (spliceSegment_last _ _ _ _ _ _ _).trans hql
    have hrp : r.length % 2 = p.length % 2 := (spliceSegment_parity _ _ _ _ _ _ _).trans hqp
    have hl := hp.2 r.length ⟨r, hre, rfl, hrp⟩
    omega
  · by_cases hio : i.val % 2 = 1
    · have hje : j.val % 2 = 0 := by omega
      have hd : (p.take i.val (by omega)).SegmentReverseDisjoint q 0 j.val := by
        intro a b _ hb
        exact hdis a b (by omega)
      let r := (p.take i.val (by omega)).spliceReverseSegment q 0 j.val (by omega)
        (by omega) hpj hio hje hd
      have hrl : r.length = i.val + j.val := by change i.val + (j.val - 0) = _; omega
      have hre : r.last = p.vertex k := by
        have hh := spliceReverseSegment_last (p.take i.val (by omega)) q 0 j.val
          (by omega) (by omega) hpj hio hje hd
        exact hh.trans hqf
      exact noOdd r hre (by rw [hrl]; omega) (by rw [hrl]; omega)
    · have hie : i.val % 2 = 0 := by omega
      have hjo : j.val % 2 = 1 := by omega
      let s := (q.take j.val (by omega)).reverse hjo
      have hsfirst : s.first = q.vertex j := by
        simp only [s, AltSegment.first, AltSegment.reverse, AltSegment.take, Nat.sub_zero, Fin.eta]
      have hslast : s.last = q.first := by
        simp only [s, AltSegment.last, AltSegment.reverse, AltSegment.take, Nat.sub_self, AltSegment.first]
      have hslen : s.length = j.val := rfl
      have hd : ∀ (a : Fin ((p.take i.val (by omega)).length + 1))
          (b : Fin (s.length + 1)), 0 < b.val →
          (p.take i.val (by omega)).vertex a ≠ s.vertex b := by
        intro a b hb
        change (p.take i.val (by omega)).vertex a ≠ q.vertex ⟨j.val - b.val, by omega⟩
        exact hdis a ⟨j.val - b.val, by omega⟩ (by
          change j.val - b.val ≠ j.val
          have hbb := b.isLt
          change b.val < j.val + 1 at hbb
          omega)
      let r := (p.take i.val (by omega)).appendSegment s hie (hpj.trans hsfirst.symm) hd
      have hrl : r.length = i.val + j.val := rfl
      have hre : r.last = p.vertex k :=
        (appendSegment_last _ _ _ _ _).trans (hslast.trans hqf)
      exact noOdd r hre (by rw [hrl]; omega) (by rw [hrl]; omega)

/-- A shortest relative segment cannot return to an earlier vertex of an even
prefix to a high-tenacity base. The total target length is specified by a
semantic shortest-path fact, rather than by assuming concatenation is valid. -/
theorem segment_avoids_prefix (p : AltPath M) (q : AltSegment M)
    (hjoin : p.last = q.first)
    (hshort : IsShortest M (q.length % 2) q.last (p.length + q.length))
    (t : Nat) (hlevel : evenlevel M p.last = some p.length)
    (hhigh : levelLT (some t) (tenacity M p.last))
    (hbound : 2 * p.length + q.length ≤ t) :
    ∀ (a : Fin (p.length + 1)) (b : Fin (q.length + 1)),
      0 < b.val → p.vertex a ≠ q.vertex b := by
  intro a b hb hab
  have ha : a.val < p.length := by
    by_cases ha : a.val < p.length
    · exact ha
    · have hae : a = ⟨p.length, by omega⟩ := Fin.ext (by change a.val = p.length; omega)
      rw [hae] at hab
      have hsame : q.vertex ⟨0, by omega⟩ = q.vertex b := hjoin.symm.trans hab
      have hidx := congrArg (fun x : Fin (q.length + 1) => x.val) (q.injective _ _ hsame)
      change 0 = b.val at hidx
      omega
  obtain ⟨i, j, _, hij, hfirst⟩ := p.first_segment_hit q ⟨p.length, by omega⟩ hjoin
  have hia : i.val ≤ a.val := by
    by_cases h : i.val ≤ a.val
    · exact h
    · exact False.elim (hfirst a b (by omega) hab)
  have hil : i.val < p.length := by omega
  have hpj : (p.take i.val (by omega)).last = q.vertex j := hij
  have hdis : ∀ (x : Fin ((p.take i.val (by omega)).length + 1))
      (y : Fin (q.length + 1)), y.val ≠ j.val →
      (p.take i.val (by omega)).vertex x ≠ q.vertex y := by
    intro x y hy he
    have hx : x.val ≤ i.val := by have := x.isLt; change x.val < i.val + 1 at this; omega
    change p.vertex ⟨x.val, by omega⟩ = q.vertex y at he
    by_cases hxl : x.val < i.val
    · exact hfirst ⟨x.val, by omega⟩ y hxl he
    · have hxi : (⟨x.val, by omega⟩ : Fin (p.length + 1)) = i := Fin.ext (by change x.val = i.val; omega)
      rw [hxi, hij] at he
      exact hy (congrArg (fun z : Fin (q.length + 1) => z.val) (q.injective _ _ he)).symm
  have noOdd (r : AltPath M) (hre : r.last = p.last) (hro : r.length % 2 = 1)
      (hrb : p.length + r.length ≤ t) : False := by
    have hw : HasPathLength M 1 p.last r.length := ⟨r, hre, rfl, hro⟩
    cases ho : oddlevel M p.last with
    | none => exact (level_eq_none_iff M 1 _).1 ho ⟨r.length, hw⟩
    | some k =>
      have hk := ((level_eq_some_iff M 1 _ k).1 ho).2 r.length hw
      have ht : t < p.length + k := by
        simpa only [tenacity, hlevel, ho, levelAdd, levelLT] using hhigh
      omega
  by_cases hpar : i.val % 2 = j.val % 2
  · have hd : (p.take i.val (by omega)).SegmentSuffixDisjoint q j.val := by
      intro x y hy
      exact hdis x y (by omega)
    let r := (p.take i.val (by omega)).spliceSegment q j.val (by omega) hpj hpar hd
    have hrl : r.length = i.val + (q.length - j.val) := rfl
    have hre : r.last = q.last := spliceSegment_last _ _ _ _ _ _ _
    have hrp : r.length % 2 = q.length % 2 := spliceSegment_parity _ _ _ _ _ _ _
    have hl := hshort.2 r.length ⟨r, hre, rfl, hrp⟩
    omega
  · by_cases hio : i.val % 2 = 1
    · have hje : j.val % 2 = 0 := by omega
      have hd : (p.take i.val (by omega)).SegmentReverseDisjoint q 0 j.val := by
        intro x y _ hy
        exact hdis x y (by omega)
      let r := (p.take i.val (by omega)).spliceReverseSegment q 0 j.val (by omega)
        (by omega) hpj hio hje hd
      have hrl : r.length = i.val + j.val := by change i.val + (j.val - 0) = _; omega
      have hre : r.last = p.last :=
        (spliceReverseSegment_last _ _ _ _ _ _ _ _ _ _).trans hjoin.symm
      exact noOdd r hre (by rw [hrl]; omega) (by rw [hrl]; omega)
    · have hie : i.val % 2 = 0 := by omega
      have hjo : j.val % 2 = 1 := by omega
      let s := (q.take j.val (by omega)).reverse hjo
      have hsfirst : s.first = q.vertex j := by
        simp only [s, AltSegment.first, AltSegment.reverse, AltSegment.take, Nat.sub_zero, Fin.eta]
      have hslast : s.last = q.first := by
        simp only [s, AltSegment.last, AltSegment.reverse, AltSegment.take, Nat.sub_self, AltSegment.first]
      have hd : ∀ (x : Fin ((p.take i.val (by omega)).length + 1))
          (y : Fin (s.length + 1)), 0 < y.val →
          (p.take i.val (by omega)).vertex x ≠ s.vertex y := by
        intro x y hy
        change (p.take i.val (by omega)).vertex x ≠ q.vertex ⟨j.val - y.val, by omega⟩
        exact hdis x ⟨j.val - y.val, by omega⟩ (by
          change j.val - y.val ≠ j.val
          have hyb := y.isLt
          change y.val < j.val + 1 at hyb
          omega)
      let r := (p.take i.val (by omega)).appendSegment s hie (hpj.trans hsfirst.symm) hd
      have hrl : r.length = i.val + j.val := rfl
      have hre : r.last = p.last :=
        (appendSegment_last _ _ _ _ _).trans (hslast.trans hjoin.symm)
      exact noOdd r hre (by rw [hrl]; omega) (by rw [hrl]; omega)

end AltPath

/-- Proposition 6.17: whenever an actual common base exists, every shortest
parity path splits at that base into a shortest even prefix and a shortest
relative segment. No confinement or disjoint-extension hypothesis is assumed. -/
theorem IsBase.shortest_relative {v b : V} (hb : IsBase M v b)
    (p : AltPath M) (hpv : p.last = v) (hp : p.Shortest) :
    ∃ (i : Fin (p.length + 1)) (hie : i.val % 2 = 0),
      p.vertex i = b ∧ (p.take i.val (by omega)).Shortest ∧
      (p.segment i.val (by omega) hie).Shortest := by
  have hdata := hb
  obtain ⟨t, hvt, _⟩ := hdata
  obtain ⟨e, o, he, ho, he0, ho1, heo⟩ := finite_levels_of_tenacity v t hvt
  have hother : ∃ q : AltPath M, q.last = v ∧ q.Shortest ∧ p.length + q.length = t := by
    by_cases hp0 : p.length % 2 = 0
    · have hpl : evenlevel M v = some p.length :=
        (level_eq_some_iff M 0 v p.length).2 (by simpa only [AltPath.Shortest, hp0, hpv] using hp)
      have hlen : e = p.length := Option.some.inj (he.symm.trans hpl)
      have hs := (level_eq_some_iff M 1 v o).1 ho
      obtain ⟨q, hqv, hql, _⟩ := hs.1
      refine ⟨q, hqv, ?_, by omega⟩
      simpa only [AltPath.Shortest, hql, ho1, hqv] using hs
    · have hp1 : p.length % 2 = 1 := by omega
      have hpl : oddlevel M v = some p.length :=
        (level_eq_some_iff M 1 v p.length).2 (by simpa only [AltPath.Shortest, hp1, hpv] using hp)
      have hlen : o = p.length := Option.some.inj (ho.symm.trans hpl)
      have hs := (level_eq_some_iff M 0 v e).1 he
      obtain ⟨q, hqv, hql, _⟩ := hs.1
      refine ⟨q, hqv, ?_, by omega⟩
      simpa only [AltPath.Shortest, hql, he0, hqv] using hs
  obtain ⟨q, hqv, hq, hpq⟩ := hother
  obtain ⟨i, hi, hie, _, himin, hip⟩ := hb.on_shortest p hpv hp
  obtain ⟨j, _, _, hjlt, hjmin, _⟩ := hb.on_shortest q hqv hq
  have hij : i.val = j.val := Option.some.inj (himin.symm.trans hjmin)
  refine ⟨i, hie, hi, hip, p.segment_shortest_of_high hp i hie t ?_ ?_ (by omega)⟩
  · rw [hi]
    exact (minlevel_eq_even_of_outer b hb.outer).symm.trans himin
  · rw [hi]
    simpa only [hvt] using hb.high

end MaximumMatching
