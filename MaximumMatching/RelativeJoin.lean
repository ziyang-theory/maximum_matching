import MaximumMatching.RelativeShortest

/-! Converse of the relative-path decomposition: any shortest even path to an
actual common base can be joined to any shortest relative path to its child.
The proof derives disjointness, rather than assuming it. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Finite tenacity supplies a globally shortest path of either requested parity. -/
theorem finite_tenacity_shortest_parity (v : V) (t k : Nat)
    (ht : tenacity M v = some t) :
    ∃ r : AltPath M, r.last = v ∧ r.Shortest ∧ r.length % 2 = k % 2 := by
  obtain ⟨e, o, he, ho, hep, hop, _⟩ := finite_levels_of_tenacity v t ht
  by_cases hk : k % 2 = 0
  · have hs := (level_eq_some_iff M 0 v e).1 he
    obtain ⟨r, hrv, hrl, _⟩ := hs.1
    refine ⟨r, hrv, ?_, by omega⟩
    simpa only [AltPath.Shortest, hrl, hep, hrv] using hs
  · have hs := (level_eq_some_iff M 1 v o).1 ho
    obtain ⟨r, hrv, hrl, _⟩ := hs.1
    refine ⟨r, hrv, ?_, by omega⟩
    simpa only [AltPath.Shortest, hrl, hop, hrv] using hs

/-- The length of an arbitrary shortest relative segment is the corresponding
global parity level minus the base's evenlevel. An opposite global path through
the same base supplies the tenacity budget needed for disjoint concatenation. -/
theorem IsBase.relative_length_formula {v b : V} (hb : IsBase M v b)
    (p : AltPath M) (hp : p.Shortest) (hpe : p.length % 2 = 0) (hpb : p.last = b)
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v)
    (t : Nat) (hvt : tenacity M v = some t) :
    IsShortest M (q.length % 2) v (p.length + q.length) ∧
      2 * p.length + q.length ≤ t := by
  have hplevel : evenlevel M b = some p.length :=
    (level_eq_some_iff M 0 b p.length).2 (by simpa only [AltPath.Shortest, hpe, hpb] using hp)
  obtain ⟨r, hrv, hr, hrpar⟩ := finite_tenacity_shortest_parity v t q.length hvt
  obtain ⟨i, hie, hib, hip, his⟩ := hb.shortest_relative r hrv hr
  have hilevel : evenlevel M b = some i.val :=
    (level_eq_some_iff M 0 b i.val).2 (by
      simpa only [AltPath.Shortest, AltPath.take_length, AltPath.take_last, hie, hib] using hip)
  have hilen : i.val = p.length := Option.some.inj (hilevel.symm.trans hplevel)
  let s := r.segment i.val (by omega) hie
  have hsf : s.first = b := (r.segment_first i.val (by omega) hie).trans hib
  have hsl : s.last = v := (r.segment_last i.val (by omega) hie).trans hrv
  have hspar : s.length % 2 = q.length % 2 := by
    change (r.length - i.val) % 2 = q.length % 2
    omega
  have hqs : q.length ≤ s.length := hq s (hsf.trans hqb.symm) (hsl.trans hqv.symm) hspar
  have hsq : s.length ≤ q.length := his q (hqb.trans hsf.symm) (hqv.trans hsl.symm) hspar.symm
  have hqlen : q.length = r.length - i.val := Nat.le_antisymm hqs hsq
  have hrlen : r.length = p.length + q.length := by omega
  have hsumpar : (p.length + q.length) % 2 = q.length % 2 := by omega
  have hshort : IsShortest M (q.length % 2) v (p.length + q.length) := by
    simpa only [AltPath.Shortest, hrv, hrlen, hsumpar] using hr
  refine ⟨hshort, ?_⟩
  obtain ⟨u, huv, hu, hupar⟩ := finite_tenacity_shortest_parity v t (q.length + 1) hvt
  obtain ⟨j, _, _, hjlt, hjmin, _⟩ := hb.on_shortest u huv hu
  have hpmin : minlevel M b = some p.length := (minlevel_eq_even_of_outer b hb.outer).trans hplevel
  have hjlen : j.val = p.length := Option.some.inj (hjmin.symm.trans hpmin)
  have hsum : r.length + u.length = t := by
    have ht' : tenacity M v = some (r.length + u.length) := by
      by_cases hqeven : q.length % 2 = 0
      · have hre : r.length % 2 = 0 := hrpar.trans hqeven
        have huo : u.length % 2 = 1 := by omega
        have hten := r.opposite_shortest_tenacity u hr hu (hrv.trans huv.symm) hre huo
        simpa only [hrv] using hten
      · have hro : r.length % 2 = 1 := by omega
        have hue : u.length % 2 = 0 := by omega
        have hten := u.opposite_shortest_tenacity r hu hr (huv.trans hrv.symm) hue hro
        simpa only [huv, Nat.add_comm] using hten
    exact Option.some.inj (ht'.symm.trans hvt)
  omega

/-- Any shortest relative path avoids every vertex of any shortest even prefix
to the base, apart from the shared base endpoint. -/
theorem IsBase.relative_avoids_prefix {v b : V} (hb : IsBase M v b)
    (p : AltPath M) (hp : p.Shortest) (hpe : p.length % 2 = 0) (hpb : p.last = b)
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v) :
    ∀ (i : Fin (p.length + 1)) (j : Fin (q.length + 1)),
      0 < j.val → p.vertex i ≠ q.vertex j := by
  obtain ⟨t, hvt, _⟩ := (show IsBase M v b from hb)
  obtain ⟨hshort, hbound⟩ := hb.relative_length_formula p hp hpe hpb q hq hqb hqv t hvt
  apply p.segment_avoids_prefix q (hpb.trans hqb.symm) (by simpa only [hqv] using hshort)
    t ?_ ?_ hbound
  · exact (level_eq_some_iff M 0 p.last p.length).2
      (by simpa only [AltPath.Shortest, hpe] using hp)
  · rw [hpb]
    simpa only [hvt] using hb.high

/-- Proposition 6.17 in the joining direction: the actual concatenation of
arbitrary shortest component paths is a shortest global alternating path.
Disjointness comes from `relative_avoids_prefix`, not from the caller. -/
theorem IsBase.append_relative_shortest {v b : V} (hb : IsBase M v b)
    (p : AltPath M) (hp : p.Shortest) (hpe : p.length % 2 = 0) (hpb : p.last = b)
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v) :
    (p.appendSegment q hpe (hpb.trans hqb.symm)
      (hb.relative_avoids_prefix p hp hpe hpb q hq hqb hqv)).Shortest := by
  obtain ⟨t, hvt, _⟩ := (show IsBase M v b from hb)
  have hshort := (hb.relative_length_formula p hp hpe hpb q hq hqb hqv t hvt).1
  have hpar : (p.length + q.length) % 2 = q.length % 2 := by omega
  simpa only [AltPath.Shortest, AltPath.appendSegment_length, AltPath.appendSegment_last,
    hqv, hpar] using hshort

end MaximumMatching
