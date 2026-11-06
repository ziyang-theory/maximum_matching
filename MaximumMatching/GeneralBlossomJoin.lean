import MaximumMatching.BlossomRelative

/-! Any shortest relative path to an established blossom member joins to any
shortest even path to its boundary. The actual common-base chain supplies the
length identities; disjointness follows from the boundary's high tenacity. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The global parity level equals the boundary's evenlevel plus the shortest
relative length, including blossoms whose member has an iterated base. -/
theorem blossom_relative_length_formula (t : Nat) (b v : V)
    (hv : Blossom M t b v) (hb : levelLT (some t) (tenacity M b))
    (p : AltPath M) (hp : p.Shortest) (hpe : p.length % 2 = 0) (hpb : p.last = b)
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v)
    (τ : Nat) (hvt : tenacity M v = some τ) :
    IsShortest M (q.length % 2) v (p.length + q.length) ∧
      2 * p.length + q.length ≤ τ := by
  have hplevel : evenlevel M b = some p.length :=
    (level_eq_some_iff M 0 b p.length).2 (by simpa only [AltPath.Shortest, hpe, hpb] using hp)
  obtain ⟨r, hrv, hr, hrpar⟩ := finite_tenacity_shortest_parity v τ q.length hvt
  obtain ⟨i, hie, hib, hip, his⟩ := blossom_shortest_relative t b v hv hb r hrv hr
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
  obtain ⟨u, huv, hu, hupar⟩ := finite_tenacity_shortest_parity v τ (q.length + 1) hvt
  obtain ⟨j, _, _, hjlt, hjmin, _⟩ := blossom_on_shortest t b v hv u huv hu
  have hpmin : minlevel M b = some p.length := (minlevel_eq_even_of_outer b (blossom_outer t b v hv)).trans hplevel
  have hjlen : j.val = p.length := Option.some.inj (hjmin.symm.trans hpmin)
  have hsum : r.length + u.length = τ := by
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
theorem blossom_relative_avoids_prefix (t : Nat) (b v : V)
    (hv : Blossom M t b v) (hb : levelLT (some t) (tenacity M b))
    (p : AltPath M) (hp : p.Shortest) (hpe : p.length % 2 = 0) (hpb : p.last = b)
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v) :
    ∀ (i : Fin (p.length + 1)) (j : Fin (q.length + 1)),
      0 < j.val → p.vertex i ≠ q.vertex j := by
  obtain ⟨s, hvt, hst⟩ := blossom_tenacity_bound t b v hv
  obtain ⟨hshort, hbound⟩ := blossom_relative_length_formula t b v hv hb p hp hpe hpb q hq hqb hqv s hvt
  apply p.segment_avoids_prefix q (hpb.trans hqb.symm) (by simpa only [hqv] using hshort)
    t ?_ ?_ (by omega)
  · exact (level_eq_some_iff M 0 p.last p.length).2
      (by simpa only [AltPath.Shortest, hpe] using hp)
  · rw [hpb]
    exact hb

/-- Proposition 6.17 in the joining direction: the actual concatenation of
arbitrary shortest component paths is a shortest global alternating path.
Disjointness comes from `relative_avoids_prefix`, not from the caller. -/
theorem blossom_append_relative_shortest (t : Nat) (b v : V)
    (hv : Blossom M t b v) (hb : levelLT (some t) (tenacity M b))
    (p : AltPath M) (hp : p.Shortest) (hpe : p.length % 2 = 0) (hpb : p.last = b)
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v) :
    (p.appendSegment q hpe (hpb.trans hqb.symm)
      (blossom_relative_avoids_prefix t b v hv hb p hp hpe hpb q hq hqb hqv)).Shortest := by
  obtain ⟨s, hvt, hst⟩ := blossom_tenacity_bound t b v hv
  have hshort := (blossom_relative_length_formula t b v hv hb p hp hpe hpb q hq hqb hqv s hvt).1
  have hpar : (p.length + q.length) % 2 = q.length % 2 := by omega
  simpa only [AltPath.Shortest, AltPath.appendSegment_length, AltPath.appendSegment_last,
    hqv, hpar] using hshort


end MaximumMatching
