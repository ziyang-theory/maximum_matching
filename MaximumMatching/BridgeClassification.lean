import MaximumMatching.MinCorrectness
import MaximumMatching.GeneralSuffix
import MaximumMatching.MatchedLevels
import MaximumMatching.MinimumBridgeAll

/-! Bridge endpoint classification (Lemma 8.1, source pp.36--37).
All path extensions below prove simplicity. The results only need finite edge
tenacity; the source's additional upper bound by the shortest augmenting-path
length is unnecessary for these local conclusions. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

theorem bridge_symm {u v : V} (h : Bridge M u v) : Bridge M v u :=
  ⟨G.symm h.1, fun hprop => h.2 (hprop.elim Or.inr Or.inl)⟩

/-- An inner vertex with finite evenlevel has a strictly smaller oddlevel. -/
theorem inner_oddlevel_lt_evenlevel (v : V) (e : Nat)
    (he : evenlevel M v = some e) (hi : Inner M v) :
    ∃ o, oddlevel M v = some o ∧ o < e ∧ minlevel M v = some o := by
  cases ho : oddlevel M v with
  | none => exact False.elim (hi.2 (by simp only [Outer, he, ho, levelLT]))
  | some o =>
    have hn : ¬e < o := by simpa only [Outer, he, ho, levelLT] using hi.2
    have hep := level_parity M 0 v e he
    have hop := level_parity M 1 v o ho
    refine ⟨o, rfl, by omega, ?_⟩
    simp only [minlevel, he, ho, levelMin, Nat.min_eq_right (by omega : o ≤ e)]

/-- A finite matched bridge has inner endpoints of equal odd minlevel.
Matched outer endpoints would make the edge a prop. -/
theorem matched_bridge_levels {u v : V} (hb : Bridge M u v)
    (hm : M.mate u = some v) (t : Nat) (ht : edgeTenacity M u v = some t) :
    ∃ i, oddlevel M u = some i ∧ oddlevel M v = some i ∧
      minlevel M u = some i ∧ minlevel M v = some i ∧
      Inner M u ∧ Inner M v ∧ t = 2 * i + 1 := by
  have ht' : matchedEdgeTenacity M u v = some t := by
    simpa only [edgeTenacity, ite_eq_left hm] using ht
  have hvt := (matched_tenacity M hm).2.trans ht'
  have hut := (matched_tenacity M hm).1.trans hvt
  obtain ⟨eu, ou, hue, huo, heu, hou, hsu⟩ := finite_levels_of_tenacity u t hut
  obtain ⟨ev, ov, hve, hvo, hev, hov, hsv⟩ := finite_levels_of_tenacity v t hvt
  have hnu : ¬ Outer M u := by
    intro hu
    exact hb.2 (matched_edge_prop_of_even_minlevel hm eu hue
      ((minlevel_eq_even_of_outer u hu).trans hue))
  have hnv : ¬ Outer M v := by
    intro hv
    exact (bridge_symm hb).2 (matched_edge_prop_of_even_minlevel (M.symm hm) ev hve
      ((minlevel_eq_even_of_outer v hv).trans hve))
  have hule : ou ≤ eu := by
    have : ¬eu < ou := by simpa only [Outer, hue, huo, levelLT] using hnu
    omega
  have hvle : ov ≤ ev := by
    have : ¬ev < ov := by simpa only [Outer, hve, hvo, levelLT] using hnv
    omega
  have hmu : minlevel M u = some ou := by
    simp only [minlevel, hue, huo, levelMin, Nat.min_eq_right hule]
  have hmv : minlevel M v = some ov := by
    simp only [minlevel, hve, hvo, levelMin, Nat.min_eq_right hvle]
  have heu' : eu = ov + 1 := by
    have h := evenlevel_matched M (M.symm hm)
    simpa only [hue, hvo, Option.map_some, Option.some.injEq] using h
  have hev' : ev = ou + 1 := by
    have h := evenlevel_matched M hm
    simpa only [hve, huo, Option.map_some, Option.some.injEq] using h
  have heq : ou = ov := by omega
  refine ⟨ou, huo, ?_, hmu, ?_, ⟨⟨ou, hmu⟩, hnu⟩, ⟨⟨ov, hmv⟩, hnv⟩, ?_⟩
  · simpa only [heq] using hvo
  · simpa only [heq] using hmv
  · omega

/-- At an unmatched bridge, an inner destination has odd minlevel strictly
below the possible arrival length from the other endpoint's evenlevel. -/
theorem unmatched_bridge_inner_arrival {u v : V} (hb : Bridge M u v)
    (hm : M.mate u ≠ some v) (e f : Nat)
    (he : evenlevel M u = some e) (hf : evenlevel M v = some f)
    (hv : Inner M v) :
    ∃ o, oddlevel M v = some o ∧ minlevel M v = some o ∧ o < e + 1 ∧ o < f := by
  have hep := level_parity M 0 u e he
  obtain ⟨o, ho, hof, hmin⟩ := inner_oddlevel_lt_evenlevel v f hf hv
  have hpar : (M.mate u = some v) ↔ e % 2 = 1 := by simp [hm, hep]
  obtain ⟨k, hk, hke⟩ := minlevel_neighbor_bound u v e (by simpa only [hep] using he) hb.1 hpar
  have hko : k = o := Option.some.inj (hk.symm.trans hmin)
  have hne : o ≠ e + 1 := by
    intro heq
    have hpred := (predecessor_iff_level_guard u v e (by rw [hmin, heq])).2
      ⟨hb.1, by simpa only [hep] using he, hpar⟩
    exact hb.2 (Or.inl hpred)
  exact ⟨o, ho, hmin, by omega, hof⟩

/-- Both outer endpoints of an unmatched bridge have the same evenlevel, and
their oddlevels are exactly one larger. -/
theorem unmatched_bridge_outer_levels {u v : V} (hb : Bridge M u v)
    (hm : M.mate u ≠ some v) (e f : Nat)
    (he : evenlevel M u = some e) (hf : evenlevel M v = some f)
    (hu : Outer M u) (hv : Outer M v) :
    e = f ∧ oddlevel M u = some (e + 1) ∧ oddlevel M v = some (f + 1) := by
  have hep := level_parity M 0 u e he
  have hfp := level_parity M 0 v f hf
  have hm' : M.mate v ≠ some u := fun h => hm (M.symm h)
  have hmu : minlevel M u = some e := (minlevel_eq_even_of_outer u hu).trans he
  have hmv : minlevel M v = some f := (minlevel_eq_even_of_outer v hv).trans hf
  obtain ⟨k, hk, hke⟩ := minlevel_neighbor_bound u v e
    (by simpa only [hep] using he) hb.1 (by simp [hm, hep])
  obtain ⟨l, hl, hlf⟩ := minlevel_neighbor_bound v u f
    (by simpa only [hfp] using hf) (G.symm hb.1) (by simp [hm', hfp])
  have hkf := Option.some.inj (hk.symm.trans hmv)
  have hle := Option.some.inj (hl.symm.trans hmu)
  have hef : e = f := by omega
  have odd_from (a b : V) (k : Nat) (ha : evenlevel M a = some k)
      (hbmin : minlevel M b = some k) (hbouter : Outer M b)
      (hab : G.Adj a b) (hn : M.mate a ≠ some b) : oddlevel M b = some (k + 1) := by
    obtain ⟨p, hp, hl, hpar⟩ := ((level_eq_some_iff M 0 a k).1 ha).1
    have hfresh : ∀ j, p.vertex j ≠ b := by
      intro j hj
      have hbound := minlevel_le_path M b k hbmin (p.take j.val (by omega)) hj
      simp only [AltPath.take_length] at hbound
      have hjlast : j = ⟨p.length, by omega⟩ := by
        apply Fin.ext
        change j.val = p.length
        have := j.isLt
        omega
      rw [hjlast] at hj
      have hab' : a = b := hp.symm.trans hj
      exact G.loopless b (hab' ▸ hab)
    have hadj : G.Adj p.last b := by rw [hp]; exact hab
    have hpa : (M.mate p.last = some b) ↔ p.length % 2 = 1 := by
      simp only [hp, hl, hpar, hn]; decide
    let q := p.append b hfresh hadj hpa
    have hq : HasPathLength M 1 b (k + 1) :=
      ⟨q, AltPath.append_last _ _ _ _ _, by change p.length + 1 = k + 1; omega, by omega⟩
    cases ho : oddlevel M b with
    | none => exact False.elim ((level_eq_none_iff M 1 b).1 ho ⟨k + 1, hq⟩)
    | some o =>
      have hob := ((level_eq_some_iff M 1 b o).1 ho).2 (k + 1) hq
      have hbo := (minlevel_eq_even_of_outer b hbouter).symm.trans hbmin
      have hko : k < o := by simpa only [Outer, hbo, ho, levelLT] using hbouter
      exact congrArg some (by omega)
  refine ⟨hef, ?_, ?_⟩
  · exact odd_from v u e (by simpa only [hef] using hf) hmu hu (G.symm hb.1) hm'
  · exact odd_from u v f (by simpa only [hef] using he) hmv hv hb.1 hm

/-- The outer endpoint in the mixed case has tenacity at most the bridge's.
If it already lies on the other endpoint's even path, use its odd prefix or
its position in the low-tenacity suffix; do not append a repeated vertex. -/
theorem unmatched_bridge_mixed_tenacity {u v : V} (hb : Bridge M u v)
    (hm : M.mate u ≠ some v) (e f : Nat)
    (he : evenlevel M u = some e) (hf : evenlevel M v = some f)
    (hu : Outer M u) (hv : Inner M v) :
    ∃ s, tenacity M u = some s ∧ s ≤ e + f + 1 := by
  classical
  have hep := level_parity M 0 u e he
  have hfp := level_parity M 0 v f hf
  have hm' : M.mate v ≠ some u := fun h => hm (M.symm h)
  have hmu : minlevel M u = some e := (minlevel_eq_even_of_outer u hu).trans he
  obtain ⟨o, ho, _, hoe, hof⟩ := unmatched_bridge_inner_arrival hb hm e f he hf hv
  obtain ⟨p, hp, hl, _⟩ := ((level_eq_some_iff M 0 v f).1 hf).1
  have hpe : p.length % 2 = 0 := by omega
  have hpshort : p.Shortest := by
    simpa only [AltPath.Shortest, hp, hl, hfp] using (level_eq_some_iff M 0 v f).1 hf
  have odd_bound (k : Nat) (hk : HasPathLength M 1 u k) :
      ∃ s, tenacity M u = some s ∧ s ≤ e + k := by
    exact tenacity_bound_of_opposite_witnesses u e k
      (by simpa only [hep] using ((level_eq_some_iff M 0 u e).1 he).1)
      (by simpa only [show (e + 1) % 2 = 1 by omega] using hk)
  by_cases hhit : ∃ j, p.vertex j = u
  · obtain ⟨j, hj⟩ := hhit
    by_cases hjo : j.val % 2 = 1
    · obtain ⟨s, hs, hsb⟩ := odd_bound j.val (by
        simpa only [hjo, hj] using p.prefix_witness j)
      exact ⟨s, hs, by have := j.isLt; omega⟩
    · have hjmin := minlevel_le_path M u e hmu (p.take j.val (by omega)) hj
      simp only [AltPath.take_length] at hjmin
      obtain ⟨q, hq, hqlen, hqpar⟩ := ((level_eq_some_iff M 1 v o).1 ho).1
      obtain ⟨s, hs, hsb⟩ := p.tenacity_bound_suffix q hpshort hpe (by omega)
        (hq.trans hp.symm) (by omega) j (by omega)
      exact ⟨s, by simpa only [hj] using hs, by omega⟩
  · have hfresh : ∀ j, p.vertex j ≠ u := fun j hj => hhit ⟨j, hj⟩
    have hadj : G.Adj p.last u := by rw [hp]; exact G.symm hb.1
    have hpar : (M.mate p.last = some u) ↔ p.length % 2 = 1 := by
      simp [hp, hm', hpe]
    let q := p.append u hfresh hadj hpar
    have hq : HasPathLength M 1 u (f + 1) :=
      ⟨q, AltPath.append_last _ _ _ _ _, by change p.length + 1 = f + 1; omega, by omega⟩
    obtain ⟨s, hs, hsb⟩ := odd_bound (f + 1) hq
    exact ⟨s, hs, by omega⟩

/-- Lemma 8.1 for unmatched bridges, with finite edge tenacity and either
endpoint classification. The strict bound for inner vertices is essential
for MAX's earlier-level scheduling. -/
theorem unmatched_bridge_tenacity {u v : V} (hb : Bridge M u v)
    (hm : M.mate u ≠ some v) (t : Nat) (ht : edgeTenacity M u v = some t) :
    (Outer M u → ∃ s, tenacity M u = some s ∧ s ≤ t) ∧
    (Inner M u → ∃ s, tenacity M u = some s ∧ s < t) := by
  have ht' : (levelAdd (evenlevel M u) (evenlevel M v)).map (· + 1) = some t := by
    simpa only [edgeTenacity, ite_eq_right hm] using ht
  have hlevels : ∃ e f, evenlevel M u = some e ∧ evenlevel M v = some f ∧ t = e + f + 1 := by
    cases he : evenlevel M u with
    | none => simp only [he, levelAdd, Option.map_none] at ht'; contradiction
    | some e =>
      cases hf : evenlevel M v with
      | none => simp only [he, hf, levelAdd, Option.map_none] at ht'; contradiction
      | some f =>
        refine ⟨e, f, rfl, rfl, ?_⟩
        simpa only [he, hf, levelAdd, Option.map_some, Option.some.injEq] using ht'.symm
  obtain ⟨e, f, he, hf, htval⟩ := hlevels
  have hm' : M.mate v ≠ some u := fun h => hm (M.symm h)
  constructor
  · intro hu
    by_cases hv : Outer M v
    · obtain ⟨hef, huo, _⟩ := unmatched_bridge_outer_levels hb hm e f he hf hu hv
      refine ⟨e + (e + 1), ?_, by omega⟩
      simp only [tenacity, he, huo, levelAdd]
    · have hvfinite : ∃ k, minlevel M v = some k := by
        have hfp := level_parity M 0 v f hf
        obtain ⟨k, hk, _⟩ := minlevel_le_of_level v f (by simpa only [hfp] using hf)
        exact ⟨k, hk⟩
      obtain ⟨s, hs, hst⟩ := unmatched_bridge_mixed_tenacity hb hm e f he hf hu ⟨hvfinite, hv⟩
      exact ⟨s, hs, by omega⟩
  · intro hu
    obtain ⟨o, ho, _, hof, _⟩ := unmatched_bridge_inner_arrival (bridge_symm hb) hm' f e hf he hu
    refine ⟨e + o, ?_, by omega⟩
    simp only [tenacity, he, ho, levelAdd]

end MaximumMatching
