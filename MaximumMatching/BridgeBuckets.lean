import MaximumMatching.BaseGeometry
import MaximumMatching.GeneralBaseStructure
import MaximumMatching.MinComplete
import MaximumMatching.MinScan
import MaximumMatching.MinimumBaseStructure

section BridgeClassification

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

end BridgeClassification

section BridgeBuckets

/-! Semantic correctness of the actual bridge lists and tenacity buckets.
These results concern stored edges and executable enqueue/scan operations;
completion of MAX's support discovery remains separate. -/
namespace MaximumMatching.Search
variable {V : Type} {G : Graph V} {M : Matching G}
variable [DecidableEq V]

/-- Every operationally computed finite edge tenacity is its semantic value.
Unknown parity labels cannot manufacture a finite tenacity. -/
theorem edgeTenacity_sound (s : State V) (hs : LabelsSound M s) (u v : V) (t : Nat)
    (ht : edgeTenacity M s u v = some t) : MaximumMatching.edgeTenacity M u v = some t := by
  unfold edgeTenacity at ht
  by_cases hm : M.mate u = some v
  · simp only [hm, ite_true] at ht
    cases hu : parityLabel s u 1 with
    | none => simp [hu] at ht
    | some a =>
      cases hv : parityLabel s v 1 with
      | none => simp [hu, hv] at ht
      | some b =>
        have heq : a + b + 1 = t := by simpa [hu, hv] using ht
        have hau := parityLabel_sound s hs u 1 a hu
        have hbv := parityLabel_sound s hs v 1 b hv
        simp only [MaximumMatching.edgeTenacity, hm, ite_true, matchedEdgeTenacity,
          hau, hbv, levelAdd, Option.map_some, heq]
  · simp only [hm, ite_false] at ht
    cases hu : parityLabel s u 0 with
    | none => simp [hu] at ht
    | some a =>
      cases hv : parityLabel s v 0 with
      | none => simp [hu, hv] at ht
      | some b =>
        have heq : a + b + 1 = t := by simpa [hu, hv] using ht
        have hau := parityLabel_sound s hs u 0 a hu
        have hbv := parityLabel_sound s hs v 0 b hv
        simp only [MaximumMatching.edgeTenacity, hm, ite_false,
          hau, hbv, levelAdd, Option.map_some, heq]

def PropsSound (M : Matching G) (s : State V) : Prop :=
  ∀ u v, (u, v) ∈ s.props → Predecessor M u v

def BridgesSound (M : Matching G) (s : State V) : Prop :=
  ∀ u v, (u, v) ∈ s.bridges → Bridge M u v

def BucketsSound (M : Matching G) (s : State V) : Prop :=
  ∀ t u v, (u, v) ∈ s.bucket t →
    Bridge M u v ∧ MaximumMatching.edgeTenacity M u v = some t

def ClassificationSound (M : Matching G) (s : State V) : Prop :=
  PropsSound M s ∧ BridgesSound M s ∧ BucketsSound M s

omit [DecidableEq V] in
theorem enqueue_bucketsSound (s : State V) (hs : BucketsSound M s) (u v : V)
    (hb : Bridge M u v) (t : Option Nat)
    (ht : ∀ k, t = some k → MaximumMatching.edgeTenacity M u v = some k) :
    BucketsSound M (enqueue s u v t) := by
  cases t with
  | none => exact hs
  | some k =>
    intro j a b hmem
    change (a, b) ∈ (if j = k then (u, v) :: s.bucket j else s.bucket j) at hmem
    split at hmem
    next hj =>
      rcases List.mem_cons.mp hmem with he | hold
      · have he' := Prod.mk.inj he
        exact ⟨by simpa only [he'.1, he'.2] using hb,
          by simpa only [he'.1, he'.2, hj] using ht k rfl⟩
      · exact hs j a b hold
    next _ => exact hs j a b hmem

/-- Every actual classification by MIN is sound, including deferred bridges
whose operational tenacity is still unknown. -/
theorem scanCandidate_classificationSound [DecidableRel G.Adj]
    (s : State V) (i : Nat) (u v : V) (hi : MinInvariant M i s)
    (hc : ClassificationSound M s) : ClassificationSound M (scanCandidate M i u v s) := by
  unfold scanCandidate
  split
  next hg =>
    have hlevel := parityLabel_sound s hi.1 u (i % 2) i hg.2.1
    unfold scan
    split
    · exact hc
    next hseen =>
      have hfalse : seen s u v = false := Bool.eq_false_iff.mpr hseen
      split
      next ha =>
        have hp := (scan_assigns_semantic s i u v hi.2.1 hlevel hg.1 hg.2.2 hfalse ha).2.1
        refine ⟨?_, hc.2.1, hc.2.2⟩
        intro a b hmem
        rcases List.mem_cons.mp hmem with he | hold
        · have he' := Prod.mk.inj he
          simpa only [he'.1, he'.2] using hp
        · exact hc.1 a b hold
      next ha =>
        have hb := scan_rejects_bridge s i u v hi.1 hi.2.2.1 hlevel hg.1 hfalse
          (Bool.eq_false_iff.mpr ha)
        have hs' : BridgesSound M { s with bridges := (u, v) :: s.bridges } := by
          intro a b hmem
          rcases List.mem_cons.mp hmem with he | hold
          · have he' := Prod.mk.inj he
            simpa only [he'.1, he'.2] using hb
          · exact hc.2.1 a b hold
        have hbs := enqueue_bucketsSound
          { { s with scanned := (u, v) :: s.scanned } with bridges := (u, v) :: s.bridges }
          hc.2.2 u v hb (edgeTenacity M s u v) (fun k hk => edgeTenacity_sound s hi.1 u v k hk)
        refine ⟨?_, ?_, hbs⟩
        · unfold enqueue; split <;> exact hc.1
        · unfold enqueue; split <;> exact hs'
  next _ => exact hc

theorem scanCandidates_classificationSound [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (i : Nat) (hi : MinInvariant M i s)
    (hc : ClassificationSound M s) : ClassificationSound M (scanCandidates M i xs s) := by
  induction xs generalizing s with
  | nil => exact hc
  | cons e es ih =>
    exact ih _ (scanCandidate_minInvariant s i e.1 e.2 hi)
      (scanCandidate_classificationSound s i e.1 e.2 hi hc)

omit [DecidableEq V] in
theorem initial_classificationSound (M : Matching G) : ClassificationSound M (initial M) := by
  simp [ClassificationSound, PropsSound, BridgesSound, BucketsSound, initial]

/-- The first concrete MIN stage correctly classifies and buckets every edge
it stores, independently of any structural blossom or MAX theorem. -/
theorem initial_scanLevel_classificationSound {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) : ClassificationSound M (scanLevel M 0 (initial M)) :=
  scanCandidates_classificationSound (allCandidates n) (initial M) 0
    (initial_minInvariant M) (initial_classificationSound M)

/-- Reconsider stored bridge tenacities after MAX makes a parity label known. -/
def refreshBridges (M : Matching G) (edges : List (V × V)) (s : State V) : State V :=
  edges.foldl (fun state e => enqueue state e.1 e.2 (edgeTenacity M state e.1 e.2)) s

omit [DecidableEq V] in
theorem enqueue_minLabel (s : State V) (u v w : V) (t : Option Nat) :
    (enqueue s u v t).minLabel w = s.minLabel w := by cases t <;> rfl

omit [DecidableEq V] in
theorem enqueue_maxLabel (s : State V) (u v w : V) (t : Option Nat) :
    (enqueue s u v t).maxLabel w = s.maxLabel w := by cases t <;> rfl

omit [DecidableEq V] in
theorem enqueue_bucket_mono (s : State V) (u v a b : V) (t : Option Nat) (k : Nat)
    (h : (a, b) ∈ s.bucket k) : (a, b) ∈ (enqueue s u v t).bucket k := by
  cases t with
  | none => exact h
  | some j =>
    change (a, b) ∈ (if k = j then (u, v) :: s.bucket k else s.bucket k)
    split
    · exact List.mem_cons_of_mem _ h
    · exact h

omit [DecidableEq V] in
theorem enqueue_mem (s : State V) (u v : V) (t : Nat) :
    (u, v) ∈ (enqueue s u v (some t)).bucket t := by simp [enqueue]

theorem refreshBridges_labels (M : Matching G) (edges : List (V × V)) (s : State V) :
    (∀ v, (refreshBridges M edges s).minLabel v = s.minLabel v) ∧
      (∀ v, (refreshBridges M edges s).maxLabel v = s.maxLabel v) := by
  induction edges generalizing s with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons e es ih =>
    have hh := ih (enqueue s e.1 e.2 (edgeTenacity M s e.1 e.2))
    exact ⟨fun v => (hh.1 v).trans (enqueue_minLabel s e.1 e.2 v _),
      fun v => (hh.2 v).trans (enqueue_maxLabel s e.1 e.2 v _)⟩

theorem edgeTenacity_enqueue (s : State V) (a b u v : V) (t : Option Nat) :
    edgeTenacity M (enqueue s a b t) u v = edgeTenacity M s u v := by cases t <;> rfl

theorem refreshBridges_bucket_mono (M : Matching G) (edges : List (V × V)) (s : State V)
    (u v : V) (t : Nat) (h : (u, v) ∈ s.bucket t) :
    (u, v) ∈ (refreshBridges M edges s).bucket t := by
  induction edges generalizing s with
  | nil => exact h
  | cons e es ih => exact ih _ (enqueue_bucket_mono s e.1 e.2 u v _ t h)

theorem refreshBridges_complete (M : Matching G) (edges : List (V × V)) (s : State V)
    (u v : V) (t : Nat) (hmem : (u, v) ∈ edges) (ht : edgeTenacity M s u v = some t) :
    (u, v) ∈ (refreshBridges M edges s).bucket t := by
  induction edges generalizing s with
  | nil => simp at hmem
  | cons e es ih =>
    rcases List.mem_cons.mp hmem with he | he
    · subst e
      apply refreshBridges_bucket_mono M es (enqueue s u v (edgeTenacity M s u v)) u v t
      change (u, v) ∈ (enqueue s u v (edgeTenacity M s u v)).bucket t
      rw [ht]
      exact enqueue_mem s u v t
    · exact ih _ he ((edgeTenacity_enqueue s e.1 e.2 u v _).trans ht)

theorem refreshBridges_bucketsSound (M : Matching G) (edges : List (V × V)) (s : State V)
    (hs : LabelsSound M s) (hb : BucketsSound M s)
    (he : ∀ u v, (u, v) ∈ edges → Bridge M u v) :
    BucketsSound M (refreshBridges M edges s) := by
  induction edges generalizing s with
  | nil => exact hb
  | cons e es ih =>
    apply ih _
    · constructor <;> intro v k hv
      · apply hs.1 v k
        simpa only [enqueue_minLabel] using hv
      · apply hs.2 v k
        simpa only [enqueue_maxLabel] using hv
    · exact enqueue_bucketsSound s hb e.1 e.2 (he e.1 e.2 (by simp)) _
        (fun k hk => edgeTenacity_sound s hs e.1 e.2 k hk)
    · intro u v hmem
      exact he u v (List.mem_cons_of_mem _ hmem)

/-- The concrete MAX incident-edge refresh considers the already registered
bridge orientations touching the newly labeled vertex. -/
def refreshIncident (M : Matching G) (v : V) (s : State V) : State V :=
  refreshBridges M (s.bridges.filter fun e => decide (e.1 = v ∨ e.2 = v)) s

theorem refreshIncident_bucketsSound (M : Matching G) (v : V) (s : State V)
    (hs : LabelsSound M s) (hc : ClassificationSound M s) :
    BucketsSound M (refreshIncident M v s) := by
  apply refreshBridges_bucketsSound M _ s hs hc.2.2
  intro a b hmem
  exact hc.2.1 a b (List.mem_filter.mp hmem).1

theorem refreshIncident_complete (M : Matching G) (w u v : V) (s : State V) (t : Nat)
    (hbridge : (u, v) ∈ s.bridges) (hincident : u = w ∨ v = w)
    (ht : edgeTenacity M s u v = some t) :
    (u, v) ∈ (refreshIncident M w s).bucket t := by
  apply refreshBridges_complete M _ s u v t
  · exact List.mem_filter.mpr ⟨hbridge, by simpa only [decide_eq_true_eq] using hincident⟩
  · exact ht

end MaximumMatching.Search

end BridgeBuckets

section MaxCorrectness

/-! Correctness of MAX's concrete label assignments. A supplied support member
is checked through its actual semantic tenacity; no arithmetic bound is assumed.
Discovering all support members by the contracted DDFS phase remains separate. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The exact subtraction used by MAX follows from finite vertex tenacity. -/
theorem maxlevel_eq_tenacity_sub (v : V) (t lo : Nat)
    (ht : tenacity M v = some t) (hlo : minlevel M v = some lo) :
    lo ≤ t ∧ maxlevel M v = some (t - lo) := by
  have hadd := minlevel_add_maxlevel M v
  rw [hlo, ht] at hadd
  cases hhi : maxlevel M v with
  | none => simp only [hhi, levelAdd] at hadd; contradiction
  | some hi =>
    have heq : lo + hi = t := by simpa only [hhi, levelAdd, Option.some.injEq] using hadd
    exact ⟨by omega, congrArg some (by omega)⟩

/-- At tenacity 2i+1 the minimum level is already at most i, so MAX does not
need an uncomputed minimum label for any vertex at its current tenacity. -/
theorem minlevel_le_half_tenacity (v : V) (i : Nat)
    (ht : tenacity M v = some (2 * i + 1)) :
    ∃ lo, minlevel M v = some lo ∧ lo ≤ i := by
  obtain ⟨e, o, he, ho, _, _, hsum⟩ := finite_levels_of_tenacity v (2 * i + 1) ht
  refine ⟨min e o, ?_, ?_⟩
  · simp [minlevel, he, ho, levelMin]
  · omega

namespace Search
variable [DecidableEq V]

/-- The actual MAX assignment preserves label soundness whenever the processed
vertex has the triggering bridge's tenacity. -/
theorem assignMax_labelsSound (s : State V) (t : Nat) (v : V)
    (hs : LabelsSound M s) (ht : tenacity M v = some t) :
    LabelsSound M (assignMax s t v) := by
  unfold assignMax
  cases hlo : s.minLabel v with
  | none => exact hs
  | some lo =>
    have htrue := maxlevel_eq_tenacity_sub v t lo ht (hs.1 v lo hlo)
    refine ⟨hs.1, ?_⟩
    intro w k hw
    change (if w = v then some (t - lo) else s.maxLabel w) = some k at hw
    split at hw
    next he =>
      have hk := Option.some.inj hw
      simpa only [he, hk] using htrue.2
    next _ => exact hs.2 w k hw

/-- An actual vertex with current tenacity receives its full semantic maxlevel. -/
theorem assignMax_correct (s : State V) (i : Nat) (v : V)
    (hc : MinCompleteBelow M i s) (ht : tenacity M v = some (2 * i + 1)) :
    (assignMax s (2 * i + 1) v).maxLabel v = maxlevel M v := by
  obtain ⟨lo, hlo, hli⟩ := minlevel_le_half_tenacity v i ht
  have hslo := hc v lo hlo hli
  have hh := maxlevel_eq_tenacity_sub v (2 * i + 1) lo ht hlo
  simp [assignMax, hslo, hh.2]

theorem assignMax_minInvariant (s : State V) (i t : Nat) (v : V)
    (hi : MinInvariant M i s) (ht : tenacity M v = some t) :
    MinInvariant M i (assignMax s t v) := by
  have hs := assignMax_labelsSound s t v hi.1 ht
  unfold assignMax at hs ⊢
  cases hlo : s.minLabel v with
  | none => exact hi
  | some lo => exact ⟨by simpa only [hlo] using hs, hi.2⟩

theorem assignMax_preserves_known_maxLabel (s : State V) (t : Nat) (u v : V) (k : Nat)
    (hs : LabelsSound M s) (ht : tenacity M u = some t) (hv : s.maxLabel v = some k) :
    (assignMax s t u).maxLabel v = some k := by
  by_cases he : v = u
  · have hvtrue : maxlevel M v = some k := hs.2 v k hv
    unfold assignMax
    cases hlo : s.minLabel u with
    | none => exact hv
    | some lo =>
      have hh := (maxlevel_eq_tenacity_sub u t lo ht (hs.1 u lo hlo)).2
      rw [he] at hvtrue
      have hk := Option.some.inj (hh.symm.trans hvtrue)
      simp only [he, ite_true, hk]
  · unfold assignMax
    cases hlo : s.minLabel u with
    | none => exact hv
    | some lo => simpa only [he, ite_false] using hv

/-- A vertex in an actual bridge support has precisely the triggering tenacity. -/
theorem assignMax_support_member (s : State V) (i : Nat) (u v w : V)
    (hc : MinCompleteBelow M i s) (he : MaximumMatching.edgeTenacity M u v = some (2 * i + 1))
    (hw : InSupport M u v w) :
    (assignMax s (2 * i + 1) w).maxLabel w = maxlevel M w := by
  obtain ⟨_, t, _, het, hwt, _⟩ := hw
  have ht : t = 2 * i + 1 := Option.some.inj (het.symm.trans he)
  exact assignMax_correct s i w hc (ht ▸ hwt)

/-- Execute the actual assignment for a supplied finite support list. -/
def assignMaxList (t : Nat) (vertices : List V) (s : State V) : State V :=
  vertices.foldl (fun state v => assignMax state t v) s

theorem assignMaxList_minInvariant (s : State V) (i t : Nat) (vs : List V)
    (hi : MinInvariant M i s) (ht : ∀ v ∈ vs, tenacity M v = some t) :
    MinInvariant M i (assignMaxList t vs s) := by
  induction vs generalizing s with
  | nil => exact hi
  | cons v vs ih =>
    exact ih _ (assignMax_minInvariant s i t v hi (ht v (by simp)))
      (fun w hw => ht w (List.mem_cons_of_mem _ hw))

theorem assignMaxList_preserves_known_maxLabel (s : State V) (t : Nat) (vs : List V)
    (hs : LabelsSound M s) (ht : ∀ v ∈ vs, tenacity M v = some t)
    (v : V) (k : Nat) (hv : s.maxLabel v = some k) :
    (assignMaxList t vs s).maxLabel v = some k := by
  induction vs generalizing s with
  | nil => exact hv
  | cons u us ih =>
    exact ih _ (assignMax_labelsSound s t u hs (ht u (by simp)))
      (fun w hw => ht w (List.mem_cons_of_mem _ hw))
      (assignMax_preserves_known_maxLabel s t u v k hs (ht u (by simp)) hv)

/-- Every listed support vertex obtains its semantic maxlevel even when lists
overlap or contain duplicates; assignments to other members cannot destroy it. -/
theorem assignMaxList_member_correct (s : State V) (i : Nat) (vs : List V)
    (hi : MinInvariant M i s) (ht : ∀ v ∈ vs, tenacity M v = some (2 * i + 1))
    (v : V) (hv : v ∈ vs) :
    (assignMaxList (2 * i + 1) vs s).maxLabel v = maxlevel M v := by
  induction vs generalizing s with
  | nil => simp at hv
  | cons u us ih =>
    have hut := ht u (by simp)
    have his := assignMax_minInvariant s i (2 * i + 1) u hi hut
    rcases List.mem_cons.mp hv with he | he
    · subst u
      have hset := assignMax_correct s i v hi.2.1 hut
      obtain ⟨lo, hlo, _⟩ := minlevel_le_half_tenacity v i hut
      have hmax := (maxlevel_eq_tenacity_sub v (2 * i + 1) lo hut hlo).2
      exact (assignMaxList_preserves_known_maxLabel (assignMax s (2 * i + 1) v) (2 * i + 1) us
        his.1 (fun w hw => ht w (List.mem_cons_of_mem _ hw)) v _ (hset.trans hmax)).trans hmax.symm
    · exact ih _ his (fun w hw => ht w (List.mem_cons_of_mem _ hw)) he

end Search
end MaximumMatching

end MaxCorrectness
