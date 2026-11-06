import MaximumMatching.WeightedExpansion

/-! Weighted paths with a low-tenacity artificial top vertex. The actual
initial segment is kept separate from assigned DDFS layers. Simplicity is
derived by showing that a descending high-core realization never reenters
its first vertex's contracted blossom. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}
namespace DDFS
variable {H : LayeredGraph V} {t : Nat}
namespace BlossomWeightedMatching

private theorem hull_mono {core core' : V → Prop}
    (h : ∀ v, core v → core' v) {v : V} :
    BlossomHull M t core v → BlossomHull M t core' v := by
  rintro (hv | ⟨b, hb, hbl⟩)
  · exact Or.inl (h v hv)
  · exact Or.inr ⟨b, h b hb, hbl⟩

/-- Actual edge lengths telescope against an endpoint potential. The potential
need not equal the assigned DDFS layer; this is needed for artificial top edges. -/
theorem weight_add_potential (W : BlossomWeightedMatching M H t) (height : V → Nat)
    (hdrop : ∀ {u v} (he : H.Edge u v),
      (W.segment he).length + height v = height u) (q : Path H) :
    W.weight q + height q.last = height q.first := by
  by_cases hz : q.length = 0
  · have he : q.last = q.first := congrArg q.vertex (Fin.ext (by omega))
    simp [weight, hz, he]
  · let p := q.take (q.length - 1) (by omega)
    have ih := W.weight_add_potential height hdrop p
    have hd := hdrop (q.last_edge (by omega))
    change (W.segment (q.last_edge (by omega))).length + height q.last = height p.last at hd
    change W.weight p + height p.last = height q.first at ih
    rw [weight, dite_eq_right hz]
    change W.weight p + (W.segment (q.last_edge (by omega))).length + height q.last = _
    omega
termination_by q.length
decreasing_by change q.length - 1 < q.length; omega

/-- A high-core realization avoids the entire blossom attached to its initial
vertex: only targets of descending edges contribute interior blossom vertices. -/
theorem realize_avoiding_initial_blossom (W : BlossomWeightedMatching M H t) (q : Path H)
    (hhigh : ∀ v, q.Contains v → levelLT (some t) (tenacity M v)) :
    ∃ s : ParitySegment M, s.first = q.first ∧ s.last = q.last ∧
      s.length = W.weight q ∧ s.phase % 2 = W.phase q.first % 2 ∧
      (s.phase + s.length) % 2 = W.phase q.last % 2 ∧
      (∀ v, s.Contains v → BlossomHull M t q.Contains v) ∧
      (∀ v, s.Contains v → ¬Blossom M t q.first v) := by
  by_cases hz : q.length = 0
  · let s := ParitySegment.trivial M q.first (W.phase q.first)
    have hq : q.first = q.last := congrArg q.vertex (Fin.ext (by omega))
    refine ⟨s, rfl, hq, ?_, rfl, ?_, ?_, ?_⟩
    · simp [s, weight, hz, ParitySegment.trivial]
    · change (W.phase q.first + 0) % 2 = W.phase q.last % 2
      simp only [Nat.add_zero, hq]
    · rintro v ⟨i, hi⟩
      change q.first = v at hi
      exact Or.inl (hi ▸ q.contains_first)
    · rintro v ⟨i, hi⟩ hbl
      change q.first = v at hi
      obtain ⟨k, hk, hkt⟩ := blossom_tenacity_bound t q.first v hbl
      have hh := hhigh v (hi ▸ q.contains_first)
      rw [hk] at hh
      change t < k at hh
      omega
  · let initial := q.take (q.length - 1) (by omega)
    let he : H.Edge initial.last q.last := q.last_edge (by omega)
    let a := W.segment he
    obtain ⟨s, hsf, hsl, hslen, hsphase, hsend, hshull, hsavoid⟩ := W.realize_avoiding_initial_blossom initial
      (fun v hv => hhigh v (q.contains_take (q.length - 1) (by omega) hv))
    have hjoin : s.last = a.first := hsl.trans (W.first he).symm
    have hphase : (s.phase + s.length) % 2 = a.phase % 2 := hsend.trans (W.start_phase he).symm
    have hcores : ∀ v, ¬(initial.Contains v ∧ v = q.last) := by
      rintro v ⟨⟨i, hi⟩, rfl⟩
      change q.vertex ⟨i.val, _⟩ = q.last at hi
      have hidx := congrArg Fin.val (q.injective _ ⟨q.length, by omega⟩ hi)
      have hib := i.isLt
      change i.val < q.length - 1 + 1 at hib
      dsimp only at hidx
      omega
    have hsep := blossom_hulls_disjoint t initial.Contains (fun v => v = q.last)
      (fun v hv => hhigh v (q.contains_take (q.length - 1) (by omega) hv))
      (fun v hv => hv.symm ▸ hhigh q.last q.contains_last) hcores
    have hdis : ∀ (i : Fin (s.length + 1)) (j : Fin (a.length + 1)),
        0 < j.val → s.vertex i ≠ a.vertex j := by
      intro i j hj hij
      have haj : BlossomHull M t (fun v => v = q.last) (a.vertex j) := by
        by_cases hjl : j.val = a.length
        · exact Or.inl ((congrArg a.vertex (Fin.ext hjl)).trans (W.last he))
        · exact Or.inr ⟨q.last, rfl,
            W.interior he j hj (show j.val < a.length by omega)⟩
      exact hsep (s.vertex i) ⟨hshull (s.vertex i) ⟨i, rfl⟩, hij.symm ▸ haj⟩
    let r := s.append a hphase hjoin hdis
    refine ⟨r, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (s.append_first a hphase hjoin hdis).trans hsf
    · exact (s.append_last a hphase hjoin hdis).trans (W.last he)
    · change s.length + a.length = W.weight q
      rw [weight, dite_eq_right hz, ← hslen]
    · exact hsphase
    · have haend := W.end_phase he
      change (a.phase + a.length) % 2 = W.phase q.last % 2 at haend
      change (s.phase + (s.length + a.length)) % 2 = W.phase q.last % 2
      omega
    · intro v hv
      rcases (s.contains_append_iff a hphase hjoin hdis v).1 hv with hs | ha
      · exact hull_mono (fun _ hv => q.contains_take (q.length - 1) (by omega) hv) (hshull v hs)
      · obtain ⟨i, hi⟩ := ha
        by_cases hi0 : i.val = 0
        · have heq : a.vertex i = initial.last :=
            (congrArg a.vertex (Fin.ext hi0)).trans (W.first he)
          have hh := q.contains_take (q.length - 1) (by omega) initial.contains_last
          exact Or.inl ((hi.symm.trans heq).symm ▸ hh)
        · by_cases hil : i.val = a.length
          · have heq : a.vertex i = q.last :=
              (congrArg a.vertex (Fin.ext hil)).trans (W.last he)
            exact Or.inl ((hi.symm.trans heq).symm ▸ q.contains_last)
          · exact Or.inr ⟨q.last, q.contains_last,
              hi ▸ W.interior he i (by omega) (show i.val < a.length by omega)⟩
    · intro v hv hbl
      rcases (s.contains_append_iff a hphase hjoin hdis v).1 hv with hs | ha
      · exact hsavoid v hs hbl
      · obtain ⟨i, hi⟩ := ha
        by_cases hi0 : i.val = 0
        · have hvhigh := hhigh initial.last
            (q.contains_take (q.length - 1) (by omega) initial.contains_last)
          have heq : a.vertex i = initial.last :=
            (congrArg a.vertex (Fin.ext hi0)).trans (W.first he)
          obtain ⟨k, hk, hkt⟩ := blossom_tenacity_bound t q.first v hbl
          rw [← heq, hi, hk] at hvhigh
          change t < k at hvhigh
          omega
        · by_cases hil : i.val = a.length
          · have hvhigh := hhigh q.last q.contains_last
            have heq : a.vertex i = q.last :=
              (congrArg a.vertex (Fin.ext hil)).trans (W.last he)
            obtain ⟨k, hk, hkt⟩ := blossom_tenacity_bound t q.first v hbl
            rw [← heq, hi, hk] at hvhigh
            change t < k at hvhigh
            omega
          · have hlastne : q.last ≠ q.first := by
              intro heq
              have hidx := congrArg Fin.val (q.injective ⟨q.length, by omega⟩ ⟨0, by omega⟩ heq)
              dsimp only at hidx
              omega
            exact blossoms_disjoint_same_tenacity t q.last q.first
              (hhigh _ q.contains_last) (hhigh _ q.contains_first) hlastne v
              ⟨hi ▸ W.interior he i (by omega) (by change i.val < a.length; omega), hbl⟩
termination_by q.length
decreasing_by change q.length - 1 < q.length; omega

/-- Prepend the actual descending segment from an artificial low top vertex.
The segment may lie in the first core vertex's blossom, which the rest of the
realization provably avoids. No cross-path freshness premise is required. -/
theorem realize_with_low_start (W : BlossomWeightedMatching M H t) (q : Path H)
    (hhigh : ∀ v, q.Contains v → levelLT (some t) (tenacity M v))
    (a : ParitySegment M) (ha : a.last = q.first)
    (hap : (a.phase + a.length) % 2 = W.phase q.first % 2)
    (hab : ∀ i : Fin (a.length + 1), i.val < a.length →
      Blossom M t q.first (a.vertex i)) :
    ∃ s : ParitySegment M, s.first = a.first ∧ s.last = q.last ∧
      s.length = a.length + W.weight q ∧ s.phase = a.phase ∧
      (s.phase + s.length) % 2 = W.phase q.last % 2 ∧
      (∀ v, s.Contains v → BlossomHull M t q.Contains v) := by
  obtain ⟨r, hrf, hrl, hrn, hrp, hre, hrh, hravoid⟩ :=
    W.realize_avoiding_initial_blossom q hhigh
  have hj : a.last = r.first := ha.trans hrf.symm
  have hp : (a.phase + a.length) % 2 = r.phase % 2 := hap.trans hrp.symm
  have hd : ∀ (i : Fin (a.length + 1)) (j : Fin (r.length + 1)),
      0 < j.val → a.vertex i ≠ r.vertex j := by
    intro i j hjp heq
    by_cases hi : i.val < a.length
    · exact hravoid (r.vertex j) ⟨j, rfl⟩ (heq ▸ hab i hi)
    · have hi' : i = ⟨a.length, by omega⟩ := Fin.ext (by change i.val = a.length; have := i.isLt; omega)
      have he : r.first = r.vertex j := hj.symm.trans ((congrArg a.vertex hi').symm.trans heq)
      have hv := congrArg Fin.val (r.injective ⟨0, by omega⟩ j he)
      dsimp only at hv
      omega
  refine ⟨a.append r hp hj hd, (a.append_first r hp hj hd),
    (a.append_last r hp hj hd).trans hrl, by simp [hrn], rfl, ?_, ?_⟩
  · change (a.phase + (a.length + r.length)) % 2 = _
    omega
  · intro v hv
    rcases (a.contains_append_iff r hp hj hd v).1 hv with hav | hrv
    · obtain ⟨i, hi⟩ := hav
      by_cases hil : i.val < a.length
      · exact Or.inr ⟨q.first, q.contains_first, hi ▸ hab i hil⟩
      · have he : i = ⟨a.length, by omega⟩ := Fin.ext (by change i.val = a.length; have := i.isLt; omega)
        have hh : v = q.first := hi.symm.trans ((congrArg a.vertex he).trans ha)
        exact Or.inl (hh.symm ▸ q.contains_first)
    · exact hrh v hrv

/-- Disjoint high-core paths retain disjointness after both actual low-top
segments are prepended. The two top vertices need not have high tenacity. -/
theorem realize_disjoint_low_starts (W : BlossomWeightedMatching M H t) (p q : Path H)
    (hp : ∀ v, p.Contains v → levelLT (some t) (tenacity M v))
    (hq : ∀ v, q.Contains v → levelLT (some t) (tenacity M v)) (hdis : p.Disjoint q)
    (a b : ParitySegment M) (ha : a.last = p.first) (hb : b.last = q.first)
    (hap : (a.phase + a.length) % 2 = W.phase p.first % 2)
    (hbp : (b.phase + b.length) % 2 = W.phase q.first % 2)
    (hab : ∀ i : Fin (a.length + 1), i.val < a.length → Blossom M t p.first (a.vertex i))
    (hbb : ∀ i : Fin (b.length + 1), i.val < b.length → Blossom M t q.first (b.vertex i)) :
    ∃ s r : ParitySegment M,
      s.first = a.first ∧ s.last = p.last ∧ s.length = a.length + W.weight p ∧
      r.first = b.first ∧ r.last = q.last ∧ r.length = b.length + W.weight q ∧
      s.phase = a.phase ∧ r.phase = b.phase ∧ (∀ i j, s.vertex i ≠ r.vertex j) := by
  obtain ⟨s, hsf, hsl, hsn, hsp, _, hsh⟩ := W.realize_with_low_start p hp a ha hap hab
  obtain ⟨r, hrf, hrl, hrn, hrp, _, hrh⟩ := W.realize_with_low_start q hq b hb hbp hbb
  refine ⟨s, r, hsf, hsl, hsn, hrf, hrl, hrn, hsp, hrp, ?_⟩
  intro i j he
  exact blossom_hulls_disjoint t p.Contains q.Contains hp hq
    (fun v h => hdis v h.1 h.2) (s.vertex i)
    ⟨hsh (s.vertex i) ⟨i, rfl⟩, he.symm ▸ hrh (r.vertex j) ⟨j, rfl⟩⟩


end BlossomWeightedMatching
end DDFS
end MaximumMatching
