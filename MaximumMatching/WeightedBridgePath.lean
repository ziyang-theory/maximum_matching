import MaximumMatching.WeightedTopExpansion

/-! Actual bridge detours after weighted blossom expansion. The lengths below
count edges in the matching graph, including the low-top segments. They do not
identify an assigned DDFS layer with the length of an expanded path. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

namespace ParitySegment

/-- Reverse the free-ending arm, cross one actual bridge edge, and follow the
other arm. Disjointness of the arms proves simplicity, including when an arm
has length zero. The matching status of the bridge fixes its phase. -/
theorem bridge_join_contains (a b : ParitySegment M)
    (hfree : M.Free b.last) (hdis : ∀ i j, b.vertex i ≠ a.vertex j)
    (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1) :
    ∃ z : AltPath M, z.first = b.last ∧ z.last = a.last ∧
      z.length = b.length + 1 + a.length ∧ z.ContainsEdge b.first a.first := by
  have hend : (b.phase + b.length) % 2 = 1 := by
    by_cases hz : b.length = 0
    · have hends : b.first = b.last := congrArg b.vertex (Fin.ext (by omega))
      have hn : ¬(b.phase + 1) % 2 = 1 := by
        intro hp
        have hm := hmatch.mpr hp
        rw [hends, hfree] at hm
        contradiction
      omega
    · have hn : ¬(b.phase + (b.length - 1)) % 2 = 1 := by
        intro hp
        have hm := (b.alternating ⟨b.length - 1, by omega⟩).mpr hp
        have he : b.length - 1 + 1 = b.length := by omega
        simp only [he] at hm
        have hm' := M.symm hm
        change M.mate b.last = some _ at hm'
        rw [hfree] at hm'
        contradiction
      omega
  let e := ofEdge b.first a.first (b.phase + 1) hedge hmatch
  have hp : (b.reverse.phase + b.reverse.length) % 2 = e.phase % 2 := by
    change (b.phase + b.length + 1 + b.length) % 2 = (b.phase + 1) % 2
    omega
  have hj : b.reverse.last = e.first := b.reverse_last
  have hd : ∀ (i : Fin (b.reverse.length + 1)) (j : Fin (e.length + 1)),
      0 < j.val → b.reverse.vertex i ≠ e.vertex j := by
    intro i j hpos he
    have hj1 : j.val = 1 := by have hjb := j.isLt; change j.val < 1 + 1 at hjb; omega
    have he' : b.vertex ⟨b.length - i.val, by have hib := i.isLt; change i.val < b.length + 1 at hib; omega⟩ = a.first := by
      simpa only [e, ofEdge, hj1, Nat.one_ne_zero, ite_false, reverse] using he
    exact hdis _ ⟨0, by omega⟩ he'
  let c := b.reverse.append e hp hj hd
  have hcp : (c.phase + c.length) % 2 = a.phase % 2 := by
    change (b.phase + b.length + 1 + (b.length + 1)) % 2 = a.phase % 2
    omega
  have hcj : c.last = a.first := b.reverse.append_last e hp hj hd
  have hcd : ∀ (i : Fin (c.length + 1)) (j : Fin (a.length + 1)),
      0 < j.val → c.vertex i ≠ a.vertex j := by
    intro i j hpos he
    have hc : c.Contains (a.vertex j) := ⟨i, he⟩
    rcases (b.reverse.contains_append_iff e hp hj hd (a.vertex j)).mp hc with hb | he
    · obtain ⟨k, hk⟩ := (b.contains_reverse_iff _).mp hb
      exact hdis k j hk
    · obtain ⟨k, hk⟩ := he
      by_cases hk0 : k.val = 0
      · have hh : b.first = a.vertex j := by simpa [e, ofEdge, hk0] using hk
        exact hdis ⟨0, by omega⟩ j hh
      · have hh : a.first = a.vertex j := by simpa [e, ofEdge, hk0] using hk
        have hh' := congrArg Fin.val (a.injective ⟨0, by omega⟩ j hh)
        change 0 = j.val at hh'
        omega
  let d := c.append a hcp hcj hcd
  have hdp : d.phase % 2 = 0 := by
    change (b.phase + b.length + 1) % 2 = 0
    omega
  have hdf : d.first = b.last :=
    (c.append_first a hcp hcj hcd).trans ((b.reverse.append_first e hp hj hd).trans b.reverse_first)
  let z := (d.toAltSegment hdp).fromFree (by change M.Free d.first; rw [hdf]; exact hfree)
  refine ⟨z, hdf, c.append_last a hcp hcj hcd, rfl, ?_⟩
  refine ⟨⟨b.length, by change b.length < b.length + 1 + a.length; omega⟩, Or.inl ⟨?_, ?_⟩⟩
  · change d.vertex ⟨b.length, _⟩ = b.first
    simp only [d, append, c, reverse, e, ofEdge, show b.length ≤ b.length + 1 by omega,
      dite_true, Nat.le_refl, Nat.sub_self, first]
  · change d.vertex ⟨b.length + 1, _⟩ = a.first
    simp only [d, append, c, reverse, e, ofEdge, Nat.le_refl, dite_true,
      show ¬b.length + 1 ≤ b.length by omega, dite_false,
      Nat.add_sub_cancel_left, Nat.one_ne_zero, ite_false]

/-- The endpoint-and-length form of the actual bridge construction. -/
theorem bridge_join (a b : ParitySegment M)
    (hfree : M.Free b.last) (hdis : ∀ i j, b.vertex i ≠ a.vertex j)
    (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1) :
    ∃ z : AltPath M, z.first = b.last ∧ z.last = a.last ∧
      z.length = b.length + 1 + a.length := by
  obtain ⟨z, hf, hl, hn, _⟩ := bridge_join_contains a b hfree hdis hphase hedge hmatch
  exact ⟨z, hf, hl, hn⟩

end ParitySegment

namespace DDFS.Path
variable {H : LayeredGraph V}

/-- Extending the opposite arm below the bottleneck cannot meet a path ending
strictly above it. This prepares a root-to-bottleneck arm for continuation to
a free bottom vertex. -/
theorem disjoint_append_below (p q d : Path H) (hjoin : q.last = d.first)
    (hdis : p.Disjoint q) (hbelow : H.level q.last < H.level p.last) :
    p.Disjoint (q.append d hjoin) := by
  intro v hp hqd
  rcases (q.contains_append_iff d hjoin v).mp hqd with hq | hd
  · exact hdis v hp hq
  · have hu := d.level_le_first hd
    have hl := p.last_level_le hp
    rw [← hjoin] at hu
    omega

end DDFS.Path

namespace DDFS.BlossomWeightedMatching
variable {H : LayeredGraph V} {t : Nat}

/-- Weighted bridge detour with actual low-top prefixes. The high-core paths
are disjoint; blossom separation supplies all cross-path freshness after
expansion. Either low-top prefix and either core path may have length zero. -/
theorem bridge_detour (W : BlossomWeightedMatching M H t) (p q : Path H)
    (hp : ∀ v, p.Contains v → levelLT (some t) (tenacity M v))
    (hq : ∀ v, q.Contains v → levelLT (some t) (tenacity M v)) (hdis : p.Disjoint q)
    (a b : ParitySegment M) (ha : a.last = p.first) (hb : b.last = q.first)
    (hap : (a.phase + a.length) % 2 = W.phase p.first % 2)
    (hbp : (b.phase + b.length) % 2 = W.phase q.first % 2)
    (hab : ∀ i : Fin (a.length + 1), i.val < a.length → Blossom M t p.first (a.vertex i))
    (hbb : ∀ i : Fin (b.length + 1), i.val < b.length → Blossom M t q.first (b.vertex i))
    (hfree : M.Free q.last) (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1) :
    ∃ z : AltPath M, z.first = q.last ∧ z.last = p.last ∧
      z.length = (b.length + W.weight q) + 1 + (a.length + W.weight p) := by
  obtain ⟨s, r, hsf, hsl, hsn, hrf, hrl, hrn, hsp, hrp, hsep⟩ :=
    W.realize_disjoint_low_starts p q hp hq hdis a b ha hb hap hbp hab hbb
  obtain ⟨z, hzf, hzl, hzn⟩ := ParitySegment.bridge_join s r
    (hrl.symm ▸ hfree) (fun i j he => hsep j i he.symm)
    (by simpa only [hsp, hrp] using hphase)
    (by simpa only [hsf, hrf] using hedge)
    (by simpa only [hsf, hrf, hrp] using hmatch)
  exact ⟨z, hzf.trans hrl, hzl.trans hsl, by simpa only [hsn, hrn] using hzn⟩

theorem bridge_detour_contains (W : BlossomWeightedMatching M H t) (p q : Path H)
    (hp : ∀ v, p.Contains v → levelLT (some t) (tenacity M v))
    (hq : ∀ v, q.Contains v → levelLT (some t) (tenacity M v)) (hdis : p.Disjoint q)
    (a b : ParitySegment M) (ha : a.last = p.first) (hb : b.last = q.first)
    (hap : (a.phase + a.length) % 2 = W.phase p.first % 2)
    (hbp : (b.phase + b.length) % 2 = W.phase q.first % 2)
    (hab : ∀ i : Fin (a.length + 1), i.val < a.length → Blossom M t p.first (a.vertex i))
    (hbb : ∀ i : Fin (b.length + 1), i.val < b.length → Blossom M t q.first (b.vertex i))
    (hfree : M.Free q.last) (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1) :
    ∃ z : AltPath M, z.first = q.last ∧ z.last = p.last ∧
      z.length = (b.length + W.weight q) + 1 + (a.length + W.weight p) ∧
      z.ContainsEdge b.first a.first := by
  obtain ⟨s, r, hsf, hsl, hsn, hrf, hrl, hrn, hsp, hrp, hsep⟩ :=
    W.realize_disjoint_low_starts p q hp hq hdis a b ha hb hap hbp hab hbb
  obtain ⟨z, hzf, hzl, hzn, hze⟩ := ParitySegment.bridge_join_contains s r
    (hrl.symm ▸ hfree) (fun i j he => hsep j i he.symm)
    (by simpa only [hsp, hrp] using hphase)
    (by simpa only [hsf, hrf] using hedge)
    (by simpa only [hsf, hrf, hrp] using hmatch)
  exact ⟨z, hzf.trans hrl, hzl.trans hsl, by simpa only [hsn, hrn] using hzn,
    by simpa only [hsf, hrf] using hze⟩

/-- Telescope actual edge lengths against a potential, while accounting for
both low-top prefixes separately. In the source application the potential is
finite minlevel, the two prefix-plus-anchor values are the endpoint levels,
and their sum plus the bridge edge is the target tenacity. -/
theorem bridge_detour_of_potential (W : BlossomWeightedMatching M H t) (p q : Path H)
    (hp : ∀ v, p.Contains v → levelLT (some t) (tenacity M v))
    (hq : ∀ v, q.Contains v → levelLT (some t) (tenacity M v)) (hdis : p.Disjoint q)
    (a b : ParitySegment M) (ha : a.last = p.first) (hb : b.last = q.first)
    (hap : (a.phase + a.length) % 2 = W.phase p.first % 2)
    (hbp : (b.phase + b.length) % 2 = W.phase q.first % 2)
    (hab : ∀ i : Fin (a.length + 1), i.val < a.length → Blossom M t p.first (a.vertex i))
    (hbb : ∀ i : Fin (b.length + 1), i.val < b.length → Blossom M t q.first (b.vertex i))
    (hfree : M.Free q.last) (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1)
    (height : V → Nat)
    (hdrop : ∀ {u v} (he : H.Edge u v),
      (W.segment he).length + height v = height u)
    (hzero : height q.last = 0) (budget : Nat)
    (hbudget : (a.length + height p.first) + (b.length + height q.first) + 1 = budget) :
    ∃ z : AltPath M, z.first = q.last ∧ z.last = p.last ∧
      z.length + height p.last = budget ∧ z.length = budget - height p.last := by
  obtain ⟨z, hzf, hzl, hzn⟩ := W.bridge_detour p q hp hq hdis a b ha hb
    hap hbp hab hbb hfree hphase hedge hmatch
  have hpn := W.weight_add_potential height hdrop p
  have hqn := W.weight_add_potential height hdrop q
  exact ⟨z, hzf, hzl, by omega, by omega⟩

theorem bridge_detour_of_potential_contains (W : BlossomWeightedMatching M H t) (p q : Path H)
    (hp : ∀ v, p.Contains v → levelLT (some t) (tenacity M v))
    (hq : ∀ v, q.Contains v → levelLT (some t) (tenacity M v)) (hdis : p.Disjoint q)
    (a b : ParitySegment M) (ha : a.last = p.first) (hb : b.last = q.first)
    (hap : (a.phase + a.length) % 2 = W.phase p.first % 2)
    (hbp : (b.phase + b.length) % 2 = W.phase q.first % 2)
    (hab : ∀ i : Fin (a.length + 1), i.val < a.length → Blossom M t p.first (a.vertex i))
    (hbb : ∀ i : Fin (b.length + 1), i.val < b.length → Blossom M t q.first (b.vertex i))
    (hfree : M.Free q.last) (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1)
    (height : V → Nat)
    (hdrop : ∀ {u v} (he : H.Edge u v),
      (W.segment he).length + height v = height u)
    (hzero : height q.last = 0) (budget : Nat)
    (hbudget : (a.length + height p.first) + (b.length + height q.first) + 1 = budget) :
    ∃ z : AltPath M, z.first = q.last ∧ z.last = p.last ∧
      z.length + height p.last = budget ∧ z.length = budget - height p.last ∧
      z.ContainsEdge b.first a.first := by
  obtain ⟨z, hzf, hzl, hzn, hze⟩ := W.bridge_detour_contains p q hp hq hdis a b ha hb
    hap hbp hab hbb hfree hphase hedge hmatch
  have hpn := W.weight_add_potential height hdrop p
  have hqn := W.weight_add_potential height hdrop q
  exact ⟨z, hzf, hzl, by omega, by omega, hze⟩

end DDFS.BlossomWeightedMatching
end MaximumMatching
