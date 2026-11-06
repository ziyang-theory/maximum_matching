import MaximumMatching.BudForest
import MaximumMatching.WeightedPaths

section WeightedBridgePath

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
  obtain ⟨z, hzf, hzl, hzn, _, i, hi, hj⟩ :=
    a.bridge_join_relative b hdis hphase hedge hmatch hend
  let p := z.fromFree (by rw [hzf]; exact hfree)
  exact ⟨p, hzf, hzl, hzn, i, Or.inl ⟨hi, hj⟩⟩

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

end WeightedBridgePath

section FiberWeightedExpansion

/-! Weighted path concatenation using actual bud fibers. Distinct current
roots have disjoint fibers by function equality, so this interface applies
to same-level petals without identifying them with mathematical blossoms.
Concrete edge witnesses must still be constructed for each represented fiber. -/
namespace MaximumMatching.DDFS
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G} {H : LayeredGraph V}

/-- Actual matching segments whose interiors remain in the directed target's
current bud fiber. Phases refer to expanded matching paths, not edge counts. -/
structure FiberWeightedMatching (M : Matching G) (H : LayeredGraph V) (F : BudForest V) where
  phase : V → Nat
  segment : ∀ {u v}, H.Edge u v → ParitySegment M
  first : ∀ {u v} (he : H.Edge u v), (segment he).first = u
  last : ∀ {u v} (he : H.Edge u v), (segment he).last = v
  start_phase : ∀ {u v} (he : H.Edge u v), (segment he).phase % 2 = phase u % 2
  end_phase : ∀ {u v} (he : H.Edge u v),
    ((segment he).phase + (segment he).length) % 2 = phase v % 2
  interior : ∀ {u v} (he : H.Edge u v) (i : Fin ((segment he).length + 1)),
    0 < i.val → i.val < (segment he).length → F.root ((segment he).vertex i) = v

namespace FiberWeightedMatching
variable {F : BudForest V}

def weight (W : FiberWeightedMatching M H F) (p : Path H) : Nat :=
  if h : p.length = 0 then 0 else
    W.weight (p.take (p.length - 1) (by omega)) + (W.segment (p.last_edge (by omega))).length
termination_by p.length
decreasing_by simp only [Path.take]; omega

private theorem positive_in_target (W : FiberWeightedMatching M H F) {u v : V}
    (he : H.Edge u v) (hv : F.root v = v) (j : Fin ((W.segment he).length + 1))
    (hj : 0 < j.val) : F.root ((W.segment he).vertex j) = v := by
  by_cases heq : j.val = (W.segment he).length
  · have hjeq : j = ⟨(W.segment he).length, by omega⟩ := Fin.ext heq
    have hlast : (W.segment he).vertex j = v := (congrArg (W.segment he).vertex hjeq).trans (W.last he)
    rw [hlast]
    exact hv
  · exact W.interior he j hj (by have := j.isLt; omega)

/-- Realize a path of fixed roots. Every expanded vertex remains in a fiber
of that path, and only the initial vertex lies in its own initial fiber. -/
theorem realize (W : FiberWeightedMatching M H F) (p : Path H)
    (hfixed : ∀ v, p.Contains v → F.root v = v) :
    ∃ s : ParitySegment M, s.first = p.first ∧ s.last = p.last ∧
      s.length = W.weight p ∧ s.phase % 2 = W.phase p.first % 2 ∧
      (s.phase + s.length) % 2 = W.phase p.last % 2 ∧
      (∀ v, s.Contains v → p.Contains (F.root v)) ∧
      (∀ v, s.Contains v → F.root v = p.first → v = p.first) := by
  by_cases hz : p.length = 0
  · have hends : p.first = p.last := congrArg p.vertex (Fin.ext (by omega))
    refine ⟨ParitySegment.trivial M p.first (W.phase p.first), rfl, hends, ?_, rfl, ?_, ?_, ?_⟩
    · rw [weight, dite_eq_left hz]
      rfl
    · change (W.phase p.first + 0) % 2 = W.phase p.last % 2
      simp only [Nat.add_zero, hends]
    · rintro v ⟨i, hi⟩
      change p.first = v at hi
      rw [← hi, hfixed p.first p.contains_first]
      exact p.contains_first
    · rintro v ⟨i, hi⟩ _
      exact hi.symm
  · let q := p.take (p.length - 1) (by omega)
    let he : H.Edge q.last p.last := p.last_edge (by omega)
    let a := W.segment he
    obtain ⟨s, hsf, hsl, hsn, hsp, hse, hsh, hsa⟩ := W.realize q
      (fun v hv => hfixed v (p.contains_take _ _ hv))
    have hj : s.last = a.first := hsl.trans (W.first he).symm
    have hp : (s.phase + s.length) % 2 = a.phase % 2 := hse.trans (W.start_phase he).symm
    have hnotlast : ∀ v, q.Contains v → v ≠ p.last := by
      rintro v ⟨i, hi⟩ hlast
      have heq := p.injective ⟨i.val, by have := i.isLt; change i.val < p.length - 1 + 1 at this; omega⟩
        ⟨p.length, by omega⟩ (hi.trans hlast)
      have hn := congrArg Fin.val heq
      have := i.isLt
      change i.val < p.length - 1 + 1 at this
      dsimp only at hn
      omega
    have hd : ∀ (i : Fin (s.length + 1)) (j : Fin (a.length + 1)),
        0 < j.val → s.vertex i ≠ a.vertex j := by
      intro i j hjp hij
      have hroot := W.positive_in_target he (hfixed p.last p.contains_last) j hjp
      have hsroot := hsh (s.vertex i) ⟨i, rfl⟩
      rw [hij, hroot] at hsroot
      exact hnotlast p.last hsroot rfl
    let r := s.append a hp hj hd
    refine ⟨r, (s.append_first a hp hj hd).trans hsf,
      (s.append_last a hp hj hd).trans (W.last he), ?_, hsp, ?_, ?_, ?_⟩
    · change s.length + a.length = W.weight p
      rw [weight, dite_eq_right hz, ← hsn]
    · have hae := W.end_phase he
      change (a.phase + a.length) % 2 = W.phase p.last % 2 at hae
      change (s.phase + (s.length + a.length)) % 2 = W.phase p.last % 2
      omega
    · intro v hv
      rcases (s.contains_append_iff a hp hj hd v).1 hv with hs | ha
      · exact p.contains_take _ _ (hsh v hs)
      · obtain ⟨i, hi⟩ := ha
        by_cases hi0 : i.val = 0
        · have hvi : v = q.last := hi.symm.trans ((congrArg a.vertex (Fin.ext hi0)).trans (W.first he))
          rw [hvi, hfixed q.last (p.contains_take _ _ q.contains_last)]
          exact p.contains_take _ _ q.contains_last
        · have hr := W.positive_in_target he (hfixed p.last p.contains_last) i (by omega)
          rw [hi] at hr
          rw [hr]
          exact p.contains_last
    · intro v hv hroot
      rcases (s.contains_append_iff a hp hj hd v).1 hv with hs | ha
      · exact hsa v hs hroot
      · obtain ⟨i, hi⟩ := ha
        by_cases hi0 : i.val = 0
        · have hvi : v = q.last := hi.symm.trans ((congrArg a.vertex (Fin.ext hi0)).trans (W.first he))
          have hvfix : F.root v = v := by rw [hvi]; exact hfixed q.last (p.contains_take _ _ q.contains_last)
          exact hvfix.symm.trans hroot
        · have hr := W.positive_in_target he (hfixed p.last p.contains_last) i (by omega)
          rw [hi, hroot] at hr
          exact False.elim (hnotlast p.first q.contains_first hr)
termination_by p.length
decreasing_by change p.length - 1 < p.length; omega

/-- Actual edge lengths telescope against any valid endpoint potential. -/
theorem weight_add_potential (W : FiberWeightedMatching M H F) (height : V → Nat)
    (hdrop : ∀ {u v} (he : H.Edge u v), (W.segment he).length + height v = height u)
    (p : Path H) : W.weight p + height p.last = height p.first := by
  by_cases hz : p.length = 0
  · have he : p.last = p.first := congrArg p.vertex (Fin.ext (by omega))
    rw [weight, dite_eq_left hz]
    simp only [Nat.zero_add, he]
  · let q := p.take (p.length - 1) (by omega)
    have ih := W.weight_add_potential height hdrop q
    have hd := hdrop (p.last_edge (by omega))
    change W.weight q + height q.last = height p.first at ih
    change (W.segment (p.last_edge (by omega))).length + height p.last = height q.last at hd
    rw [weight, dite_eq_right hz]
    change W.weight q + (W.segment (p.last_edge (by omega))).length + height p.last = _
    omega
termination_by p.length
decreasing_by change p.length - 1 < p.length; omega

/-- Attach an actual endpoint-to-root segment lying in the initial fiber.
The realized core only meets that fiber at its initial root. -/
theorem realize_with_start (W : FiberWeightedMatching M H F) (p : Path H)
    (hfixed : ∀ v, p.Contains v → F.root v = v)
    (a : ParitySegment M) (ha : a.last = p.first)
    (hap : (a.phase + a.length) % 2 = W.phase p.first % 2)
    (haf : ∀ i : Fin (a.length + 1), i.val < a.length → F.root (a.vertex i) = p.first) :
    ∃ s : ParitySegment M, s.first = a.first ∧ s.last = p.last ∧
      s.length = a.length + W.weight p ∧ s.phase = a.phase ∧
      (s.phase + s.length) % 2 = W.phase p.last % 2 ∧
      (∀ v, s.Contains v → p.Contains (F.root v)) := by
  obtain ⟨r, hrf, hrl, hrn, hrp, hre, hrh, hravoid⟩ := W.realize p hfixed
  have hj : a.last = r.first := ha.trans hrf.symm
  have hp : (a.phase + a.length) % 2 = r.phase % 2 := hap.trans hrp.symm
  have hd : ∀ (i : Fin (a.length + 1)) (j : Fin (r.length + 1)),
      0 < j.val → a.vertex i ≠ r.vertex j := by
    intro i j hjp hij
    have hfirst : r.vertex j = r.first := by
      by_cases hi : i.val < a.length
      · have hrroot : F.root (r.vertex j) = p.first := hij ▸ haf i hi
        exact (hravoid (r.vertex j) ⟨j, rfl⟩ hrroot).trans hrf.symm
      · have hi' : i = ⟨a.length, by omega⟩ := Fin.ext (by change i.val = a.length; have := i.isLt; omega)
        exact hij.symm.trans ((congrArg a.vertex hi').trans hj)
    have he := congrArg Fin.val (r.injective j ⟨0, by omega⟩ hfirst)
    dsimp only at he
    omega
  refine ⟨a.append r hp hj hd, a.append_first r hp hj hd,
    (a.append_last r hp hj hd).trans hrl, by simp only [ParitySegment.append_length, hrn], rfl, ?_, ?_⟩
  · change (a.phase + (a.length + r.length)) % 2 = W.phase p.last % 2
    omega
  · intro v hv
    rcases (a.contains_append_iff r hp hj hd v).1 hv with ha' | hr
    · obtain ⟨i, hi⟩ := ha'
      have hroot : F.root (a.vertex i) = p.first := by
        by_cases hi' : i.val < a.length
        · exact haf i hi'
        · have he : i = ⟨a.length, by omega⟩ := Fin.ext (by change i.val = a.length; have := i.isLt; omega)
          rw [he]
          change F.root a.last = p.first
          rw [ha, hfixed p.first p.contains_first]
      rw [hi] at hroot
      rw [hroot]
      exact p.contains_first
    · exact hrh v hr

/-- Disjoint current-root paths expand to disjoint original-vertex paths,
including arbitrary initial segments contained in their respective fibers. -/
theorem realize_disjoint_starts (W : FiberWeightedMatching M H F) (p q : Path H)
    (hp : ∀ v, p.Contains v → F.root v = v) (hq : ∀ v, q.Contains v → F.root v = v)
    (hdis : p.Disjoint q) (a b : ParitySegment M) (ha : a.last = p.first) (hb : b.last = q.first)
    (hap : (a.phase + a.length) % 2 = W.phase p.first % 2)
    (hbp : (b.phase + b.length) % 2 = W.phase q.first % 2)
    (haf : ∀ i : Fin (a.length + 1), i.val < a.length → F.root (a.vertex i) = p.first)
    (hbf : ∀ i : Fin (b.length + 1), i.val < b.length → F.root (b.vertex i) = q.first) :
    ∃ s r : ParitySegment M,
      s.first = a.first ∧ s.last = p.last ∧ s.length = a.length + W.weight p ∧
      r.first = b.first ∧ r.last = q.last ∧ r.length = b.length + W.weight q ∧
      s.phase = a.phase ∧ r.phase = b.phase ∧ (∀ i j, s.vertex i ≠ r.vertex j) := by
  obtain ⟨s, hsf, hsl, hsn, hsp, _, hsh⟩ := W.realize_with_start p hp a ha hap haf
  obtain ⟨r, hrf, hrl, hrn, hrp, _, hrh⟩ := W.realize_with_start q hq b hb hbp hbf
  refine ⟨s, r, hsf, hsl, hsn, hrf, hrl, hrn, hsp, hrp, ?_⟩
  intro i j he
  exact hdis (F.root (s.vertex i)) (hsh (s.vertex i) ⟨i, rfl⟩)
    (by rw [he]; exact hrh (r.vertex j) ⟨j, rfl⟩)

/-- Cross a real bridge between two expanded fiber-disjoint core paths. -/
theorem bridge_detour_contains (W : FiberWeightedMatching M H F) (p q : Path H)
    (hp : ∀ v, p.Contains v → F.root v = v) (hq : ∀ v, q.Contains v → F.root v = v)
    (hdis : p.Disjoint q) (a b : ParitySegment M) (ha : a.last = p.first) (hb : b.last = q.first)
    (hap : (a.phase + a.length) % 2 = W.phase p.first % 2)
    (hbp : (b.phase + b.length) % 2 = W.phase q.first % 2)
    (haf : ∀ i : Fin (a.length + 1), i.val < a.length → F.root (a.vertex i) = p.first)
    (hbf : ∀ i : Fin (b.length + 1), i.val < b.length → F.root (b.vertex i) = q.first)
    (hfree : M.Free q.last) (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1) :
    ∃ z : AltPath M, z.first = q.last ∧ z.last = p.last ∧
      z.length = (b.length + W.weight q) + 1 + (a.length + W.weight p) ∧
      z.ContainsEdge b.first a.first := by
  obtain ⟨s, r, hsf, hsl, hsn, hrf, hrl, hrn, hsp, hrp, hsep⟩ :=
    W.realize_disjoint_starts p q hp hq hdis a b ha hb hap hbp haf hbf
  obtain ⟨z, hzf, hzl, hzn, hze⟩ := ParitySegment.bridge_join_contains s r
    (hrl.symm ▸ hfree) (fun i j he => hsep j i he.symm)
    (by simpa only [hsp, hrp] using hphase)
    (by simpa only [hsf, hrf] using hedge)
    (by simpa only [hsf, hrf, hrp] using hmatch)
  exact ⟨z, hzf.trans hrl, hzl.trans hsl, by simpa only [hsn, hrn] using hzn,
    by simpa only [hsf, hrf] using hze⟩

/-- Fiber-based bridge lifting with an exact expanded-length budget. -/
theorem bridge_detour_of_potential_contains (W : FiberWeightedMatching M H F) (p q : Path H)
    (hp : ∀ v, p.Contains v → F.root v = v) (hq : ∀ v, q.Contains v → F.root v = v)
    (hdis : p.Disjoint q) (a b : ParitySegment M) (ha : a.last = p.first) (hb : b.last = q.first)
    (hap : (a.phase + a.length) % 2 = W.phase p.first % 2)
    (hbp : (b.phase + b.length) % 2 = W.phase q.first % 2)
    (haf : ∀ i : Fin (a.length + 1), i.val < a.length → F.root (a.vertex i) = p.first)
    (hbf : ∀ i : Fin (b.length + 1), i.val < b.length → F.root (b.vertex i) = q.first)
    (hfree : M.Free q.last) (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1)
    (height : V → Nat)
    (hdrop : ∀ {u v} (he : H.Edge u v), (W.segment he).length + height v = height u)
    (hzero : height q.last = 0) (budget : Nat)
    (hbudget : (a.length + height p.first) + (b.length + height q.first) + 1 = budget) :
    ∃ z : AltPath M, z.first = q.last ∧ z.last = p.last ∧
      z.length + height p.last = budget ∧ z.length = budget - height p.last ∧
      z.ContainsEdge b.first a.first := by
  obtain ⟨z, hzf, hzl, hzn, hze⟩ := W.bridge_detour_contains p q hp hq hdis a b ha hb
    hap hbp haf hbf hfree hphase hedge hmatch
  have hpn := W.weight_add_potential height hdrop p
  have hqn := W.weight_add_potential height hdrop q
  exact ⟨z, hzf, hzl, by omega, by omega, hze⟩

end FiberWeightedMatching
end MaximumMatching.DDFS

end FiberWeightedExpansion

section ParityBridgeRecovery

/-! Executable bridge joins. The vertex sequence is built by reversing one
supplied arm, inserting the actual bridge edge, and appending the other arm;
all simplicity, phase, and coverage certificates are erased proofs. -/
namespace MaximumMatching.ParitySegment
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Construct the actual relative bridge detour without a free-boundary
hypothesis and without choosing a semantic path witness. -/
def recoverBridgeJoinExact (a b : ParitySegment M)
    (hdis : ∀ i j, b.vertex i ≠ a.vertex j)
    (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1) :
    { z : ParitySegment M // z.first = b.last ∧ z.last = a.last ∧
      z.length = b.length + 1 + a.length ∧
      z.phase = b.phase + b.length + 1 ∧
      (∀ w, z.Contains w ↔ a.Contains w ∨ b.Contains w) ∧
      ∃ i : Fin z.length, z.vertex ⟨i.val, by omega⟩ = b.first ∧
        z.vertex ⟨i.val + 1, by omega⟩ = a.first } := by
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
  have hdf : d.first = b.last :=
    (c.append_first a hcp hcj hcd).trans ((b.reverse.append_first e hp hj hd).trans b.reverse_first)
  refine ⟨d, hdf, c.append_last a hcp hcj hcd, rfl, rfl, ?_, ?_⟩
  · intro w
    constructor
    · intro hw
      rcases (c.contains_append_iff a hcp hcj hcd w).1 hw with hcw | haw
      · rcases (b.reverse.contains_append_iff e hp hj hd w).1 hcw with hbw | hew
        · exact Or.inr ((b.contains_reverse_iff w).1 hbw)
        · obtain ⟨i, hi⟩ := hew
          by_cases hz : i.val = 0
          · have hbw : b.first = w := by simpa only [e, ofEdge, hz, ite_true] using hi
            exact Or.inr ⟨⟨0, by omega⟩, hbw⟩
          · have haw : a.first = w := by simpa only [e, ofEdge, hz, ite_false] using hi
            exact Or.inl ⟨⟨0, by omega⟩, haw⟩
      · exact Or.inl haw
    · intro hw
      apply (c.contains_append_iff a hcp hcj hcd w).2
      rcases hw with haw | hbw
      · exact Or.inr haw
      · exact Or.inl ((b.reverse.contains_append_iff e hp hj hd w).2
          (Or.inl ((b.contains_reverse_iff w).2 hbw)))
  · refine ⟨⟨b.length, by change b.length < b.length + 1 + a.length; omega⟩, ?_, ?_⟩
    · change d.vertex ⟨b.length, _⟩ = b.first
      simp only [d, append, c, reverse, e, ofEdge, show b.length ≤ b.length + 1 by omega,
        dite_true, Nat.le_refl, Nat.sub_self, first]
    · change d.vertex ⟨b.length + 1, _⟩ = a.first
      simp only [d, append, c, reverse, e, ofEdge, Nat.le_refl, dite_true,
        show ¬b.length + 1 ≤ b.length by omega, dite_false,
        Nat.add_sub_cancel_left, Nat.one_ne_zero, ite_false]

/-- Compatibility interface for the same computed bridge join. -/
def recoverBridgeJoin (a b : ParitySegment M)
    (hdis : ∀ i j, b.vertex i ≠ a.vertex j)
    (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1) :
    { z : ParitySegment M // z.first = b.last ∧ z.last = a.last ∧
      z.length = b.length + 1 + a.length ∧
      z.phase = b.phase + b.length + 1 ∧
      (∀ w, z.Contains w → a.Contains w ∨ b.Contains w) ∧
      ∃ i : Fin z.length, z.vertex ⟨i.val, by omega⟩ = b.first ∧
        z.vertex ⟨i.val + 1, by omega⟩ = a.first } := by
  let z := a.recoverBridgeJoinExact b hdis hphase hedge hmatch
  exact ⟨z.val, z.property.1, z.property.2.1, z.property.2.2.1,
    z.property.2.2.2.1, fun w hw => (z.property.2.2.2.2.1 w).1 hw,
    z.property.2.2.2.2.2⟩

/-- The same computed bridge join is an alternating path when its starting
boundary is free. -/
def recoverBridgeJoinFreeExact (a b : ParitySegment M)
    (hfree : M.Free b.last) (hdis : ∀ i j, b.vertex i ≠ a.vertex j)
    (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1) :
    { z : AltPath M // z.first = b.last ∧ z.last = a.last ∧
      z.length = b.length + 1 + a.length ∧ z.ContainsEdge b.first a.first ∧
      (∀ w, (∃ i, z.vertex i = w) ↔ a.Contains w ∨ b.Contains w) } := by
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
  obtain ⟨z, hzf, hzl, hzn, hzp, hcover, hbridge⟩ :=
    a.recoverBridgeJoinExact b hdis hphase hedge hmatch
  have hzero : z.phase % 2 = 0 := by rw [hzp]; omega
  let p := (z.toAltSegment hzero).fromFree (by change M.Free z.first; rw [hzf]; exact hfree)
  refine ⟨p, hzf, hzl, hzn, ?_, hcover⟩
  obtain ⟨i, hi, hj⟩ := hbridge
  exact ⟨i, Or.inl ⟨hi, hj⟩⟩

/-- Compatibility interface for the same computed free-boundary join. -/
def recoverBridgeJoinFree (a b : ParitySegment M)
    (hfree : M.Free b.last) (hdis : ∀ i j, b.vertex i ≠ a.vertex j)
    (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1) :
    { z : AltPath M // z.first = b.last ∧ z.last = a.last ∧
      z.length = b.length + 1 + a.length ∧ z.ContainsEdge b.first a.first } := by
  let z := a.recoverBridgeJoinFreeExact b hfree hdis hphase hedge hmatch
  exact ⟨z.val, z.property.1, z.property.2.1, z.property.2.2.1, z.property.2.2.2.1⟩

end MaximumMatching.ParitySegment

end ParityBridgeRecovery

section FiberWeightedRecovery

/-! Computable recovery from actual weighted fiber segments. These functions
retain witnesses in Type and use only the supplied segment data, directed-path
operations and simple concatenation; their certificates are erased proofs. -/
namespace MaximumMatching.DDFS.FiberWeightedMatching
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}
    {H : LayeredGraph V} {F : BudForest V}

private theorem recover_positive_in_target (W : FiberWeightedMatching M H F) {u v : V}
    (he : H.Edge u v) (hv : F.root v = v) (j : Fin ((W.segment he).length + 1))
    (hj : 0 < j.val) : F.root ((W.segment he).vertex j) = v := by
  by_cases heq : j.val = (W.segment he).length
  · have hjeq : j = ⟨(W.segment he).length, by omega⟩ := Fin.ext heq
    have hlast : (W.segment he).vertex j = v := (congrArg (W.segment he).vertex hjeq).trans (W.last he)
    rw [hlast]
    exact hv
  · exact W.interior he j hj (by have := j.isLt; omega)

/-- Realize a path of fixed roots. Every expanded vertex remains in a fiber
of that path, and only the initial vertex lies in its own initial fiber. -/
def recoverPathWithCore (W : FiberWeightedMatching M H F) (p : Path H)
    (hfixed : ∀ v, p.Contains v → F.root v = v) :
    { s : ParitySegment M // s.first = p.first ∧ s.last = p.last ∧
      s.length = W.weight p ∧ s.phase % 2 = W.phase p.first % 2 ∧
      (s.phase + s.length) % 2 = W.phase p.last % 2 ∧
      (∀ v, s.Contains v → p.Contains (F.root v)) ∧
      (∀ v, s.Contains v → F.root v = p.first → v = p.first) ∧
      (∀ v, p.Contains v → s.Contains v) } := by
  by_cases hz : p.length = 0
  · have hends : p.first = p.last := congrArg p.vertex (Fin.ext (by omega))
    refine ⟨ParitySegment.trivial M p.first (W.phase p.first), rfl, hends, ?_, rfl, ?_, ?_, ?_, ?_⟩
    · rw [weight, dite_eq_left hz]
      rfl
    · change (W.phase p.first + 0) % 2 = W.phase p.last % 2
      simp only [Nat.add_zero, hends]
    · rintro v ⟨i, hi⟩
      change p.first = v at hi
      rw [← hi, hfixed p.first p.contains_first]
      exact p.contains_first
    · rintro v ⟨i, hi⟩ _
      exact hi.symm
    · rintro v ⟨i, hi⟩
      refine ⟨⟨0, by omega⟩, ?_⟩
      have hie : i = ⟨0, by omega⟩ := Fin.ext (by have := i.isLt; omega)
      exact (congrArg p.vertex hie).symm.trans hi
  · let q := p.take (p.length - 1) (by omega)
    let he : H.Edge q.last p.last := p.last_edge (by omega)
    let a := W.segment he
    obtain ⟨s, hsf, hsl, hsn, hsp, hse, hsh, hsa, hcore⟩ := W.recoverPathWithCore q
      (fun v hv => hfixed v (p.contains_take _ _ hv))
    have hj : s.last = a.first := hsl.trans (W.first he).symm
    have hp : (s.phase + s.length) % 2 = a.phase % 2 := hse.trans (W.start_phase he).symm
    have hnotlast : ∀ v, q.Contains v → v ≠ p.last := by
      rintro v ⟨i, hi⟩ hlast
      have heq := p.injective ⟨i.val, by have := i.isLt; change i.val < p.length - 1 + 1 at this; omega⟩
        ⟨p.length, by omega⟩ (hi.trans hlast)
      have hn := congrArg Fin.val heq
      have := i.isLt
      change i.val < p.length - 1 + 1 at this
      dsimp only at hn
      omega
    have hd : ∀ (i : Fin (s.length + 1)) (j : Fin (a.length + 1)),
        0 < j.val → s.vertex i ≠ a.vertex j := by
      intro i j hjp hij
      have hroot := W.recover_positive_in_target he (hfixed p.last p.contains_last) j hjp
      have hsroot := hsh (s.vertex i) ⟨i, rfl⟩
      rw [hij, hroot] at hsroot
      exact hnotlast p.last hsroot rfl
    let r := s.append a hp hj hd
    refine ⟨r, (s.append_first a hp hj hd).trans hsf,
      (s.append_last a hp hj hd).trans (W.last he), ?_, hsp, ?_, ?_, ?_, ?_⟩
    · change s.length + a.length = W.weight p
      rw [weight, dite_eq_right hz, ← hsn]
    · have hae := W.end_phase he
      change (a.phase + a.length) % 2 = W.phase p.last % 2 at hae
      change (s.phase + (s.length + a.length)) % 2 = W.phase p.last % 2
      omega
    · intro v hv
      rcases (s.contains_append_iff a hp hj hd v).1 hv with hs | ha
      · exact p.contains_take _ _ (hsh v hs)
      · obtain ⟨i, hi⟩ := ha
        by_cases hi0 : i.val = 0
        · have hvi : v = q.last := hi.symm.trans ((congrArg a.vertex (Fin.ext hi0)).trans (W.first he))
          rw [hvi, hfixed q.last (p.contains_take _ _ q.contains_last)]
          exact p.contains_take _ _ q.contains_last
        · have hr := W.recover_positive_in_target he (hfixed p.last p.contains_last) i (by omega)
          rw [hi] at hr
          rw [hr]
          exact p.contains_last
    · intro v hv hroot
      rcases (s.contains_append_iff a hp hj hd v).1 hv with hs | ha
      · exact hsa v hs hroot
      · obtain ⟨i, hi⟩ := ha
        by_cases hi0 : i.val = 0
        · have hvi : v = q.last := hi.symm.trans ((congrArg a.vertex (Fin.ext hi0)).trans (W.first he))
          have hvfix : F.root v = v := by rw [hvi]; exact hfixed q.last (p.contains_take _ _ q.contains_last)
          exact hvfix.symm.trans hroot
        · have hr := W.recover_positive_in_target he (hfixed p.last p.contains_last) i (by omega)
          rw [hi, hroot] at hr
          exact False.elim (hnotlast p.first q.contains_first hr)
    · rintro v ⟨i, hi⟩
      apply (s.contains_append_iff a hp hj hd v).2
      by_cases hilast : i.val = p.length
      · right
        refine ⟨⟨a.length, by omega⟩, ?_⟩
        exact (W.last he).trans ((congrArg p.vertex (Fin.ext hilast)).symm.trans hi)
      · left
        exact hcore v ⟨⟨i.val, by change i.val < p.length - 1 + 1; have := i.isLt; omega⟩, hi⟩
termination_by p.length
decreasing_by change p.length - 1 < p.length; omega

/-- Compatibility interface for the same computed recovery. -/
def recoverPath (W : FiberWeightedMatching M H F) (p : Path H)
    (hfixed : ∀ v, p.Contains v → F.root v = v) :
    { s : ParitySegment M // s.first = p.first ∧ s.last = p.last ∧
      s.length = W.weight p ∧ s.phase % 2 = W.phase p.first % 2 ∧
      (s.phase + s.length) % 2 = W.phase p.last % 2 ∧
      (∀ v, s.Contains v → p.Contains (F.root v)) ∧
      (∀ v, s.Contains v → F.root v = p.first → v = p.first) } := by
  let z := W.recoverPathWithCore p hfixed
  exact ⟨z.val, z.property.1, z.property.2.1, z.property.2.2.1,
    z.property.2.2.2.1, z.property.2.2.2.2.1, z.property.2.2.2.2.2.1,
    z.property.2.2.2.2.2.2.1⟩

/-- Attach an actual endpoint-to-root segment lying in the initial fiber.
The realized core only meets that fiber at its initial root. -/
def recoverPathWithStartAndCore (W : FiberWeightedMatching M H F) (p : Path H)
    (hfixed : ∀ v, p.Contains v → F.root v = v)
    (a : ParitySegment M) (ha : a.last = p.first)
    (hap : (a.phase + a.length) % 2 = W.phase p.first % 2)
    (haf : ∀ i : Fin (a.length + 1), i.val < a.length → F.root (a.vertex i) = p.first) :
    { s : ParitySegment M // s.first = a.first ∧ s.last = p.last ∧
      s.length = a.length + W.weight p ∧ s.phase = a.phase ∧
      (s.phase + s.length) % 2 = W.phase p.last % 2 ∧
      (∀ v, s.Contains v → p.Contains (F.root v)) ∧
      (∀ v, p.Contains v → s.Contains v) } := by
  obtain ⟨r, hrf, hrl, hrn, hrp, hre, hrh, hravoid, hrcore⟩ := W.recoverPathWithCore p hfixed
  have hj : a.last = r.first := ha.trans hrf.symm
  have hp : (a.phase + a.length) % 2 = r.phase % 2 := hap.trans hrp.symm
  have hd : ∀ (i : Fin (a.length + 1)) (j : Fin (r.length + 1)),
      0 < j.val → a.vertex i ≠ r.vertex j := by
    intro i j hjp hij
    have hfirst : r.vertex j = r.first := by
      by_cases hi : i.val < a.length
      · have hrroot : F.root (r.vertex j) = p.first := hij ▸ haf i hi
        exact (hravoid (r.vertex j) ⟨j, rfl⟩ hrroot).trans hrf.symm
      · have hi' : i = ⟨a.length, by omega⟩ := Fin.ext (by change i.val = a.length; have := i.isLt; omega)
        exact hij.symm.trans ((congrArg a.vertex hi').trans hj)
    have he := congrArg Fin.val (r.injective j ⟨0, by omega⟩ hfirst)
    dsimp only at he
    omega
  refine ⟨a.append r hp hj hd, a.append_first r hp hj hd,
    (a.append_last r hp hj hd).trans hrl, by simp only [ParitySegment.append_length, hrn], rfl, ?_, ?_, ?_⟩
  · change (a.phase + (a.length + r.length)) % 2 = W.phase p.last % 2
    omega
  · intro v hv
    rcases (a.contains_append_iff r hp hj hd v).1 hv with ha' | hr
    · obtain ⟨i, hi⟩ := ha'
      have hroot : F.root (a.vertex i) = p.first := by
        by_cases hi' : i.val < a.length
        · exact haf i hi'
        · have he : i = ⟨a.length, by omega⟩ := Fin.ext (by change i.val = a.length; have := i.isLt; omega)
          rw [he]
          change F.root a.last = p.first
          rw [ha, hfixed p.first p.contains_first]
      rw [hi] at hroot
      rw [hroot]
      exact p.contains_first
    · exact hrh v hr

  · intro v hv
    exact (a.contains_append_iff r hp hj hd v).2 (Or.inr (hrcore v hv))

/-- Compatibility interface retaining the computed segment and old guarantees. -/
def recoverPathWithStart (W : FiberWeightedMatching M H F) (p : Path H)
    (hfixed : ∀ v, p.Contains v → F.root v = v)
    (a : ParitySegment M) (ha : a.last = p.first)
    (hap : (a.phase + a.length) % 2 = W.phase p.first % 2)
    (haf : ∀ i : Fin (a.length + 1), i.val < a.length → F.root (a.vertex i) = p.first) :
    { s : ParitySegment M // s.first = a.first ∧ s.last = p.last ∧
      s.length = a.length + W.weight p ∧ s.phase = a.phase ∧
      (s.phase + s.length) % 2 = W.phase p.last % 2 ∧
      (∀ v, s.Contains v → p.Contains (F.root v)) } := by
  let z := W.recoverPathWithStartAndCore p hfixed a ha hap haf
  exact ⟨z.val, z.property.1, z.property.2.1, z.property.2.2.1,
    z.property.2.2.2.1, z.property.2.2.2.2.1, z.property.2.2.2.2.2.1⟩

/-- Disjoint current-root paths expand to disjoint original-vertex paths,
including arbitrary initial segments contained in their respective fibers. -/
def recoverDisjointStarts (W : FiberWeightedMatching M H F) (p q : Path H)
    (hp : ∀ v, p.Contains v → F.root v = v) (hq : ∀ v, q.Contains v → F.root v = v)
    (hdis : p.Disjoint q) (a b : ParitySegment M) (ha : a.last = p.first) (hb : b.last = q.first)
    (hap : (a.phase + a.length) % 2 = W.phase p.first % 2)
    (hbp : (b.phase + b.length) % 2 = W.phase q.first % 2)
    (haf : ∀ i : Fin (a.length + 1), i.val < a.length → F.root (a.vertex i) = p.first)
    (hbf : ∀ i : Fin (b.length + 1), i.val < b.length → F.root (b.vertex i) = q.first) :
    Σ s : ParitySegment M, { r : ParitySegment M //
      s.first = a.first ∧ s.last = p.last ∧ s.length = a.length + W.weight p ∧
      r.first = b.first ∧ r.last = q.last ∧ r.length = b.length + W.weight q ∧
      s.phase = a.phase ∧ r.phase = b.phase ∧ (∀ i j, s.vertex i ≠ r.vertex j) } := by
  obtain ⟨s, hsf, hsl, hsn, hsp, _, hsh⟩ := W.recoverPathWithStart p hp a ha hap haf
  obtain ⟨r, hrf, hrl, hrn, hrp, _, hrh⟩ := W.recoverPathWithStart q hq b hb hbp hbf
  refine ⟨s, r, hsf, hsl, hsn, hrf, hrl, hrn, hsp, hrp, ?_⟩
  intro i j he
  exact hdis (F.root (s.vertex i)) (hsh (s.vertex i) ⟨i, rfl⟩)
    (by rw [he]; exact hrh (r.vertex j) ⟨j, rfl⟩)


/-- Cross a real bridge between two expanded fiber-disjoint core paths. -/
def recoverBridgeDetourWithCore (W : FiberWeightedMatching M H F) (p q : Path H)
    (hp : ∀ v, p.Contains v → F.root v = v) (hq : ∀ v, q.Contains v → F.root v = v)
    (hdis : p.Disjoint q) (a b : ParitySegment M) (ha : a.last = p.first) (hb : b.last = q.first)
    (hap : (a.phase + a.length) % 2 = W.phase p.first % 2)
    (hbp : (b.phase + b.length) % 2 = W.phase q.first % 2)
    (haf : ∀ i : Fin (a.length + 1), i.val < a.length → F.root (a.vertex i) = p.first)
    (hbf : ∀ i : Fin (b.length + 1), i.val < b.length → F.root (b.vertex i) = q.first)
    (hfree : M.Free q.last) (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1) :
    { z : AltPath M // z.first = q.last ∧ z.last = p.last ∧
      z.length = (b.length + W.weight q) + 1 + (a.length + W.weight p) ∧
      z.ContainsEdge b.first a.first ∧
      (∀ w, (∃ i, z.vertex i = w) → p.Contains (F.root w) ∨ q.Contains (F.root w)) ∧
      (∀ w, p.Contains w ∨ q.Contains w → ∃ i, z.vertex i = w) } := by
  obtain ⟨s, hsf, hsl, hsn, hsp, _, hsh, hscore⟩ :=
    W.recoverPathWithStartAndCore p hp a ha hap haf
  obtain ⟨r, hrf, hrl, hrn, hrp, _, hrh, hrcore⟩ :=
    W.recoverPathWithStartAndCore q hq b hb hbp hbf
  have hsep : ∀ i j, s.vertex i ≠ r.vertex j := by
    intro i j he
    exact hdis (F.root (s.vertex i)) (hsh (s.vertex i) ⟨i, rfl⟩)
      (by rw [he]; exact hrh (r.vertex j) ⟨j, rfl⟩)
  obtain ⟨z, hzf, hzl, hzn, hze, hcover⟩ := ParitySegment.recoverBridgeJoinFreeExact s r
    (hrl.symm ▸ hfree) (fun i j he => hsep j i he.symm)
    (by simpa only [hsp, hrp] using hphase)
    (by simpa only [hsf, hrf] using hedge)
    (by simpa only [hsf, hrf, hrp] using hmatch)
  refine ⟨z, hzf.trans hrl, hzl.trans hsl, by simpa only [hsn, hrn] using hzn,
    by simpa only [hsf, hrf] using hze, ?_, ?_⟩
  · intro w hw
    rcases (hcover w).1 hw with hs | hr
    · exact Or.inl (hsh w hs)
    · exact Or.inr (hrh w hr)
  · intro w hw
    apply (hcover w).2
    rcases hw with hpw | hqw
    · exact Or.inl (hscore w hpw)
    · exact Or.inr (hrcore w hqw)

/-- Compatibility interface for the same computed bridge path. -/
def recoverBridgeDetour (W : FiberWeightedMatching M H F) (p q : Path H)
    (hp : ∀ v, p.Contains v → F.root v = v) (hq : ∀ v, q.Contains v → F.root v = v)
    (hdis : p.Disjoint q) (a b : ParitySegment M) (ha : a.last = p.first) (hb : b.last = q.first)
    (hap : (a.phase + a.length) % 2 = W.phase p.first % 2)
    (hbp : (b.phase + b.length) % 2 = W.phase q.first % 2)
    (haf : ∀ i : Fin (a.length + 1), i.val < a.length → F.root (a.vertex i) = p.first)
    (hbf : ∀ i : Fin (b.length + 1), i.val < b.length → F.root (b.vertex i) = q.first)
    (hfree : M.Free q.last) (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1) :
    { z : AltPath M // z.first = q.last ∧ z.last = p.last ∧
      z.length = (b.length + W.weight q) + 1 + (a.length + W.weight p) ∧
      z.ContainsEdge b.first a.first } := by
  let z := W.recoverBridgeDetourWithCore p q hp hq hdis a b ha hb hap hbp haf hbf
    hfree hphase hedge hmatch
  exact ⟨z.val, z.property.1, z.property.2.1, z.property.2.2.1, z.property.2.2.2.1⟩

/-- Fiber-based bridge lifting with an exact expanded-length budget. -/
def recoverBridgeDetourOfPotentialWithCore (W : FiberWeightedMatching M H F) (p q : Path H)
    (hp : ∀ v, p.Contains v → F.root v = v) (hq : ∀ v, q.Contains v → F.root v = v)
    (hdis : p.Disjoint q) (a b : ParitySegment M) (ha : a.last = p.first) (hb : b.last = q.first)
    (hap : (a.phase + a.length) % 2 = W.phase p.first % 2)
    (hbp : (b.phase + b.length) % 2 = W.phase q.first % 2)
    (haf : ∀ i : Fin (a.length + 1), i.val < a.length → F.root (a.vertex i) = p.first)
    (hbf : ∀ i : Fin (b.length + 1), i.val < b.length → F.root (b.vertex i) = q.first)
    (hfree : M.Free q.last) (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1)
    (height : V → Nat)
    (hdrop : ∀ {u v} (he : H.Edge u v), (W.segment he).length + height v = height u)
    (hzero : height q.last = 0) (budget : Nat)
    (hbudget : (a.length + height p.first) + (b.length + height q.first) + 1 = budget) :
    { z : AltPath M // z.first = q.last ∧ z.last = p.last ∧
      z.length + height p.last = budget ∧ z.length = budget - height p.last ∧
      z.ContainsEdge b.first a.first ∧
      (∀ w, (∃ i, z.vertex i = w) → p.Contains (F.root w) ∨ q.Contains (F.root w)) ∧
      (∀ w, p.Contains w ∨ q.Contains w → ∃ i, z.vertex i = w) } := by
  obtain ⟨z, hzf, hzl, hzn, hze, hroots, hcore⟩ := W.recoverBridgeDetourWithCore p q hp hq hdis a b ha hb
    hap hbp haf hbf hfree hphase hedge hmatch
  have hpn := W.weight_add_potential height hdrop p
  have hqn := W.weight_add_potential height hdrop q
  exact ⟨z, hzf, hzl, by omega, by omega, hze, hroots, hcore⟩

/-- Compatibility interface retaining the potential budget. -/
def recoverBridgeDetourOfPotential (W : FiberWeightedMatching M H F) (p q : Path H)
    (hp : ∀ v, p.Contains v → F.root v = v) (hq : ∀ v, q.Contains v → F.root v = v)
    (hdis : p.Disjoint q) (a b : ParitySegment M) (ha : a.last = p.first) (hb : b.last = q.first)
    (hap : (a.phase + a.length) % 2 = W.phase p.first % 2)
    (hbp : (b.phase + b.length) % 2 = W.phase q.first % 2)
    (haf : ∀ i : Fin (a.length + 1), i.val < a.length → F.root (a.vertex i) = p.first)
    (hbf : ∀ i : Fin (b.length + 1), i.val < b.length → F.root (b.vertex i) = q.first)
    (hfree : M.Free q.last) (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1)
    (height : V → Nat)
    (hdrop : ∀ {u v} (he : H.Edge u v), (W.segment he).length + height v = height u)
    (hzero : height q.last = 0) (budget : Nat)
    (hbudget : (a.length + height p.first) + (b.length + height q.first) + 1 = budget) :
    { z : AltPath M // z.first = q.last ∧ z.last = p.last ∧
      z.length + height p.last = budget ∧ z.length = budget - height p.last ∧
      z.ContainsEdge b.first a.first } := by
  let z := W.recoverBridgeDetourOfPotentialWithCore p q hp hq hdis a b ha hb hap hbp haf hbf
    hfree hphase hedge hmatch height hdrop hzero budget hbudget
  exact ⟨z.val, z.property.1, z.property.2.1, z.property.2.2.1,
    z.property.2.2.2.1, z.property.2.2.2.2.1⟩

end MaximumMatching.DDFS.FiberWeightedMatching

end FiberWeightedRecovery
