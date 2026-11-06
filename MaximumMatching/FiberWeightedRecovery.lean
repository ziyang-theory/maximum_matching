import MaximumMatching.FiberWeightedExpansion
import MaximumMatching.ParityBridgeRecovery

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
def recoverPath (W : FiberWeightedMatching M H F) (p : Path H)
    (hfixed : ∀ v, p.Contains v → F.root v = v) :
    { s : ParitySegment M // s.first = p.first ∧ s.last = p.last ∧
      s.length = W.weight p ∧ s.phase % 2 = W.phase p.first % 2 ∧
      (s.phase + s.length) % 2 = W.phase p.last % 2 ∧
      (∀ v, s.Contains v → p.Contains (F.root v)) ∧
      (∀ v, s.Contains v → F.root v = p.first → v = p.first) } := by
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
    obtain ⟨s, hsf, hsl, hsn, hsp, hse, hsh, hsa⟩ := W.recoverPath q
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
termination_by p.length
decreasing_by change p.length - 1 < p.length; omega

/-- Attach an actual endpoint-to-root segment lying in the initial fiber.
The realized core only meets that fiber at its initial root. -/
def recoverPathWithStart (W : FiberWeightedMatching M H F) (p : Path H)
    (hfixed : ∀ v, p.Contains v → F.root v = v)
    (a : ParitySegment M) (ha : a.last = p.first)
    (hap : (a.phase + a.length) % 2 = W.phase p.first % 2)
    (haf : ∀ i : Fin (a.length + 1), i.val < a.length → F.root (a.vertex i) = p.first) :
    { s : ParitySegment M // s.first = a.first ∧ s.last = p.last ∧
      s.length = a.length + W.weight p ∧ s.phase = a.phase ∧
      (s.phase + s.length) % 2 = W.phase p.last % 2 ∧
      (∀ v, s.Contains v → p.Contains (F.root v)) } := by
  obtain ⟨r, hrf, hrl, hrn, hrp, hre, hrh, hravoid⟩ := W.recoverPath p hfixed
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
  obtain ⟨s, r, hsf, hsl, hsn, hrf, hrl, hrn, hsp, hrp, hsep⟩ :=
    W.recoverDisjointStarts p q hp hq hdis a b ha hb hap hbp haf hbf
  obtain ⟨z, hzf, hzl, hzn, hze⟩ := ParitySegment.recoverBridgeJoinFree s r
    (hrl.symm ▸ hfree) (fun i j he => hsep j i he.symm)
    (by simpa only [hsp, hrp] using hphase)
    (by simpa only [hsf, hrf] using hedge)
    (by simpa only [hsf, hrf, hrp] using hmatch)
  exact ⟨z, hzf.trans hrl, hzl.trans hsl, by simpa only [hsn, hrn] using hzn,
    by simpa only [hsf, hrf] using hze⟩

/-- Fiber-based bridge lifting with an exact expanded-length budget. -/
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
  obtain ⟨z, hzf, hzl, hzn, hze⟩ := W.recoverBridgeDetour p q hp hq hdis a b ha hb
    hap hbp haf hbf hfree hphase hedge hmatch
  have hpn := W.weight_add_potential height hdrop p
  have hqn := W.weight_add_potential height hdrop q
  exact ⟨z, hzf, hzl, by omega, by omega, hze⟩

end MaximumMatching.DDFS.FiberWeightedMatching
