import MaximumMatching.OperationalArms
import MaximumMatching.FiberWeightedRecovery
import MaximumMatching.OperationalPredecessorArms
import MaximumMatching.CurrentBucket

/-! Computed bridge endpoints and matching paths from operational parity arms.
Available parity labels supply the actual two endpoint segments. The weighted
core recovery consumes the raw DDFS paths and returns a matching path in Type. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

/-- The two computed endpoint arms and the exact trigger-edge budget. -/
structure ComputedBridgeArms (M : Matching G) (t : Nat) (s : State V)
    (F : BudForest V) (u v : V) where
  left : ParitySegment M
  right : ParitySegment M
  left_first : left.first = u
  left_last : left.last = F.root u
  right_first : right.first = v
  right_last : right.last = F.root v
  left_end_phase : (left.phase + left.length) % 2 = ((s.minLabel (F.root u)).getD 0 + 1) % 2
  right_end_phase : (right.phase + right.length) % 2 = ((s.minLabel (F.root v)).getD 0 + 1) % 2
  left_interior : ∀ j : Fin (left.length + 1), j.val < left.length →
    F.root (left.vertex j) = F.root u
  right_interior : ∀ j : Fin (right.length + 1), j.val < right.length →
    F.root (right.vertex j) = F.root v
  same_phase : left.phase % 2 = right.phase % 2
  bridge_phase : (M.mate right.first = some left.first) ↔ (right.phase + 1) % 2 = 1
  budget : (left.length + (s.minLabel (F.root u)).getD 0) +
    (right.length + (s.minLabel (F.root v)).getD 0) + 1 = t

namespace OperationalArms
variable {s : State V} {F : BudForest V}

/-- Read actual available labels, then retrieve their computed parity arms.
No existential witness or semantic minimum is used to select runtime data. -/
def bridgeArms (A : OperationalArms M s F) (hs : LabelsSound M s)
    (u v : V) (t : Nat) (ht : edgeTenacity M s u v = some t) :
    ComputedBridgeArms M t s F u v := by
  let parity := if M.mate u = some v then 1 else 0
  have ht' : (do let a ← parityLabel s u parity
                 let b ← parityLabel s v parity
                 some (a + b + 1)) = some t := ht
  cases hu : parityLabel s u parity with
  | none => simp [hu] at ht'
  | some k =>
    cases hv : parityLabel s v parity with
    | none => simp [hu, hv] at ht'
    | some l =>
      let a := A.get u parity k hu
      let b := A.get v parity l hv
      have hsum : k + l + 1 = t := by simpa [hu, hv] using ht'
      have hkp := level_parity M parity u k (parityLabel_sound s hs u parity k hu)
      have hlp := level_parity M parity v l (parityLabel_sound s hs v parity l hv)
      have hap := a.phase
      have hbp := b.phase
      refine {
        left := a.segment, right := b.segment,
        left_first := a.first, left_last := a.last,
        right_first := b.first, right_last := b.last,
        left_end_phase := a.end_phase, right_end_phase := b.end_phase,
        left_interior := a.interior, right_interior := b.interior,
        same_phase := by omega,
        bridge_phase := ?_, budget := by rw [a.length, b.length]; exact hsum }
      rw [a.first, b.first]
      by_cases hm : M.mate u = some v
      · have hp : parity = 1 := by simp only [parity, hm, ite_true]
        exact ⟨fun _ => by omega, fun _ => M.symm hm⟩
      · have hp : parity = 0 := by simp only [parity, hm, ite_false]
        exact ⟨fun hm' => False.elim (hm (M.symm hm')), fun hn => by omega⟩

variable {cap : Nat} {h : BudGraphInvariant M cap s F}

/-- Expand raw disjoint DDFS arms through the actual triggering edge. All
segments and vertex maps are computed from operational arms and the supplied
weighted representation; only their certificates are erased. -/
def recoverBridgePath (A : OperationalArms M s F) (hs : LabelsSound M s)
    (W : DDFS.FiberWeightedMatching M (DDFS.fixedRootGraph (predecessorGraph s F h) F) F)
    (hphase : ∀ v, W.phase v % 2 = ((s.minLabel v).getD 0 + 1) % 2)
    (hdrop : ∀ {u v} (he : (DDFS.fixedRootGraph (predecessorGraph s F h) F).Edge u v),
      (W.segment he).length + (s.minLabel v).getD 0 = (s.minLabel u).getD 0)
    (u v : V) (t : Nat) (hadj : G.Adj u v) (ht : edgeTenacity M s u v = some t)
    (p q : DDFS.Path (predecessorGraph s F h))
    (hpf : p.first = F.root u) (hqf : q.first = F.root v)
    (hqb : (predecessorGraph s F h).level q.last = 0) (hdis : p.Disjoint q) :
    { z : AltPath M // z.first = q.last ∧ z.last = p.last ∧
      z.length + (s.minLabel p.last).getD 0 = t ∧ z.ContainsEdge u v } := by
  let T := A.bridgeArms hs u v t ht
  obtain ⟨hu, hv⟩ := edgeTenacity_has_minLabels s u v t ht
  have hqa : ∃ k, s.minLabel q.first = some k := by
    rw [hqf]
    obtain ⟨k, hk⟩ := hv
    exact h.rootAssigned v k hk
  have hpfix : ∀ w, p.Contains w → F.root w = w := by
    rintro w ⟨i, rfl⟩
    exact F.root_of_fixed _ (h.path_fixed p (by rw [hpf]; exact F.root_fixed u) i)
  have hqfix : ∀ w, q.Contains w → F.root w = w := by
    rintro w ⟨i, rfl⟩
    exact F.root_of_fixed _ (h.path_fixed q (by rw [hqf]; exact F.root_fixed v) i)
  let pr := p.restrictRoots F hpfix
  let qr := q.restrictRoots F hqfix
  have hap : (T.left.phase + T.left.length) % 2 = W.phase pr.first % 2 := by
    rw [hphase]
    change _ = ((s.minLabel p.first).getD 0 + 1) % 2
    rw [hpf]
    exact T.left_end_phase
  have hbp : (T.right.phase + T.right.length) % 2 = W.phase qr.first % 2 := by
    rw [hphase]
    change _ = ((s.minLabel q.first).getD 0 + 1) % 2
    rw [hqf]
    exact T.right_end_phase
  obtain ⟨z, hzf, hzl, hzn, _, hedge⟩ := W.recoverBridgeDetourOfPotential pr qr
    hpfix hqfix hdis T.left T.right (T.left_last.trans hpf.symm) (T.right_last.trans hqf.symm)
    hap hbp
    (by change ∀ j, j.val < T.left.length → F.root (T.left.vertex j) = p.first
        rw [hpf]; exact T.left_interior)
    (by change ∀ j, j.val < T.right.length → F.root (T.right.vertex j) = q.first
        rw [hqf]; exact T.right_interior)
    (h.path_bottom_free q hqa hqb) T.same_phase
    (by rw [T.right_first, T.left_first]; exact G.symm hadj) T.bridge_phase
    (fun w => (s.minLabel w).getD 0) hdrop hqb t
    (by change (T.left.length + (s.minLabel p.first).getD 0) +
          (T.right.length + (s.minLabel q.first).getD 0) + 1 = t
        rw [hpf, hqf]; exact T.budget)
  rw [T.right_first, T.left_first] at hedge
  exact ⟨z, hzf, hzl, hzn, (z.containsEdge_symm v u).1 hedge⟩

/-- Recover the actual shortest augmenting matching path when both computed
DDFS arms reach free bottoms. -/
def recoverShortestAugmenting (A : OperationalArms M s F) (hs : LabelsSound M s)
    (W : DDFS.FiberWeightedMatching M (DDFS.fixedRootGraph (predecessorGraph s F h) F) F)
    (hphase : ∀ v, W.phase v % 2 = ((s.minLabel v).getD 0 + 1) % 2)
    (hdrop : ∀ {u v} (he : (DDFS.fixedRootGraph (predecessorGraph s F h) F).Edge u v),
      (W.segment he).length + (s.minLabel v).getD 0 = (s.minLabel u).getD 0)
    (u v : V) (t : Nat) (hadj : G.Adj u v) (ht : edgeTenacity M s u v = some t)
    (hodd : t % 2 = 1) (hbound : AtMostShortestAugmenting M t)
    (p q : DDFS.Path (predecessorGraph s F h))
    (hp : p.ToBottom (F.root u)) (hq : q.ToBottom (F.root v)) (hdis : p.Disjoint q) :
    { z : AltPath M // z.Augmenting ∧ z.first = q.last ∧ z.last = p.last ∧
      z.length = t ∧ z.ContainsEdge u v ∧
      ∀ r : AltPath M, r.Augmenting → z.length ≤ r.length } := by
  obtain ⟨z, hzf, hzl, hzn, hedge⟩ := A.recoverBridgePath hs W hphase hdrop u v t hadj ht
    p q hp.1 hq.1 hq.2 hdis
  have hpb : (s.minLabel p.last).getD 0 = 0 := hp.2
  have hlen : z.length = t := by omega
  have hpa : ∃ k, s.minLabel p.first = some k := by
    rw [hp.1]
    obtain ⟨⟨k, hk⟩, _⟩ := edgeTenacity_has_minLabels s u v t ht
    exact h.rootAssigned u k hk
  have hfree : M.Free z.last := hzl ▸ h.path_bottom_free p hpa hp.2
  exact ⟨z, ⟨by rw [hlen]; exact hodd, hfree⟩, hzf, hzl, hlen, hedge,
    fun r hr => hlen ▸ hbound r hr⟩

end OperationalArms

namespace CurrentBucketWitness
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}
    {i cut : Nat} {B : CurrentBucketState M i cut}

/-- Turn this exact raw DDFS output into a computed shortest alternating
matching path, using the operational arms stored alongside its search state. -/
def recover (certificate : CurrentBucketWitness B)
    (A : OperationalArms M B.state B.forest)
    (_hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) :
    { p : AltPath M // p.Augmenting ∧ p.first = certificate.green.last ∧
      p.last = certificate.red.last ∧ p.length = 2 * i + 1 ∧
      p.ContainsEdge certificate.left certificate.right ∧
      ∀ q : AltPath M, q.Augmenting → p.length ≤ q.length } := by
  have hb := B.stage.classification.2.2 (2 * i + 1) certificate.left certificate.right certificate.queued
  have hk := B.stage.current_bridge_known certificate.left certificate.right hb.1 hb.2
  exact A.recoverShortestAugmenting B.stage.min.1 (A.weighted B.stage B.bud)
    (fun _ => rfl) (fun he => A.weighted_drop B.stage B.bud he)
    certificate.left certificate.right (2 * i + 1) hb.1.1 hk (by omega)
    (by simpa only [hstageTen] using htop) certificate.red certificate.green
    certificate.red_bottom certificate.green_bottom certificate.disjoint

end CurrentBucketWitness
end MaximumMatching.Search
