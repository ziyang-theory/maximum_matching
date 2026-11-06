import MaximumMatching.ActivePetalPaths
import MaximumMatching.ActivePetalMax
import MaximumMatching.OperationalMaxRoutes

/-! Runtime parity routes for a petal found by DDFS in the restricted live
graph. The computed tree and tail paths are lifted with their vertex sequences
unchanged before the existing fiber expansion is applied. -/
namespace MaximumMatching.Search
variable {n i cut : Nat} {G : Graph (Fin n)} {M : Matching G}

namespace ActivePetalRecord

/-- Compute the old-root path to its new root, choosing by membership in the
stored selected-root list and following stored predecessor lists. -/
def recoverRootTail (R : ActivePetalRecord M i cut) (v : Fin n) :
    { q : DDFS.Path (predecessorGraph R.prior R.forest R.invariant) //
      q.first = R.forest.root v ∧ q.last = R.after.root v ∧
      (∀ w, q.Contains w → R.forest.root w = w) ∧
      (∀ w, q.Contains w → R.after.root w = R.after.root v) } := by
  if hv : R.forest.root v ∈ R.trees.vertices then
    have hsel := (R.trees.mem_vertices _).1 hv
    let q0 := R.recoverTail (R.forest.root v) hsel
    let q : {q : DDFS.Path (predecessorGraph R.prior R.forest R.invariant) //
        q.first = R.forest.root v ∧ q.last = R.bottleneck ∧
        ∀ w, q.Contains w → R.selected w} :=
      ⟨R.input.liftPath q0.val, q0.property⟩
    have hav := R.after_selected v hsel
    refine ⟨q.val, q.property.1, q.property.2.1.trans hav.symm, ?_, ?_⟩
    · intro w hw
      exact R.forest.root_of_fixed w (R.selected_fixed w (q.property.2.2 w hw))
    · intro w hw
      rw [hav]
      apply R.after_selected
      change R.selected (R.forest.root w)
      rw [R.forest.root_of_fixed w (R.selected_fixed w (q.property.2.2 w hw))]
      exact q.property.2.2 w hw
  else
    have hout : ¬ R.selected (R.forest.root v) := fun hs => hv ((R.trees.mem_vertices _).2 hs)
    have hav := R.after_outside v hout
    refine ⟨DDFS.Path.trivial _ (R.forest.root v), rfl, hav.symm, ?_, ?_⟩
    · rintro w ⟨j, hj⟩
      change R.forest.root v = w at hj
      rw [← hj]
      exact R.forest.root_idempotent v
    · rintro w ⟨j, hj⟩
      change R.forest.root v = w at hj
      rw [← hj]
      exact R.forest.mergeManyInto_root_congr _ _ _ _ (R.forest.root_idempotent v)


/-- A path from either recorded trigger root to a selected vertex stays in
the recorded region: append that vertex's tail to the bottleneck. -/
theorem path_selected (R : ActivePetalRecord M i cut)
    (p : DDFS.Path R.graph)
    (hfirst : p.first = R.forest.root R.left ∨ p.first = R.forest.root R.right)
    (hlast : R.selected p.last) : ∀ w, p.Contains w → R.selected w := by
  obtain ⟨q, hqf, hqb, _⟩ := R.recoverTail p.last hlast
  have hj : p.last = q.first := hqf.symm
  intro w hw
  exact (R.region w).2 ⟨p.append q hj,
    by simpa only [DDFS.Path.append_first] using hfirst,
    (p.append_last q hj).trans hqb,
    (p.contains_append_iff q hj w).2 (Or.inl hw)⟩

end ActivePetalRecord

namespace ParityArm

/-- Extend a computed old parity arm to the new root by the actual recorded
petal tail. The parity-label budget is unchanged. -/
def afterActivePetal (R : ActivePetalRecord M i cut)
    (W : DDFS.FiberWeightedMatching M
      (DDFS.fixedRootGraph (predecessorGraph R.prior R.forest R.invariant) R.forest) R.forest)
    (hphase : ∀ v, W.phase v % 2 = ((R.prior.minLabel v).getD 0 + 1) % 2)
    (hdrop : ∀ {u v} (he : (DDFS.fixedRootGraph
      (predecessorGraph R.prior R.forest R.invariant) R.forest).Edge u v),
      (W.segment he).length + (R.prior.minLabel v).getD 0 = (R.prior.minLabel u).getD 0)
    {v : Fin n} {k : Nat} (a : ParityArm M R.prior R.forest v k) :
    ParityArm M R.prior R.after v k := by
  let q := R.recoverRootTail v
  let p := q.val.restrictRoots R.forest q.property.2.2.1
  have hpf : p.first = R.forest.root v := q.property.1
  have hpl : p.last = R.after.root v := q.property.2.1
  have hap : (a.segment.phase + a.segment.length) % 2 = W.phase p.first % 2 := by
    rw [hphase, hpf]
    exact a.end_phase
  let c := W.recoverPathWithStart p q.property.2.2.1 a.segment
    (a.last.trans hpf.symm) hap (by rw [hpf]; exact a.interior)
  have hw := W.weight_add_potential (fun x => (R.prior.minLabel x).getD 0) hdrop p
  rw [hpf, hpl] at hw
  refine {
    segment := c.val
    first := c.property.1.trans a.first
    last := c.property.2.1.trans hpl
    length := ?_
    phase := ?_
    end_phase := ?_
    interior := ?_ }
  · have hn := c.property.2.2.1
    have ha := a.length
    omega
  · rw [c.property.2.2.2.1]
    exact a.phase
  · exact c.property.2.2.2.2.1.trans ((hphase p.last).trans (by rw [hpl]))
  · intro j _
    have hc := c.property.2.2.2.2.2 (c.val.vertex j) ⟨j, rfl⟩
    have hc' : q.val.Contains (R.forest.root (c.val.vertex j)) := hc
    have he : R.after.root (c.val.vertex j) = R.after.root (R.forest.root (c.val.vertex j)) :=
      (R.forest.mergeManyInto_root_congr _ _ _ _ (R.forest.root_idempotent _)).symm
    exact he.trans (q.property.2.2.2 _ hc')


end ParityArm

namespace ActivePetalRecord

def recoverMaxArmOfLinkage (R : ActivePetalRecord M i cut)
    (W : DDFS.FiberWeightedMatching M
      (DDFS.fixedRootGraph (predecessorGraph R.prior R.forest R.invariant) R.forest) R.forest)
    (hphase : ∀ v, W.phase v % 2 = ((R.prior.minLabel v).getD 0 + 1) % 2)
    (hdrop : ∀ {u v} (he : (DDFS.fixedRootGraph
      (predecessorGraph R.prior R.forest R.invariant) R.forest).Edge u v),
      (W.segment he).length + (R.prior.minLabel v).getD 0 = (R.prior.minLabel u).getD 0)
    {u v w : Fin n} (T : ComputedBridgeArms M (2 * i + 1) R.prior R.forest u v)
    (hadj : G.Adj u v) (htodd : (2 * i + 1) % 2 = 1)
    (p q : DDFS.Path (predecessorGraph R.prior R.forest R.invariant))
    (hpf : p.first = R.forest.root u) (hqf : q.first = R.forest.root v)
    (hpl : p.last = w) (hql : q.last = R.bottleneck) (hdis : p.Disjoint q)
    (hps : ∀ x, p.Contains x → R.selected x) (hqs : ∀ x, q.Contains x → R.selected x) :
    ParityArm M R.prior R.after w ((2 * i + 1) - (R.prior.minLabel w).getD 0) := by
  have hpfix : ∀ x, p.Contains x → R.forest.root x = x :=
    fun x hx => R.forest.root_of_fixed x (R.selected_fixed x (hps x hx))
  have hqfix : ∀ x, q.Contains x → R.forest.root x = x :=
    fun x hx => R.forest.root_of_fixed x (R.selected_fixed x (hqs x hx))
  let pr := p.restrictRoots R.forest hpfix
  let qr := q.restrictRoots R.forest hqfix
  have hap : (T.left.phase + T.left.length) % 2 = W.phase pr.first % 2 := by
    rw [hphase]
    change _ = ((R.prior.minLabel p.first).getD 0 + 1) % 2
    rw [hpf]
    exact T.left_end_phase
  have hbp : (T.right.phase + T.right.length) % 2 = W.phase qr.first % 2 := by
    rw [hphase]
    change _ = ((R.prior.minLabel q.first).getD 0 + 1) % 2
    rw [hqf]
    exact T.right_end_phase
  let a := W.recoverPathWithStart pr hpfix T.left (T.left_last.trans hpf.symm) hap
    (by change ∀ j, j.val < T.left.length → R.forest.root (T.left.vertex j) = p.first
        rw [hpf]; exact T.left_interior)
  let b := W.recoverPathWithStart qr hqfix T.right (T.right_last.trans hqf.symm) hbp
    (by change ∀ j, j.val < T.right.length → R.forest.root (T.right.vertex j) = q.first
        rw [hqf]; exact T.right_interior)
  have hsep : ∀ j k, a.val.vertex j ≠ b.val.vertex k := by
    intro j k he
    exact hdis (R.forest.root (a.val.vertex j))
      (a.property.2.2.2.2.2 _ ⟨j, rfl⟩)
      (by rw [he]; exact b.property.2.2.2.2.2 _ ⟨k, rfl⟩)
  have hbridge : (M.mate a.val.first = some b.val.first) ↔ (a.val.phase + 1) % 2 = 1 := by
    rw [a.property.1, b.property.1, a.property.2.2.2.1]
    have hs := T.same_phase
    exact ⟨fun hm => by have hh := T.bridge_phase.1 (M.symm hm); omega,
      fun hh => M.symm (T.bridge_phase.2 (by omega))⟩
  let z := b.val.recoverBridgeJoin a.val hsep
    (by rw [a.property.2.2.2.1, b.property.2.2.2.1]; exact T.same_phase.symm)
    (by rw [a.property.1, b.property.1, T.left_first, T.right_first]; exact hadj) hbridge
  have ha := W.weight_add_potential (fun x => (R.prior.minLabel x).getD 0) hdrop pr
  have hb := W.weight_add_potential (fun x => (R.prior.minLabel x).getD 0) hdrop qr
  change W.weight pr + (R.prior.minLabel p.last).getD 0 = (R.prior.minLabel p.first).getD 0 at ha
  change W.weight qr + (R.prior.minLabel q.last).getD 0 = (R.prior.minLabel q.first).getD 0 at hb
  rw [hpf, hpl] at ha
  rw [hqf, hql] at hb
  have haw : R.after.root w = R.bottleneck := R.after_selected w (by
    change R.selected (R.forest.root w)
    rw [hpfix w (hpl ▸ p.contains_last)]
    exact hps w (hpl ▸ p.contains_last))
  have hlen : z.val.length + (R.prior.minLabel R.bottleneck).getD 0 =
      (2 * i + 1) - (R.prior.minLabel w).getD 0 := by
    have hbudget := T.budget
    have hza := z.property.2.2.1
    have hal := a.property.2.2.1
    have hbl := b.property.2.2.1
    omega
  have hstart : z.val.phase % 2 = ((2 * i + 1) - (R.prior.minLabel w).getD 0 + 1) % 2 := by
    have hap' := a.property.2.2.2.2.1.trans (hphase pr.last)
    change (a.val.phase + a.val.length) % 2 = ((R.prior.minLabel p.last).getD 0 + 1) % 2 at hap'
    rw [hpl] at hap'
    have hzp := z.property.2.2.2.1
    have hbudget := T.budget
    have hal := a.property.2.2.1
    have hbl := b.property.2.2.1
    omega
  refine {
    segment := z.val
    first := z.property.1.trans (a.property.2.1.trans hpl)
    last := z.property.2.1.trans ((b.property.2.1.trans hql).trans haw.symm)
    length := by rw [haw]; exact hlen
    phase := hstart
    end_phase := ?_
    interior := ?_ }
  · rw [haw]
    omega
  · intro j _
    rw [haw]
    have hsel : R.selected (R.forest.root (z.val.vertex j)) := by
      rcases z.property.2.2.2.2.1 _ ⟨j, rfl⟩ with hz | hz
      · exact hqs _ (b.property.2.2.2.2.2 _ hz)
      · exact hps _ (a.property.2.2.2.2.2 _ hz)
    exact R.after_selected _ hsel


/-- Recover a newly selected root's maximum-parity route by its stored color:
follow its color tree back across the recorded bridge, then the opposite tree
to the bottleneck. All nested expansions use the supplied runtime arms. -/
def recoverMaxArm (R : ActivePetalRecord M i cut) (A : OperationalArms M R.prior R.forest)
    (W : DDFS.FiberWeightedMatching M
      (DDFS.fixedRootGraph (predecessorGraph R.prior R.forest R.invariant) R.forest) R.forest)
    (hphase : ∀ v, W.phase v % 2 = ((R.prior.minLabel v).getD 0 + 1) % 2)
    (hdrop : ∀ {u v} (he : (DDFS.fixedRootGraph
      (predecessorGraph R.prior R.forest R.invariant) R.forest).Edge u v),
      (W.segment he).length + (R.prior.minLabel v).getD 0 = (R.prior.minLabel u).getD 0)
    (htodd : (2 * i + 1) % 2 = 1) (w : Fin n) (hw : w ∈ R.newRoots) :
    ParityArm M R.prior R.after w ((2 * i + 1) - (R.prior.minLabel w).getD 0) := by
  have hsel := ((R.mem_newRoots w).1 hw).1
  have hne := ((R.mem_newRoots w).1 hw).2
  have hlevel := DDFS.onRootTo_level_gt ((R.region w).1 hsel) hne
  let T := A.bridgeArms R.invariant.minInvariant.1 R.left R.right (2 * i + 1) R.known
  cases hc : R.trees.color w with
  | none =>
    exact False.elim (by
      obtain ⟨c, hcolor⟩ := (R.trees.domain w).2 ⟨hsel, hne⟩
      rw [hc] at hcolor
      contradiction)
  | some c =>
    cases c
    · let pq := R.trees.red.recoverLinkage R.trees.green (Or.inr hc) (Or.inl rfl)
        (fun x hx hx' => (R.trees.overlap x).1 ⟨hx, hx'⟩) hlevel
      exact R.recoverMaxArmOfLinkage W hphase hdrop T R.trigger.1.1 htodd (R.input.liftPath pq.val.1) (R.input.liftPath pq.val.2)
        pq.property.1 pq.property.2.2.1 pq.property.2.1 pq.property.2.2.2.1 pq.property.2.2.2.2
        (R.path_selected pq.val.1 (Or.inl pq.property.1) (by rw [pq.property.2.1]; exact hsel))
        (R.path_selected pq.val.2 (Or.inr pq.property.2.2.1)
          (by rw [pq.property.2.2.2.1]; exact R.trees.bottleneck_mem))
    · let pq := R.trees.green.recoverLinkage R.trees.red (Or.inr hc) (Or.inl rfl)
        (fun x hx hx' => (R.trees.overlap x).1 ⟨hx', hx⟩) hlevel
      exact R.recoverMaxArmOfLinkage W hphase hdrop T.swap (G.symm R.trigger.1.1) htodd (R.input.liftPath pq.val.1) (R.input.liftPath pq.val.2)
        pq.property.1 pq.property.2.2.1 pq.property.2.1 pq.property.2.2.2.1 pq.property.2.2.2.2
        (R.path_selected pq.val.1 (Or.inr pq.property.1) (by rw [pq.property.2.1]; exact hsel))
        (R.path_selected pq.val.2 (Or.inl pq.property.2.2.1)
          (by rw [pq.property.2.2.2.1]; exact R.trees.bottleneck_mem))


end ActivePetalRecord

namespace OperationalArms
variable [DecidableRel G.Adj]

/-- Carry runtime parity routes through the actual MAX assignment and petal
merge. Old labels extend their old routes; new maximum labels receive the
computed colored-tree bridge route. No semantic path witness is executed. -/
def afterActiveMax (R : ActivePetalRecord M i cut)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) :
    OperationalArms M R.maxEvent.1 R.after := by
  let A := R.input.A
  let W := A.weighted R.input.B.stage R.invariant
  have hphase : ∀ v, W.phase v % 2 = ((R.prior.minLabel v).getD 0 + 1) % 2 := fun _ => rfl
  have hdrop : ∀ {u v} (he : (DDFS.fixedRootGraph
      (predecessorGraph R.prior R.forest R.invariant) R.forest).Edge u v),
      (W.segment he).length + (R.prior.minLabel v).getD 0 = (R.prior.minLabel u).getD 0 :=
    fun he => A.weighted_drop R.input.B.stage R.invariant he
  have hmdata : R.maxEvent.1.minLabel = R.prior.minLabel := funext (R.maxEvent_minLabel)
  have hset : ∀ v, v ∈ R.newRoots → R.maxEvent.1.maxLabel v = maxlevel M v := by
    obtain ⟨P⟩ := R.input.B.represented
    exact (R.maxEvent_correct_of_current P hc htop hstageTen).2.2.1
  refine ⟨fun v parity k hk => ?_⟩
  cases hm : R.prior.minLabel v with
  | none =>
    have hn : R.maxEvent.1.minLabel v = none := (R.maxEvent_minLabel v).trans hm
    simp [parityLabel, hn] at hk
  | some lo =>
    have hn : R.maxEvent.1.minLabel v = some lo := (R.maxEvent_minLabel v).trans hm
    by_cases hpar : lo % 2 = parity
    · have heq : lo = k := by simpa [parityLabel, hn, hpar] using hk
      have hkold : parityLabel R.prior v parity = some k := by
        rw [← heq]
        simp [parityLabel, hm, hpar]
      exact ((A.get v parity k hkold).afterActivePetal R W hphase hdrop).of_same_min_data hmdata
    · if hv : v ∈ R.newRoots then
        have hmax : maxlevel M v = some ((2 * i + 1) - lo) := by
          obtain ⟨P⟩ := R.input.B.represented
          have ht := (R.newRoots_support_of_current P hc htop hstageTen v hv).1
          exact (maxlevel_eq_tenacity_sub v (2 * i + 1) lo ht (R.invariant.minInvariant.1.1 v lo hm)).2
        have hnewmax := (hset v hv).trans hmax
        have heq : (2 * i + 1) - lo = k := by
          have hk' : (if ((2 * i + 1) - lo) % 2 = parity then some ((2 * i + 1) - lo) else none) = some k := by
            simpa [parityLabel, hn, hpar, hnewmax] using hk
          split at hk'
          · exact Option.some.inj hk'
          · contradiction
        have hodd : (2 * i + 1) % 2 = 1 := by omega
        have hkind : (2 * i + 1) - (R.prior.minLabel v).getD 0 = k := by
          simpa only [hm, Option.getD_some] using heq
        exact hkind ▸ (R.recoverMaxArm A W hphase hdrop hodd v hv).of_same_min_data hmdata
      else
        have hmax := R.maxEvent_outside v hv
        have hkold : parityLabel R.prior v parity = some k := by
          simpa only [parityLabel, hn, hm, hmax] using hk
        exact ((A.get v parity k hkold).afterActivePetal R W hphase hdrop).of_same_min_data hmdata

end OperationalArms
end MaximumMatching.Search
