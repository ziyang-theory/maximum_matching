import MaximumMatching.ActivePetalRecord
import MaximumMatching.ActiveSearch
import MaximumMatching.PhaseDriver
import MaximumMatching.RecoverableBucket
import MaximumMatching.ShortestAugmentingSearch

section ActivePetalArms

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

end ActivePetalArms

section ActivePetalTransport

/-! A live petal contraction preserves bottom paths and their original-vertex
containment. Its region closure is used only in the restricted live graph. -/
namespace MaximumMatching.Search.ActivePetalRecord
variable {n i cut : Nat} {G : Graph (Fin n)} {M : Matching G}

abbrev afterGraph (R : ActivePetalRecord M i cut) :=
  DDFS.RecursiveRemoval.restricted
    (predecessorGraph R.prior R.after R.after_invariant) R.afterLive

theorem after_root_old_root (R : ActivePetalRecord M i cut) (v : Fin n) :
    R.after.root (R.forest.root v) = R.after.root v :=
  R.forest.mergeManyInto_root_congr _ _ _ _ (R.forest.root_idempotent v)

/-- The target of an old predecessor edge becomes its new bud root. -/
theorem after_edge_target (R : ActivePetalRecord M i cut) {v w : Fin n}
    (he : (predecessorGraph R.prior R.forest R.invariant).Edge v w) :
    (predecessorGraph R.prior R.after R.after_invariant).Edge v (R.after.root w) := by
  obtain ⟨u, hu, huw⟩ := List.mem_map.mp he.2
  refine ⟨he.1, List.mem_map.mpr ⟨u, hu, ?_⟩⟩
  exact R.forest.mergeManyInto_root_congr _ _ u w
    (by rw [← huw]; exact (R.forest.root_idempotent u).symm)

/-- Each old live edge collapses or survives as an actual new live edge. -/
theorem after_edge_eq_or_edge (R : ActivePetalRecord M i cut) {v w : Fin n}
    (he : R.graph.Edge v w) :
    R.after.root v = R.after.root w ∨ R.afterGraph.Edge (R.after.root v) (R.after.root w) := by
  have hvfix := R.input.live_fixed v he.1
  have hwfix := R.input.live_fixed w he.2.1
  by_cases hv : R.selected v
  · by_cases hvb : v = R.bottleneck
    · right
      refine ⟨R.after_root_live v he.1, R.after_root_live w he.2.1, ?_⟩
      have hvafter : R.after.root v = v := by
        rw [R.after_selected v (by change R.selected (R.forest.root v); rw [hvfix]; exact hv)]
        exact hvb.symm
      rw [hvafter]
      exact R.after_edge_target he.2.2
    · left
      have hw := R.selected_edge_closed hv hvb he
      rw [R.after_selected v (by change R.selected (R.forest.root v); rw [hvfix]; exact hv),
        R.after_selected w (by change R.selected (R.forest.root w); rw [hwfix]; exact hw)]
  · right
    refine ⟨R.after_root_live v he.1, R.after_root_live w he.2.1, ?_⟩
    have hvafter : R.after.root v = v :=
      (R.after_outside v (by change ¬R.selected (R.forest.root v); rwa [hvfix])).trans hvfix
    rw [hvafter]
    exact R.after_edge_target he.2.2

theorem transport_path (R : ActivePetalRecord M i cut) (p : DDFS.Path R.graph) :
    ∃ q : DDFS.Path R.afterGraph,
      q.first = R.after.root p.first ∧ q.last = R.after.root p.last ∧ q.length ≤ p.length ∧
      ∀ w, q.Contains w ↔ ∃ v, p.Contains v ∧ R.after.root v = w := by
  exact p.map_eq_or_edge R.after.root (fun _ _ he _ _ => R.after_edge_eq_or_edge he)

/-- A path reaching bottom after entering the selected region passes through
its bottleneck, including when its endpoint is that bottleneck. -/
theorem selected_bottom_path_contains_bottleneck (R : ActivePetalRecord M i cut)
    (p : DDFS.Path R.graph) (v : Fin n) (hv : p.Contains v) (hsel : R.selected v)
    (hbottom : R.graph.level p.last = 0) : p.Contains R.bottleneck := by
  apply Classical.byContradiction
  intro havoid
  obtain ⟨j, hj⟩ := hv
  let q := p.drop j.val (by omega)
  have hqf : R.selected q.first := by rw [p.drop_first, hj]; exact hsel
  have hqavoid : ¬q.Contains R.bottleneck := fun hb => havoid (p.contains_drop _ _ hb)
  have hall := q.stays_in_closed_except R.selected R.bottleneck
    (fun _ _ hw hne he => R.selected_edge_closed hw hne he) hqf hqavoid
  have hslast : R.selected p.last := by
    have hh := hall ⟨q.length, by omega⟩
    change R.selected q.last at hh
    rwa [p.drop_last] at hh
  have hne : p.last ≠ R.bottleneck := fun he => havoid (he ▸ p.contains_last)
  have hh := DDFS.onRootTo_level_gt ((R.region p.last).1 hslast) hne
  rw [hbottom] at hh
  omega

theorem after_root_on_bottom_path (R : ActivePetalRecord M i cut)
    (p : DDFS.Path R.graph) (hfix : ∀ v, p.Contains v → R.forest.root v = v)
    (hb : R.graph.level p.last = 0) (v : Fin n) (hv : p.Contains v) :
    p.Contains (R.after.root v) := by
  have hf := hfix v hv
  by_cases hs : R.selected v
  · rw [R.after_selected v (by change R.selected (R.forest.root v); rwa [hf])]
    exact R.selected_bottom_path_contains_bottleneck p v hv hs hb
  · rw [R.after_outside v (by change ¬R.selected (R.forest.root v); rwa [hf]), hf]
    exact hv

theorem after_bottom_fixed (R : ActivePetalRecord M i cut) (v : Fin n)
    (hfix : R.forest.root v = v) (hb : R.graph.level v = 0) : R.after.root v = v := by
  by_cases hs : R.selected v
  · have he : v = R.bottleneck := by
      by_cases he : v = R.bottleneck
      · exact he
      · have hh := DDFS.onRootTo_level_gt ((R.region v).1 hs) he
        rw [hb] at hh
        omega
    exact (R.after_selected v (by change R.selected (R.forest.root v); rwa [hfix])).trans he.symm
  · exact (R.after_outside v (by change ¬R.selected (R.forest.root v); rwa [hfix])).trans hfix

theorem after_bottom (R : ActivePetalRecord M i cut) (v : Fin n)
    (hb : R.graph.level v = 0) : R.afterGraph.level v = 0 := by
  by_cases hv : v ∈ R.afterLive
  · have hold := ((R.mem_afterLive v).1 hv).1
    change (if v ∈ R.afterLive then (R.prior.minLabel v).getD 0 else 0) = 0
    rw [ite_eq_left hv]
    exact (R.input.level_live v hold).symm.trans hb
  · change (if v ∈ R.afterLive then _ else 0) = 0
    exact ite_eq_right hv

/-- Contraction adds no original vertex to a bottom path. -/
theorem transport_bottom_path (R : ActivePetalRecord M i cut)
    (p : DDFS.Path R.graph) (hfix : ∀ v, p.Contains v → R.forest.root v = v)
    (hb : R.graph.level p.last = 0) :
    ∃ q : DDFS.Path R.afterGraph,
      q.first = R.after.root p.first ∧ q.last = p.last ∧ R.afterGraph.level q.last = 0 ∧
      ∀ v, q.Contains v → p.Contains v := by
  obtain ⟨q, hqf, hql, _, hqv⟩ := R.transport_path p
  have hlast : q.last = p.last := hql.trans (R.after_bottom_fixed p.last (hfix _ p.contains_last) hb)
  refine ⟨q, hqf, hlast, ?_, ?_⟩
  · rw [hlast]
    exact R.after_bottom p.last hb
  · intro v hv
    obtain ⟨u, hu, huv⟩ := (hqv v).1 hv
    rw [← huv]
    exact R.after_root_on_bottom_path p hfix hb u hu

/-- Every surviving root still reaches a genuine live bottom. Isolated
removed roots retain the restricted graph's conventional zero level. -/
theorem after_reach (R : ActivePetalRecord M i cut) : DDFS.ReachBottom R.afterGraph := by
  intro v
  by_cases hv : v ∈ R.afterLive
  · have hvlive := ((R.mem_afterLive v).1 hv).1
    obtain ⟨p, hpf, hpb⟩ := R.input.reach v
    have hfix : ∀ w, p.Contains w → R.forest.root w = w := by
      intro w hw
      exact R.input.live_fixed w (R.input.path_live p (hpf ▸ hvlive) w hw)
    obtain ⟨q, hqf, _, hqb, _⟩ := R.transport_bottom_path p hfix hpb
    exact ⟨q, hqf.trans ((congrArg R.after.root hpf).trans ((R.mem_afterLive v).1 hv).2), hqb⟩
  · refine ⟨DDFS.Path.trivial R.afterGraph v, rfl, ?_⟩
    change (if v ∈ R.afterLive then _ else 0) = 0
    exact ite_eq_right hv

/-- Vertex-contained disjoint bottom arms remain vertex-contained and
separate after a live petal contraction. -/
theorem transport_bottom_bridge_arms (R : ActivePetalRecord M i cut)
    {u v : Fin n} {Q : Fin n → Prop}
    (ha : BottomBridgeArms R.graph R.forest u v Q) :
    BottomBridgeArms R.afterGraph R.after u v Q := by
  obtain ⟨p, q, hp, hq, hd, hpQ, hqQ⟩ := ha
  have hpf : R.forest.parent (R.input.liftPath p).first = (R.input.liftPath p).first := by
    change R.forest.parent p.first = p.first
    rw [hp.1]
    exact R.forest.root_fixed u
  have hqf : R.forest.parent (R.input.liftPath q).first = (R.input.liftPath q).first := by
    change R.forest.parent q.first = q.first
    rw [hq.1]
    exact R.forest.root_fixed v
  have hpfix : ∀ x, p.Contains x → R.forest.root x = x := by
    rintro x ⟨j, rfl⟩
    exact R.forest.root_of_fixed _ (R.invariant.path_fixed (R.input.liftPath p) hpf j)
  have hqfix : ∀ x, q.Contains x → R.forest.root x = x := by
    rintro x ⟨j, rfl⟩
    exact R.forest.root_of_fixed _ (R.invariant.path_fixed (R.input.liftPath q) hqf j)
  obtain ⟨a, haf, _, hab, hav⟩ := R.transport_bottom_path p hpfix hp.2
  obtain ⟨b, hbf, _, hbb, hbv⟩ := R.transport_bottom_path q hqfix hq.2
  refine ⟨a, b, ⟨?_, hab⟩, ⟨?_, hbb⟩, ?_, ?_, ?_⟩
  · exact haf.trans ((congrArg R.after.root hp.1).trans (R.after_root_old_root u))
  · exact hbf.trans ((congrArg R.after.root hq.1).trans (R.after_root_old_root v))
  · exact fun w ha hb => hd w (hav w ha) (hbv w hb)
  · exact fun w hw => hpQ w (hav w hw)
  · exact fun w hw => hqQ w (hbv w hw)

end MaximumMatching.Search.ActivePetalRecord

end ActivePetalTransport

section ActivePetalState

/-! The actual MAX state and computed arms after a live petal event. The full
semantic representation is reconstructed from those runtime arms and the
preserved root bound. -/
namespace MaximumMatching.Search.ActivePetalRecord
variable {n i cut : Nat} {G : Graph (Fin n)} {M : Matching G} [DecidableRel G.Adj]

/-- Execute the current MAX update and retain its full matching invariants. -/
def afterBucket (R : ActivePetalRecord M i cut)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) : CurrentBucketState M i cut where
  state := R.maxEvent.1
  forest := R.after
  stage := by
    obtain ⟨P⟩ := R.input.B.represented
    exact (R.maxEvent_correct_of_current P hc htop hstageTen).1
  bud := by
    obtain ⟨P⟩ := R.input.B.represented
    exact (R.maxEvent_correct_of_current P hc htop hstageTen).2.1
  represented := by
    obtain ⟨P⟩ := R.input.B.represented
    exact ⟨CurrentBridgeRepresentation.ofOperationalArms
      (OperationalArms.afterActiveMax R hc htop hstageTen)
      (R.maxEvent_correct_of_current P hc htop hstageTen).1
      (R.maxEvent_correct_of_current P hc htop hstageTen).2.1
      hstageTen (R.maxEvent_high P)⟩

theorem afterBucket_graph (R : ActivePetalRecord M i cut)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) :
    predecessorGraph (R.afterBucket hc htop hstageTen).state
      (R.afterBucket hc htop hstageTen).forest (R.afterBucket hc htop hstageTen).bud =
      predecessorGraph R.prior R.after R.after_invariant :=
  predecessorGraph_eq_of_fields R.after_invariant (R.afterBucket hc htop hstageTen).bud
    (funext R.maxEvent_minLabel) (maxProcessVertices_predecessors M i R.newRoots R.prior)

/-- The next live node uses the actual updated labels, forest, stored routes,
and surviving fixed roots. Every live root still reaches a live bottom. -/
def afterPetal (R : ActivePetalRecord M i cut)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) : ActiveSearchState M i cut where
  B := R.afterBucket hc htop hstageTen
  A := OperationalArms.afterActiveMax R hc htop hstageTen
  live := R.afterLive
  live_fixed := fun v hv => ((R.mem_afterLive v).1 hv).2
  reach := by
    rw [R.afterBucket_graph hc htop hstageTen]
    exact R.after_reach

theorem afterPetal_graph (R : ActivePetalRecord M i cut)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) :
    (R.afterPetal hc htop hstageTen).graph = R.afterGraph := by
  change DDFS.RecursiveRemoval.restricted
    (predecessorGraph (R.afterBucket hc htop hstageTen).state
      (R.afterBucket hc htop hstageTen).forest (R.afterBucket hc htop hstageTen).bud) R.afterLive = _
  rw [R.afterBucket_graph hc htop hstageTen]

theorem afterPetal_monotone (R : ActivePetalRecord M i cut)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) :
    R.input.Monotone (R.afterPetal hc htop hstageTen) :=
  ⟨R.after_root_congr, R.after_root_inactive⟩

theorem afterPetal_accounted (R : ActivePetalRecord M i cut)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) :
    (R.afterPetal hc htop hstageTen).Accounted R.left R.right :=
  Or.inl R.after_trigger_equal

theorem afterPetal_bucket_mono (R : ActivePetalRecord M i cut)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)
    (u v : Fin n) (t : Nat) (h : (u, v) ∈ R.prior.bucket t) :
    (u, v) ∈ (R.afterPetal hc htop hstageTen).B.state.bucket t :=
  R.maxEvent_bucket_mono u v t h

/-- Vertex-contained live arms survive the computed contraction. The MAX
assignment changes neither minimum labels nor predecessor lists. -/
theorem afterPetal_liveBridgeArms (R : ActivePetalRecord M i cut)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)
    {u v : Fin n} {Q : Fin n → Prop} (h : R.input.LiveBridgeArms u v Q) :
    (R.afterPetal hc htop hstageTen).LiveBridgeArms u v Q := by
  refine ⟨?_, ?_, ?_⟩
  · have hh := R.after_root_live (R.forest.root u) h.1
    rwa [R.after_root_congr _ _ (R.forest.root_idempotent u)] at hh
  · have hh := R.after_root_live (R.forest.root v) h.2.1
    rwa [R.after_root_congr _ _ (R.forest.root_idempotent v)] at hh
  · change BottomBridgeArms (R.afterPetal hc htop hstageTen).graph R.after u v Q
    rw [R.afterPetal_graph hc htop hstageTen]
    exact R.transport_bottom_bridge_arms h.2.2

end MaximumMatching.Search.ActivePetalRecord

end ActivePetalState

section BlockingBucket

/-! The deletion-aware continuation of the current bridge bucket. Each live
trigger runs DDFS on the current restricted graph. A bottleneck updates MAX
and contracts that live petal; disjoint bottom arms recover an augmentation,
remove its root fibers, and recursively prune predecessors before the next
trigger. The matching and MIN labels are held fixed throughout this phase. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G} {i cut : Nat}
    [DecidableRel G.Adj]

/-- Scan the supplied current-level bridges once, continuing after every
recovered augmentation. The result carries the proved accounting and
surviving-path invariant of the actual computed execution. -/
def runBlockingBucket
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)
    (S : ActiveSearchState M i cut) (es : List (Fin n × Fin n))
    (hqueued : ∀ e, e ∈ es → e ∈ S.B.state.bucket (2 * i + 1)) :
    BlockingBucketResult S es :=
  match es with
  | [] => .done S
  | (u, v) :: rest =>
    have he := hqueued (u, v) List.mem_cons_self
    have hrest : ∀ e, e ∈ rest → e ∈ S.B.state.bucket (2 * i + 1) :=
      fun e h => hqueued e (List.mem_cons_of_mem (u, v) h)
    if hsame : S.B.forest.root u = S.B.forest.root v then
      (runBlockingBucket hc htop hstageTen S rest hrest).skip (Or.inl hsame)
    else if hu : S.B.forest.root u ∈ S.live then
      if hv : S.B.forest.root v ∈ S.live then
        match hout : DDFS.Machine.executeFull S.reach (S.B.forest.root u) (S.B.forest.root v) with
        | .disjoint p q hp hq hd =>
          let z := S.recoverLivePath htop hstageTen u v he hu hv p q hp hq hd
          let T := S.remove (S.pathRoots z.val)
          let result := runBlockingBucket hc htop hstageTen T rest hrest
          let recovered := BlockingBucketResult.prependRemoved S z.val z.property.1 z.property.2.1
            (fun j => z.property.2.2.1 _ ⟨j, rfl⟩)
            (fun j => z.property.2.2.2.1 _ ⟨j, rfl⟩) result
          recovered.account (by
            apply Or.inr
            apply Or.inl
            apply result.monotone.inactive u
            intro hlive
            have hn := (S.remove_live (S.pathRoots z.val) (S.B.forest.root u) hlive).2
            apply hn
            obtain ⟨j, hj⟩ := z.property.2.2.2.2.1
            apply (S.mem_pathRoots z.val _).2
            exact ⟨j, (congrArg S.B.forest.root hj).trans (S.B.forest.root_idempotent u)⟩)
        | .bottleneck b selected trees highest region =>
          let R : ActivePetalRecord M i cut := {
            input := S, left := u, right := v, queued := he,
            left_live := hu, right_live := hv, different := hsame,
            bottleneck := b, selected := selected, trees := trees,
            highest := highest, region := region, computed := hout }
          let T := R.afterPetal hc htop hstageTen
          let result := runBlockingBucket hc htop hstageTen T rest (fun e h =>
            R.afterPetal_bucket_mono hc htop hstageTen e.1 e.2 (2 * i + 1) (hrest e h))
          let advanced := BlockingBucketResult.advance
            (R.afterPetal_monotone hc htop hstageTen)
            (R.afterPetal_bucket_mono hc htop hstageTen)
            (fun _ _ _ h => R.afterPetal_liveBridgeArms hc htop hstageTen h) result
          advanced.account ((R.afterPetal_accounted hc htop hstageTen).mono result.monotone)
      else
        (runBlockingBucket hc htop hstageTen S rest hrest).skip (Or.inr (Or.inr hv))
    else
      (runBlockingBucket hc htop hstageTen S rest hrest).skip (Or.inr (Or.inl hu))
termination_by es.length

/-- A complete supplied bucket produces a maximal family of vertex-disjoint
shortest augmentations, using the initial vertex-contained arm coverage. -/
theorem runBlockingBucket_maximalShortest
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)
    (S : ActiveSearchState M i cut) (es : List (Fin n × Fin n))
    (hqueued : ∀ e, e ∈ es → e ∈ S.B.state.bucket (2 * i + 1))
    (hcover : ∀ p : AltPath M, p.Augmenting → p.length = 2 * i + 1 →
      ∃ u v, (u, v) ∈ es ∧ S.LiveBridgeArms u v (fun w => ∃ j, p.vertex j = w)) :
    (runBlockingBucket hc htop hstageTen S es hqueued).family.MaximalShortest (2 * i + 1) :=
  (runBlockingBucket hc htop hstageTen S es hqueued).maximalShortest (hstageTen ▸ htop) hcover

end MaximumMatching.Search

end BlockingBucket

section BlockingPhase

/-! Complete deletion-aware maximal shortest blocking phases and their outer
matching solver. The first computed witness is retained and expanded once;
continued live DDFS uses the same labels, matching and current bridge bucket.
The outer driver proves termination and maximum cardinality. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}
variable [DecidableRel G.Adj]

/-- Recover the already computed first witness, delete its root classes, and
continue the current bucket. Previously processed triggers are merely skipped
because their roots were merged; the first found trigger is now inactive. -/
def resumeBlockingPhase {i cut : Nat}
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)
    (B : CurrentBucketState M i cut) (A : OperationalArms M B.state B.forest)
    (W : CurrentBucketWitness B) (es : List (Fin n × Fin n))
    (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1)) :
    BlockingBucketResult (ActiveSearchState.initial B A) es := by
  let S := ActiveSearchState.initial B A
  let p := W.recover A hc htop hstageTen
  let T := S.remove (S.pathRoots p.val)
  let result := runBlockingBucket hc htop hstageTen T es hqueued
  exact BlockingBucketResult.prependRemoved S p.val p.property.1 p.property.2.2.2.1
    (fun j => ActiveSearchState.initial_root_live B A (p.val.vertex j))
    (fun j => (W.recover_coverage A hc htop hstageTen).2.2 _ ⟨j, rfl⟩) result

theorem resumeBlockingPhase_maximalShortest {i cut : Nat}
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)
    (B : CurrentBucketState M i cut) (A : OperationalArms M B.state B.forest)
    (W : CurrentBucketWitness B) (es : List (Fin n × Fin n))
    (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (hcover : ∀ p : AltPath M, p.Augmenting → p.length = 2 * i + 1 →
      ∃ u v, (u, v) ∈ es ∧
        BottomBridgeArms (predecessorGraph B.state B.forest B.bud) B.forest u v
          (fun w => ∃ j, p.vertex j = w)) :
    (resumeBlockingPhase hc htop hstageTen B A W es hqueued).family.MaximalShortest (2 * i + 1) := by
  apply BlockingBucketResult.maximalShortest _ (hstageTen ▸ htop)
  intro p hp hlen
  obtain ⟨u, v, he, ha⟩ := hcover p hp hlen
  exact ⟨u, v, he, ActiveSearchState.initial_root_live B A u,
    ActiveSearchState.initial_root_live B A v, ActiveSearchState.initial_arms B A ha⟩

/-- Computed family with its two search contracts proved from execution. -/
structure BlockingPhaseResult (M : Matching G) where
  family : AugmentingFamily M
  complete : family.count = 0 → M.NoAugmentingPath
  shortest : family.count ≠ 0 → ∃ l, family.MaximalShortest l

/-- Execute one full phase. Length one uses the greedy free-edge scan; higher
levels use MIN/MAX until the first witness, followed by deletion-aware DDFS. -/
def blockingPhaseResult (M : Matching G) : BlockingPhaseResult M :=
  let f := freeEdgePhase M
  if hz : f.count = 0 then
    let hnoaug := freeEdgePhase_empty_no_short M hz
    match locateBlockingPhase (firstHigherState M hnoaug) (firstHigherArms M hnoaug) with
    | .maximum hn => ⟨.empty, fun _ => hn, fun h => False.elim (h rfl)⟩
    | .found i _cut hc ht hstageTen B A W es hqueued hcover =>
      let result := resumeBlockingPhase hc ht hstageTen B A W es hqueued
      have hmax := resumeBlockingPhase_maximalShortest hc ht hstageTen B A W es hqueued hcover
      ⟨result.family, fun hz' => False.elim (Nat.add_one_ne_zero _ hz'),
        fun _ => ⟨2 * i + 1, hmax⟩⟩
  else
    ⟨f, fun he => False.elim (hz he), fun _ => ⟨1, freeEdgePhase_maximalShortest M⟩⟩

def blockingPhase (M : Matching G) : AugmentingFamily M := (blockingPhaseResult M).family

theorem blockingPhase_complete : PhaseDriver.Complete (blockingPhase (G := G)) :=
  fun M => (blockingPhaseResult M).complete

theorem blockingPhase_shortestBlocking : PhaseDriver.ShortestBlocking (blockingPhase (G := G)) :=
  fun M => (blockingPhaseResult M).shortest

/-- Repeated actual blocking phases, with executable matching flips. -/
def runBlockingPhases (M : Matching G) : PhaseDriver.Result G :=
  PhaseDriver.run (blockingPhase (G := G)) M

theorem runBlockingPhases_isMaximum (M : Matching G) :
    (runBlockingPhases M).matching.IsMaximum :=
  PhaseDriver.run_isMaximum _ blockingPhase_complete M

/-- A total maximum-cardinality matching solver for finite simple graphs. -/
def maximumMatching (G : Graph (Fin n)) [DecidableRel G.Adj] : Matching G :=
  (runBlockingPhases (Matching.empty G)).matching

theorem maximumMatching_isMaximum (G : Graph (Fin n)) [DecidableRel G.Adj] :
    (maximumMatching G).IsMaximum := runBlockingPhases_isMaximum (Matching.empty G)

end MaximumMatching.Search

end BlockingPhase
