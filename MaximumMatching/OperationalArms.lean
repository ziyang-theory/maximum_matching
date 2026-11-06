import MaximumMatching.CurrentBridgeRepresentation
import MaximumMatching.CurrentBucket
import MaximumMatching.MatchingSearchGraph
import MaximumMatching.PetalPathTransport
import MaximumMatching.SearchStage
import MaximumMatching.WeightedRecovery

section OperationalArms

/-! Computational path data for known parity labels. Each arm ends at the
actual current bud and records the exact matching-path length. These data
are distinct from the erased existential representation used for correctness. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

/-- A computed route from a labeled vertex to its current root. -/
structure ParityArm (M : Matching G) (s : State V) (F : BudForest V)
    (v : V) (k : Nat) where
  segment : ParitySegment M
  first : segment.first = v
  last : segment.last = F.root v
  length : segment.length + (s.minLabel (F.root v)).getD 0 = k
  phase : segment.phase % 2 = (k + 1) % 2
  end_phase : (segment.phase + segment.length) % 2 =
    ((s.minLabel (F.root v)).getD 0 + 1) % 2
  interior : ∀ j : Fin (segment.length + 1), j.val < segment.length →
    F.root (segment.vertex j) = F.root v

/-- Runtime arms for every available parity label. Their proofs certify the
computed segments; neither the segment nor its vertex map is erased. -/
structure OperationalArms (M : Matching G) (s : State V) (F : BudForest V) where
  get : ∀ v parity k, parityLabel s v parity = some k → ParityArm M s F v k

namespace ParityArm

def singleton (s : State V) (F : BudForest V) (v : V) (k : Nat)
    (hroot : F.root v = v) (hmin : s.minLabel v = some k) : ParityArm M s F v k where
  segment := ParitySegment.trivial M v (k + 1)
  first := rfl
  last := hroot.symm
  length := by simp only [ParitySegment.trivial, hroot, hmin, Option.getD_some, Nat.zero_add]
  phase := rfl
  end_phase := by simp only [ParitySegment.trivial, hroot, hmin, Option.getD_some, Nat.add_zero]
  interior := by intro j hj; exact False.elim (Nat.not_lt_zero _ hj)

end ParityArm

namespace OperationalArms

/-- Initial parity labels are all minimum labels at singleton roots, so their
computed arms have length zero. -/
def initial (M : Matching G) : OperationalArms M (Search.initial M)
    (uncontractedForest (Search.initial M)) where
  get v parity k hk := by
    have hmin : (Search.initial M).minLabel v = some k := by
      unfold parityLabel at hk
      cases hm : (Search.initial M).minLabel v with
      | none => simp [hm] at hk
      | some l =>
        rw [hm] at hk
        change (if l % 2 = parity then some l else none) = some k at hk
        split at hk
        · exact hk
        · contradiction
    exact ParityArm.singleton _ _ v k
      ((uncontractedForest (Search.initial M)).root_of_fixed v rfl) hmin

end OperationalArms
end MaximumMatching.Search

end OperationalArms

section OperationalMinArms

/-! Preserve computed parity arms through actual MIN scans and forest rank
updates. Old arms retain their vertices; a newly labeled singleton root gets
its concrete zero-length arm. No semantic path choice occurs at runtime. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

namespace ParityArm

/-- Reuse the same computed segment when roots and its root label are
unchanged. Only the state and forest certificates are transported. -/
def withState {s s' : State V} {F F' : BudForest V} {v : V} {k : Nat}
    (a : ParityArm M s F v k) (hroots : ∀ x, F'.root x = F.root x)
    (hlabel : s'.minLabel (F'.root v) = s.minLabel (F.root v)) :
    ParityArm M s' F' v k where
  segment := a.segment
  first := a.first
  last := a.last.trans (hroots v).symm
  length := by rw [hlabel]; exact a.length
  phase := a.phase
  end_phase := by rw [hlabel]; exact a.end_phase
  interior j hj := (hroots _).trans ((a.interior j hj).trans (hroots v).symm)

end ParityArm

section Finite
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G} [DecidableRel G.Adj]

theorem scanLevelWithBuds_assigned_root_label (i : Nat) (s : State (Fin n))
    (F : BudForest (Fin n)) (h : BudGraphInvariant M i s F) (v : Fin n) (k : Nat)
    (hk : s.minLabel v = some k) :
    (scanLevelWithBuds M i s F h).1.minLabel ((scanLevelWithBuds M i s F h).2.root v) =
      s.minLabel (F.root v) := by
  rw [scanLevelWithBuds_root]
  obtain ⟨j, hj⟩ := h.rootAssigned v k hk
  exact (scanCandidates_preserves_assigned_minLabel (allCandidates n) s i h.minInvariant _ j hj).trans hj.symm

namespace OperationalArms

/-- Execute the actual MIN scan while carrying its computed parity arms.
An old assigned vertex reuses its old segment. Any new vertex was a fixed
root, and its first label has the zero-length singleton segment. -/
def afterMin {i : Nat} {s : State (Fin n)} {F : BudForest (Fin n)}
    (A : OperationalArms M s F) (h : BudGraphInvariant M i s F)
    (hmaxmin : MaxLabelsHaveMin s) :
    OperationalArms M (scanLevelWithBuds M i s F h).1 (scanLevelWithBuds M i s F h).2 where
  get v parity k hk := by
    cases hm : s.minLabel v with
    | none =>
      have hmax : s.maxLabel v = none := by
        cases hh : s.maxLabel v with
        | none => rfl
        | some j =>
          obtain ⟨l, hl⟩ := hmaxmin v j hh
          rw [hm] at hl
          contradiction
      have hmax' : (scanLevelWithBuds M i s F h).1.maxLabel v = none :=
        (scanCandidates_maxLabel (allCandidates n) s i v).trans hmax
      have hnewmin : (scanLevelWithBuds M i s F h).1.minLabel v = some k := by
        unfold parityLabel at hk
        cases hn : (scanLevelWithBuds M i s F h).1.minLabel v with
        | none => simp [hn] at hk
        | some j =>
          rw [hn] at hk
          change (if j % 2 = parity then some j else do
            let l ← (scanLevelWithBuds M i s F h).1.maxLabel v
            if l % 2 = parity then some l else none) = some k at hk
          rw [hmax'] at hk
          split at hk
          · exact hk
          · contradiction
      exact ParityArm.singleton _ _ v k
        ((scanLevelWithBuds_root M i s F h v).trans (F.root_of_fixed v (h.unknown_fixed v hm))) hnewmin
    | some j =>
      have hn : (scanLevelWithBuds M i s F h).1.minLabel v = some j :=
        scanCandidates_preserves_assigned_minLabel (allCandidates n) s i h.minInvariant v j hm
      have hmax : (scanLevelWithBuds M i s F h).1.maxLabel = s.maxLabel :=
        funext (scanCandidates_maxLabel (allCandidates n) s i)
      have hkold : parityLabel s v parity = some k := by
        simpa only [parityLabel, hm, hn, hmax] using hk
      exact (A.get v parity k hkold).withState (scanLevelWithBuds_root M i s F h)
        (scanLevelWithBuds_assigned_root_label i s F h v j hm)

end OperationalArms
end Finite
end MaximumMatching.Search

end OperationalMinArms

section OperationalPredecessorArms

/-! Recover weighted predecessor edges by a stored predecessor followed by
its computed parity arm. No semantic shortest-path witness supplies data. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}
    {i : Nat} {s : State (Fin n)} {F : BudForest (Fin n)}

theorem ParityArm.root_all {v : Fin n} {k : Nat} (a : ParityArm M s F v k)
    (j : Fin (a.segment.length + 1)) : F.root (a.segment.vertex j) = F.root v := by
  by_cases hj : j.val < a.segment.length
  · exact a.interior j hj
  · have he : j = ⟨a.segment.length, by omega⟩ := Fin.ext (show j.val = a.segment.length by have := j.isLt; omega)
    change F.root (a.segment.vertex j) = _
    rw [he]
    change F.root a.segment.last = _
    rw [a.last, F.root_idempotent]

/-- Every stored predecessor's honest prefix label is operationally available
from earlier MIN/MAX levels. -/
theorem StageState.predecessor_parityLabel
    (hs : StageState M (i + 1) (2 * i + 1) s)
    (v u : Fin n) (N : Nat) (hv : s.minLabel v = some N)
    (hp : Predecessor M u v) :
    0 < N ∧ parityLabel s u ((N - 1) % 2) = some (N - 1) ∧
      G.Adj v u ∧ (M.mate v = some u ↔ (N + 1) % 2 = 1) := by
  obtain ⟨p, hpv, hpm, hpos, hpu⟩ := hp
  have hlen : p.length = N := Option.some.inj
    (hpm.symm.trans (hs.min.1.1 v N hv))
  have hk : N - 1 ≤ i := by have := hs.minBound v N hv; omega
  have hhon := (p.honest_iff_level ⟨p.length - 1, by omega⟩).1
    (p.minlevel_last_predecessor_honest (by rw [hpv]; exact hpm) hpos)
  have hlu : level M ((N - 1) % 2) u = some (N - 1) := by
    rw [hpu] at hhon
    simpa only [hlen] using hhon
  have hav := frontierAvailable_of_prior_levels s (N - 1)
    (fun w k hw hki => hs.min.2.1 w k hw (by omega))
    (fun w t hwt ht => hs.maxComplete w t hwt (by omega)) u hlu
  have hlast : (⟨p.length - 1 + 1, by omega⟩ : Fin (p.length + 1)) =
      ⟨p.length, by omega⟩ := Fin.ext (show p.length - 1 + 1 = p.length by omega)
  have ha := p.adjacent ⟨p.length - 1, by omega⟩
  have hm := p.alternating ⟨p.length - 1, by omega⟩
  rw [hlast] at ha hm
  change G.Adj (p.vertex ⟨p.length - 1, by omega⟩) p.last at ha
  change (M.mate (p.vertex ⟨p.length - 1, by omega⟩) = some p.last ↔ _) at hm
  rw [hpu, hpv] at ha hm
  refine ⟨by omega, hav, G.symm ha, ?_⟩
  constructor
  · intro h
    have hh := hm.1 (M.symm h)
    change (p.length - 1) % 2 = 1 at hh
    omega
  · intro h
    exact M.symm (hm.2 (by change (p.length - 1) % 2 = 1; omega))

namespace OperationalArms

/-- Recover one fixed-root graph edge as a concrete parity segment. -/
def recoverEdge (A : OperationalArms M s F)
    (hs : StageState M (i + 1) (2 * i + 1) s)
    (h : BudGraphInvariant M (i + 1) s F) {v w : Fin n}
    (he : (DDFS.fixedRootGraph (predecessorGraph s F h) F).Edge v w) :
    { a : ParitySegment M // a.first = v ∧ a.last = w ∧
      a.length + (s.minLabel w).getD 0 = (s.minLabel v).getD 0 ∧
      a.phase % 2 = ((s.minLabel v).getD 0 + 1) % 2 ∧
      (a.phase + a.length) % 2 = ((s.minLabel w).getD 0 + 1) % 2 ∧
      ∀ j : Fin (a.length + 1), 0 < j.val → j.val < a.length → F.root (a.vertex j) = w } := by
  let N := (s.minLabel v).getD 0
  have hv : s.minLabel v = some N := by
    cases hv : s.minLabel v with
    | none =>
      have hh := he.1.1
      rw [hv] at hh
      contradiction
    | some k => simp only [N, hv, Option.getD_some]
  let u := h.recoverEdgePredecessor v w he.1
  have hp := h.minInvariant.2.2.2.2 u.val v u.property.1
  have hf := hs.predecessor_parityLabel v u.val N hv hp
  let a := A.get u.val ((N - 1) % 2) (N - 1) hf.2.1
  let e := ParitySegment.ofEdge v u.val (N + 1) hf.2.2.1 hf.2.2.2
  have hj : e.last = a.segment.first := a.first.symm
  have hphase : (e.phase + e.length) % 2 = a.segment.phase % 2 := by
    have hap := a.phase
    change (N + 1 + 1) % 2 = a.segment.phase % 2
    omega
  have hvw : v ≠ w := by
    intro hsame
    have hh := h.edge_decreases he.1
    rw [hsame] at hh
    exact Nat.lt_irrefl _ hh
  have hdis : ∀ (j : Fin (e.length + 1)) (k : Fin (a.segment.length + 1)),
      0 < k.val → e.vertex j ≠ a.segment.vertex k := by
    intro j k hk hsame
    by_cases hj0 : j.val = 0
    · have hvk : v = a.segment.vertex k := by simpa [e, ParitySegment.ofEdge, hj0] using hsame
      have hr := a.root_all k
      rw [← hvk, he.2.1, u.property.2] at hr
      exact hvw hr
    · have huk : u.val = a.segment.vertex k := by simpa [e, ParitySegment.ofEdge, hj0] using hsame
      have heq := a.segment.injective ⟨0, by omega⟩ k (a.first.trans huk)
      have hh : 0 = k.val := congrArg Fin.val heq
      omega
  let z := e.append a.segment hphase hj hdis
  have han : a.segment.length + (s.minLabel w).getD 0 = N - 1 := by
    simpa only [u.property.2] using a.length
  refine ⟨z, e.append_first _ _ _ _, (e.append_last _ _ _ _).trans (a.last.trans u.property.2),
    ?_, rfl, ?_, ?_⟩
  · change 1 + a.segment.length + (s.minLabel w).getD 0 = N
    omega
  · have hh := a.end_phase
    rw [u.property.2] at hh
    change (N + 1 + (1 + a.segment.length)) % 2 = _
    omega
  · intro j hj0 _hjl
    change F.root ((e.append a.segment hphase hj hdis).vertex j) = w
    by_cases hje : j.val ≤ e.length
    · have hj1 : j.val = 1 := by change j.val ≤ 1 at hje; omega
      simpa [ParitySegment.append, dite_eq_left hje, e, ParitySegment.ofEdge,
        hj1, Nat.one_ne_zero, ite_false] using u.property.2
    · have hr := a.root_all ⟨j.val - e.length, by
        have := j.isLt; change j.val < e.length + a.segment.length + 1 at this; omega⟩
      simpa only [ParitySegment.append, dite_eq_right hje, u.property.2] using hr

/-- A computed weighted matching graph from actual stored parity arms. -/
def weighted (A : OperationalArms M s F)
    (hs : StageState M (i + 1) (2 * i + 1) s)
    (h : BudGraphInvariant M (i + 1) s F) :
    DDFS.FiberWeightedMatching M (DDFS.fixedRootGraph (predecessorGraph s F h) F) F where
  phase v := (s.minLabel v).getD 0 + 1
  segment he := (A.recoverEdge hs h he).val
  first he := (A.recoverEdge hs h he).property.1
  last he := (A.recoverEdge hs h he).property.2.1
  start_phase he := (A.recoverEdge hs h he).property.2.2.2.1
  end_phase he := (A.recoverEdge hs h he).property.2.2.2.2.1
  interior he := (A.recoverEdge hs h he).property.2.2.2.2.2

theorem weighted_drop (A : OperationalArms M s F)
    (hs : StageState M (i + 1) (2 * i + 1) s)
    (h : BudGraphInvariant M (i + 1) s F) {v w : Fin n}
    (he : (DDFS.fixedRootGraph (predecessorGraph s F h) F).Edge v w) :
    ((A.weighted hs h).segment he).length + (s.minLabel w).getD 0 = (s.minLabel v).getD 0 :=
  (A.recoverEdge hs h he).property.2.2.1

end OperationalArms
end MaximumMatching.Search

end OperationalPredecessorArms

section OperationalBridgeArms

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
def recoverBridgePathWithCore (A : OperationalArms M s F) (hs : LabelsSound M s)
    (W : DDFS.FiberWeightedMatching M (DDFS.fixedRootGraph (predecessorGraph s F h) F) F)
    (hphase : ∀ v, W.phase v % 2 = ((s.minLabel v).getD 0 + 1) % 2)
    (hdrop : ∀ {u v} (he : (DDFS.fixedRootGraph (predecessorGraph s F h) F).Edge u v),
      (W.segment he).length + (s.minLabel v).getD 0 = (s.minLabel u).getD 0)
    (u v : V) (t : Nat) (hadj : G.Adj u v) (ht : edgeTenacity M s u v = some t)
    (p q : DDFS.Path (predecessorGraph s F h))
    (hpf : p.first = F.root u) (hqf : q.first = F.root v)
    (hqb : (predecessorGraph s F h).level q.last = 0) (hdis : p.Disjoint q) :
    { z : AltPath M // z.first = q.last ∧ z.last = p.last ∧
      z.length + (s.minLabel p.last).getD 0 = t ∧ z.ContainsEdge u v ∧
      (∀ w, (∃ j, z.vertex j = w) → p.Contains (F.root w) ∨ q.Contains (F.root w)) ∧
      (∀ w, p.Contains w ∨ q.Contains w → ∃ j, z.vertex j = w) } := by
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
  obtain ⟨z, hzf, hzl, hzn, _, hedge, hfibers, hcore⟩ := W.recoverBridgeDetourOfPotentialWithCore pr qr
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
  exact ⟨z, hzf, hzl, hzn, (z.containsEdge_symm v u).1 hedge, hfibers, hcore⟩

/-- Compatibility interface for the same computed matching path. -/
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
  let z := A.recoverBridgePathWithCore hs W hphase hdrop u v t hadj ht p q hpf hqf hqb hdis
  exact ⟨z.val, z.property.1, z.property.2.1, z.property.2.2.1, z.property.2.2.2.1⟩

/-- Recover the actual shortest augmenting matching path when both computed
DDFS arms reach free bottoms. -/
def recoverShortestAugmentingWithCore (A : OperationalArms M s F) (hs : LabelsSound M s)
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
      (∀ r : AltPath M, r.Augmenting → z.length ≤ r.length) ∧
      (∀ w, (∃ j, z.vertex j = w) → p.Contains (F.root w) ∨ q.Contains (F.root w)) ∧
      (∀ w, p.Contains w ∨ q.Contains w → ∃ j, z.vertex j = w) } := by
  obtain ⟨z, hzf, hzl, hzn, hedge, hfibers, hcore⟩ := A.recoverBridgePathWithCore hs W hphase hdrop u v t hadj ht
    p q hp.1 hq.1 hq.2 hdis
  have hpb : (s.minLabel p.last).getD 0 = 0 := hp.2
  have hlen : z.length = t := by omega
  have hpa : ∃ k, s.minLabel p.first = some k := by
    rw [hp.1]
    obtain ⟨⟨k, hk⟩, _⟩ := edgeTenacity_has_minLabels s u v t ht
    exact h.rootAssigned u k hk
  have hfree : M.Free z.last := hzl ▸ h.path_bottom_free p hpa hp.2
  exact ⟨z, ⟨by rw [hlen]; exact hodd, hfree⟩, hzf, hzl, hlen, hedge,
    (fun r hr => hlen ▸ hbound r hr), hfibers, hcore⟩

/-- Compatibility interface retaining shortestness and the computed path. -/
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
  let z := A.recoverShortestAugmentingWithCore hs W hphase hdrop u v t hadj ht hodd hbound
    p q hp hq hdis
  exact ⟨z.val, z.property.1, z.property.2.1, z.property.2.2.1,
    z.property.2.2.2.1, z.property.2.2.2.2.1, z.property.2.2.2.2.2.1⟩

end OperationalArms

namespace CurrentBucketWitness
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}
    {i cut : Nat} {B : CurrentBucketState M i cut}

/-- Turn this exact raw DDFS output into a computed shortest alternating
matching path, using the operational arms stored alongside its search state. -/
def recoverWithCore (certificate : CurrentBucketWitness B)
    (A : OperationalArms M B.state B.forest)
    (_hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) :
    { p : AltPath M // p.Augmenting ∧ p.first = certificate.green.last ∧
      p.last = certificate.red.last ∧ p.length = 2 * i + 1 ∧
      p.ContainsEdge certificate.left certificate.right ∧
      (∀ q : AltPath M, q.Augmenting → p.length ≤ q.length) ∧
      (∀ w, (∃ j, p.vertex j = w) →
        certificate.red.Contains (B.forest.root w) ∨ certificate.green.Contains (B.forest.root w)) ∧
      (∀ w, certificate.red.Contains w ∨ certificate.green.Contains w → ∃ j, p.vertex j = w) } := by
  have hb := B.stage.classification.2.2 (2 * i + 1) certificate.left certificate.right certificate.queued
  have hk := B.stage.current_bridge_known certificate.left certificate.right hb.1 hb.2
  exact A.recoverShortestAugmentingWithCore B.stage.min.1 (A.weighted B.stage B.bud)
    (fun _ => rfl) (fun he => A.weighted_drop B.stage B.bud he)
    certificate.left certificate.right (2 * i + 1) hb.1.1 hk (by omega)
    (by simpa only [hstageTen] using htop) certificate.red certificate.green
    certificate.red_bottom certificate.green_bottom certificate.disjoint

/-- Compatibility interface for the same recovered certificate path. -/
def recover (certificate : CurrentBucketWitness B)
    (A : OperationalArms M B.state B.forest)
    (_hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) :
    { p : AltPath M // p.Augmenting ∧ p.first = certificate.green.last ∧
      p.last = certificate.red.last ∧ p.length = 2 * i + 1 ∧
      p.ContainsEdge certificate.left certificate.right ∧
      ∀ q : AltPath M, q.Augmenting → p.length ≤ q.length } := by
  let p := certificate.recoverWithCore A _hc htop hstageTen
  exact ⟨p.val, p.property.1, p.property.2.1, p.property.2.2.1,
    p.property.2.2.2.1, p.property.2.2.2.2.1, p.property.2.2.2.2.2.1⟩

end CurrentBucketWitness
end MaximumMatching.Search

end OperationalBridgeArms

section OperationalRepresentation

/-! Runtime arms provide the full current-bridge representation. This permits
later graph refinements to reuse computed path data without extracting any
semantic witness as executable data. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}
    {i cut : Nat} {s : State (Fin n)} {F : BudForest (Fin n)}

/-- Construct the semantic current-bridge interface from computed parity
arms, operational label invariants, and the lower-cutoff root bound. -/
def CurrentBridgeRepresentation.ofOperationalArms
    (A : OperationalArms M s F) (hs : StageState M (i + 1) (2 * i + 1) s)
    (h : BudGraphInvariant M (i + 1) s F)
    (hstageTen : cut + 2 = 2 * i + 1)
    (hhigh : ∀ v k, s.minLabel v = some k → levelLT (some cut) (tenacity M (F.root v))) :
    CurrentBridgeRepresentation M cut h where
  weighted := A.weighted hs h
  phase _ := rfl
  drop he := A.weighted_drop hs h he
  high := hhigh
  tops u v hb ht _hu _hv := by
    let T := A.bridgeArms hs.min.1 u v (2 * i + 1)
      (hs.current_bridge_known u v hb (by rw [← hstageTen]; exact ht))
    exact ⟨T.left, T.right, T.left_first, T.left_last, T.right_first, T.right_last,
      T.left_end_phase, T.right_end_phase, T.left_interior, T.right_interior,
      T.same_phase, T.bridge_phase, T.budget.trans hstageTen.symm⟩

end MaximumMatching.Search

end OperationalRepresentation

section RecoveryContainment

/-! Containment of the actual recovered matching path. Every compressed root
occurs on its expansion, and each expanded vertex belongs to a root on the
compressed path. These two directions give closure under current bud lookup. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

/-- Looking up the current bud of a path vertex stays on that same path. -/
def RootClosed (F : BudForest V) (p : AltPath M) : Prop :=
  ∀ v, (∃ j, p.vertex j = v) → ∃ j, p.vertex j = F.root v

/-- Two-way core coverage proves root closure without an assumption about
whole blossom membership or the choice of a shortest matching path. -/
theorem rootClosed_of_core_coverage (F : BudForest V) (p : AltPath M) (core : V → Prop)
    (hfibers : ∀ v, (∃ j, p.vertex j = v) → core (F.root v))
    (hcore : ∀ v, core v → ∃ j, p.vertex j = v) : RootClosed F p :=
  fun v hv => hcore (F.root v) (hfibers v hv)

/-- If every compressed root is live, the expansion avoids every dead fiber. -/
theorem recovered_fibers_live (F : BudForest V) (p : AltPath M) (core live : V → Prop)
    (hfibers : ∀ v, (∃ j, p.vertex j = v) → core (F.root v))
    (hlive : ∀ v, core v → live v) :
    ∀ v, (∃ j, p.vertex j = v) → live (F.root v) :=
  fun v hv => hlive (F.root v) (hfibers v hv)

namespace OperationalArms
variable {s : State V} {F : BudForest V} {cap : Nat} {h : BudGraphInvariant M cap s F}

/-- Exact core/fiber coverage for the compatibility API's computed path.
In particular the recovered path is closed under the current bud map. -/
theorem recoverShortestAugmenting_coverage (A : OperationalArms M s F) (hs : LabelsSound M s)
    (W : DDFS.FiberWeightedMatching M (DDFS.fixedRootGraph (predecessorGraph s F h) F) F)
    (hphase : ∀ v, W.phase v % 2 = ((s.minLabel v).getD 0 + 1) % 2)
    (hdrop : ∀ {u v} (he : (DDFS.fixedRootGraph (predecessorGraph s F h) F).Edge u v),
      (W.segment he).length + (s.minLabel v).getD 0 = (s.minLabel u).getD 0)
    (u v : V) (t : Nat) (hadj : G.Adj u v) (ht : edgeTenacity M s u v = some t)
    (hodd : t % 2 = 1) (hbound : AtMostShortestAugmenting M t)
    (p q : DDFS.Path (predecessorGraph s F h))
    (hp : p.ToBottom (F.root u)) (hq : q.ToBottom (F.root v)) (hdis : p.Disjoint q) :
    let z := (A.recoverShortestAugmenting hs W hphase hdrop u v t hadj ht hodd hbound p q hp hq hdis).val
    (∀ w, (∃ j, z.vertex j = w) → p.Contains (F.root w) ∨ q.Contains (F.root w)) ∧
      (∀ w, p.Contains w ∨ q.Contains w → ∃ j, z.vertex j = w) ∧ RootClosed F z := by
  let z := A.recoverShortestAugmentingWithCore hs W hphase hdrop u v t hadj ht hodd hbound p q hp hq hdis
  have hfibers := z.property.2.2.2.2.2.2.1
  have hcore := z.property.2.2.2.2.2.2.2
  exact ⟨hfibers, hcore, rootClosed_of_core_coverage F z.val _ hfibers hcore⟩

end OperationalArms

namespace CurrentBucketWitness
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}
    {i cut : Nat} {B : CurrentBucketState M i cut}

/-- The exact matching path recovered from this computed DDFS certificate
contains both compressed cores and is closed under the certificate's bud map. -/
theorem recover_coverage (certificate : CurrentBucketWitness B)
    (A : OperationalArms M B.state B.forest)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) :
    let p := (certificate.recover A hc htop hstageTen).val
    (∀ w, (∃ j, p.vertex j = w) →
      certificate.red.Contains (B.forest.root w) ∨ certificate.green.Contains (B.forest.root w)) ∧
      (∀ w, certificate.red.Contains w ∨ certificate.green.Contains w → ∃ j, p.vertex j = w) ∧
      RootClosed B.forest p := by
  let p := certificate.recoverWithCore A hc htop hstageTen
  have hfibers := p.property.2.2.2.2.2.2.1
  have hcore := p.property.2.2.2.2.2.2.2
  exact ⟨hfibers, hcore, rootClosed_of_core_coverage B.forest p.val _ hfibers hcore⟩

end CurrentBucketWitness
end MaximumMatching.Search

end RecoveryContainment
