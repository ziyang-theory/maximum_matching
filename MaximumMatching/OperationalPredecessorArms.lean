import MaximumMatching.OperationalArms
import MaximumMatching.SearchStage

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
