import MaximumMatching.MatchingPathRecoveryTrees
import MaximumMatching.PetalPathTransport

/-! Recover original predecessor witnesses and descending petal tails from
stored MIN lists. Each choice scans only a concrete predecessor list; no
matching path is obtained from a semantic existential witness. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

namespace BudGraphInvariant
variable {cap : Nat} {s : State V} {F : BudForest V}

/-- Select the first stored predecessor realizing an actual contracted edge. -/
def recoverEdgePredecessor (h : BudGraphInvariant M cap s F) (v w : V)
    (he : (predecessorGraph s F h).Edge v w) :
    { u : V // u ∈ s.predecessors v ∧ F.root u = w } :=
  match hp : (s.predecessors v).find? (fun u => decide (F.root u = w)) with
  | some u => ⟨u, List.mem_of_find?_eq_some hp,
      of_decide_eq_true (List.find?_some (p := fun x => decide (F.root x = w)) hp)⟩
  | none => False.elim (by
      obtain ⟨u, hu, huw⟩ := List.mem_map.mp he.2
      have hn := List.find?_eq_none.mp hp u hu
      simp only [huw, decide_true] at hn
      contradiction)

/-- Choose the head of a nonempty stored predecessor list. Positive layer
and the MIN invariant prove that the empty-list case cannot occur. -/
def firstPredecessor (h : BudGraphInvariant M cap s F) (v : V)
    (hpos : 0 < (s.minLabel v).getD 0) :
    { u : V // u ∈ s.predecessors v ∧
      (predecessorGraph s F h).Edge v (F.root u) } :=
  match hl : s.predecessors v with
  | [] => False.elim (by
      obtain ⟨w, hw⟩ := h.outgoing v hpos
      obtain ⟨u, hu, _⟩ := List.mem_map.mp hw.2
      rw [hl] at hu
      exact List.not_mem_nil hu)
  | u :: us => ⟨u, List.mem_cons_self, (by
      have ha : (s.minLabel v).isSome = true := by
        cases hlabel : s.minLabel v with
        | none => simp only [hlabel, Option.getD_none] at hpos; omega
        | some k => rfl
      exact ⟨ha, List.mem_map.mpr ⟨u, by rw [hl]; exact List.mem_cons_self, rfl⟩⟩)⟩

end BudGraphInvariant

namespace PetalRecord
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

/-- Recover an actual descending path from a selected vertex to the recorded
bottleneck by following stored predecessors. Region closure ensures that every
step stays in this petal, and the recorded layer strictly decreases. -/
def recoverTail (R : PetalRecord M) (v : Fin n) (hv : R.selected v) :
    { p : DDFS.Path (predecessorGraph R.prior R.forest R.invariant) //
      p.first = v ∧ p.last = R.bottleneck ∧ ∀ w, p.Contains w → R.selected w } :=
  if he : v = R.bottleneck then
    ⟨DDFS.Path.trivial _ v, rfl, he, by
      rintro w ⟨j, hj⟩
      change v = w at hj
      exact hj ▸ hv⟩
  else
    have hpos : 0 < (R.prior.minLabel v).getD 0 :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) (DDFS.onRootTo_level_gt ((R.region v).1 hv) he)
    let u := R.invariant.firstPredecessor v hpos
    let q := R.recoverTail (R.forest.root u.val) (R.selected_edge_closed hv he u.property.2)
    have hedge : (predecessorGraph R.prior R.forest R.invariant).Edge v q.val.first :=
      q.property.1.symm ▸ u.property.2
    ⟨q.val.prepend v hedge, rfl, (q.val.prepend_last v hedge).trans q.property.2.1, by
      intro w hw
      rcases (q.val.contains_prepend_iff v hedge w).1 hw with hw | hw
      · exact hw.symm ▸ hv
      · exact q.property.2.2 w hw⟩
termination_by (R.prior.minLabel v).getD 0
decreasing_by exact R.invariant.edge_decreases u.property.2

end PetalRecord
end MaximumMatching.Search
