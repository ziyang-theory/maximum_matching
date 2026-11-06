import MaximumMatching.OperationalArms
import MaximumMatching.MatchingBudStage
import MaximumMatching.SearchStage

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
