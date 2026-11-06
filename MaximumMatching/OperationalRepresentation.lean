import MaximumMatching.OperationalBridgeArms

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
