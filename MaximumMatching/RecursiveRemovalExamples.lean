import MaximumMatching.RecursiveRemoval

/-! Executed recursive-removal cascade and independent surviving branch. -/
namespace MaximumMatching.DDFS.RecursiveRemoval.Examples

def graph : LayeredGraph (Fin 5) where
  Edge u v := (u = 3 ∧ v = 2) ∨ (u = 2 ∧ v = 0) ∨ (u = 4 ∧ v = 1)
  level v := if v = 3 then 2 else if v = 2 ∨ v = 4 then 1 else 0
  decreases := by
    intro u v he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

instance : DecidableRel graph.Edge := fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- Removing bottom 0 recursively removes 2 and then 3, while the separate
4-to-1 branch remains available. -/
example : (remove graph (List.finRange 5) [0]).map Fin.val = [1, 4] := by
  simp only [remove]
  rw [prune]
  change (prune graph [1, 3, 4]).map Fin.val = [1, 4]
  rw [prune]
  change (prune graph [1, 4]).map Fin.val = [1, 4]
  rw [prune]
  decide

/-- With no explicit deletion the two full bottom-reaching branches survive. -/
example : prune graph (List.finRange 5) = List.finRange 5 := by
  rw [prune]
  decide

example : ReachBottom (restricted graph (remove graph (List.finRange 5) [0])) :=
  remove_reachBottom graph _ _

end MaximumMatching.DDFS.RecursiveRemoval.Examples
