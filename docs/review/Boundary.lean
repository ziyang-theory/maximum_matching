import MaximumMatching
namespace IndependentBoundary
open MaximumMatching

def emptyGraph : Graph (Fin 0) where
  Adj := fun _ _ => False
  symm := fun h => h
  loopless := fun _ h => h

example : (Matching.empty emptyGraph).cardinality = 0 := by decide

example : (Matching.empty emptyGraph).IsMaximum := by
  intro N
  have h := N.cardinality_le
  exact h

example : ¬ ∃ p : AltPath (Matching.empty emptyGraph), p.Augmenting := by
  rintro ⟨p, _⟩
  exact Fin.elim0 p.first
end IndependentBoundary
