import Std

/-! Terminating bud-pointer lookup and verified path compression.

This verifies the data structure under a decreasing-rank invariant. It does not
assert that MV's petal construction establishes that invariant. -/
namespace MaximumMatching

structure BudForest (V : Type) where
  parent : V → V
  rank : V → Nat
  decreases : ∀ v, parent v ≠ v → rank (parent v) < rank v

namespace BudForest
variable {V : Type} [DecidableEq V]

def root (F : BudForest V) (v : V) : V :=
  if _h : F.parent v = v then v else F.root (F.parent v)
termination_by F.rank v
decreasing_by exact F.decreases v (by assumption)

theorem root_of_fixed (F : BudForest V) (v : V) (h : F.parent v = v) :
    F.root v = v := by
  rw [root, dite_eq_left h]

theorem root_parent (F : BudForest V) (v : V) :
    F.root (F.parent v) = F.root v := by
  by_cases h : F.parent v = v
  · rw [h]
  · symm
    rw [root, dite_eq_right h]

theorem root_fixed (F : BudForest V) (v : V) :
    F.parent (F.root v) = F.root v := by
  rw [root]
  split
  · assumption
  · exact F.root_fixed (F.parent v)
termination_by F.rank v
decreasing_by exact F.decreases v (by assumption)

theorem root_idempotent (F : BudForest V) (v : V) :
    F.root (F.root v) = F.root v :=
  F.root_of_fixed _ (F.root_fixed v)

theorem root_rank_le (F : BudForest V) (v : V) :
    F.rank (F.root v) ≤ F.rank v := by
  rw [root]
  split
  · exact Nat.le_refl _
  · exact Nat.le_trans (F.root_rank_le (F.parent v)) (Nat.le_of_lt (F.decreases v ‹_›))
termination_by F.rank v
decreasing_by exact F.decreases v (by assumption)

theorem root_rank_lt (F : BudForest V) (v : V) (h : F.root v ≠ v) :
    F.rank (F.root v) < F.rank v := by
  have hp : F.parent v ≠ v := by
    intro hp
    exact h (F.root_of_fixed v hp)
  rw [← F.root_parent]
  exact Nat.lt_of_le_of_lt (F.root_rank_le _) (F.decreases v hp)

/-- Compress one pointer after a root lookup, retaining the same ranks. -/
def compress (F : BudForest V) (x : V) : BudForest V where
  parent v := if v = x then F.root x else F.parent v
  rank := F.rank
  decreases := by
    intro v h
    by_cases hv : v = x
    · subst v
      simp only [ite_true] at h ⊢
      exact F.root_rank_lt x h
    · simp only [ite_eq_right (fun h => False.elim (hv h))] at h ⊢
      exact F.decreases v h

theorem compress_fixed (F : BudForest V) (x v : V) (h : F.parent v = v) :
    (F.compress x).parent v = v := by
  by_cases hv : v = x
  · subst v
    simp [compress, F.root_of_fixed x h]
  · simp [compress, hv, h]

theorem compress_root (F : BudForest V) (x v : V) :
    (F.compress x).root v = F.root v := by
  by_cases hv : v = x
  · subst v
    rw [← (F.compress x).root_parent]
    have hp : (F.compress x).parent x = F.root x := by simp [compress]
    rw [hp]
    exact (F.compress x).root_of_fixed _ (F.compress_fixed x _ (F.root_fixed x))
  · by_cases hp : F.parent v = v
    · rw [(F.compress x).root_of_fixed v (F.compress_fixed x v hp), F.root_of_fixed v hp]
    · rw [← (F.compress x).root_parent]
      have he : (F.compress x).parent v = F.parent v := by simp [compress, hv]
      rw [he, F.compress_root x (F.parent v), F.root_parent]
termination_by F.rank v
decreasing_by exact F.decreases v (by assumption)

/-- Compress a finite sequence of inspected vertices. -/
def compressMany (F : BudForest V) : List V → BudForest V
  | [] => F
  | x :: xs => (F.compress x).compressMany xs

theorem compressMany_root (F : BudForest V) (xs : List V) (v : V) :
    (F.compressMany xs).root v = F.root v := by
  induction xs generalizing F with
  | nil => rfl
  | cons x xs ih =>
    change ((F.compress x).compressMany xs).root v = F.root v
    rw [ih, F.compress_root]

end BudForest
end MaximumMatching
