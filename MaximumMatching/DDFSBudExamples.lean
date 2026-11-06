import MaximumMatching.DDFSBud
import MaximumMatching.DDFSExecutableExamples

/-! Executable regression checks for actual DDFS-driven bud merging, including
an old descendant outside the search region and an abandoned search branch. -/
namespace MaximumMatching.DDFS.BudExamples
open Machine

def roots {n : Nat} (F : BudForest (Fin n)) : List Nat :=
  (List.finRange n).map fun v => (F.root v).val

def identityForest {n : Nat} (H : LayeredGraph (Fin n)) : BudForest (Fin n) where
  parent v := v
  rank := H.level
  decreases := by intro v hv; exact False.elim (hv rfl)

abbrev star : LayeredGraph (Fin 4) where
  Edge u v := v = 0 ∧ u ≠ 0
  level v := v.val
  decreases := by
    intro u v h
    rcases h with ⟨rfl, hu⟩
    have hupos : 0 < u.val := by
      by_cases hz : u.val = 0
      · exact False.elim (hu (Fin.ext hz))
      · omega
    exact hupos

instance : DecidableRel star.Edge := fun _ _ => inferInstanceAs (Decidable (_ = 0 ∧ _ ≠ 0))

theorem star_reaches : ReachBottom star := by
  intro v
  by_cases hv : v = 0
  · subst v
    exact ⟨Path.trivial star 0, rfl, rfl⟩
  · let p := (Path.trivial star v).snoc 0 ⟨rfl, hv⟩
    exact ⟨p, rfl, rfl⟩

-- Vertex 3 is an old descendant of root 2. It is never searched from roots
-- 1 and 2, but must move with the selected root's entire existing bud class.
def oldForest : BudForest (Fin 4) where
  parent v := if v = 3 then 2 else v
  rank v := v.val
  decreases := by
    intro v hv
    by_cases he : v = 3
    · subst v
      decide
    · exact False.elim (hv (ite_eq_right he))

/-- info: true -/
#guard_msgs in
#eval roots (executeAndContract star_reaches 2 1 oldForest).2 == [0, 0, 0, 0]

-- When only root 1 is selected, the untouched class rooted at 2 remains.
/-- info: true -/
#guard_msgs in
#eval roots (executeAndContract star_reaches 0 1 oldForest).2 == [0, 0, 2, 2]

-- The abandoned branch vertex 3 is still contracted with the full region.
/-- info: true -/
#guard_msgs in
#eval roots (executeAndContract ExecutableExamples.fixture_reaches 0 1
  (identityForest ExecutableExamples.fixture)).2 == [5, 5, 5, 5, 5, 5, 6]

-- A disjoint-path output requests no contraction.
/-- info: true -/
#guard_msgs in
#eval roots (executeAndContract ExecutableExamples.edgeless_reaches 0 1
  (identityForest ExecutableExamples.edgeless)).2 == [0, 1]

end MaximumMatching.DDFS.BudExamples
