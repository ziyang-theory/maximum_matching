import MaximumMatching.Phase

/-! Sequential augmentation of a supplied finite, vertex-disjoint family.
Finding a maximal family of shortest paths remains the MV search obligation. -/
namespace MaximumMatching

structure AugmentingFamily {V : Type} {G : Graph V} (M : Matching G) where
  count : Nat
  path : Fin count → AltPath M
  augmenting : ∀ i, (path i).Augmenting
  disjoint : ∀ i j, i ≠ j → (path i).Disjoint (path j)

namespace AugmentingFamily
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

/-- Flip the first path and transport every remaining disjoint path. -/
def tailAfterFirst (f : AugmentingFamily M) (h : 0 < f.count) :
    AugmentingFamily ((f.path ⟨0, h⟩).augment (f.augmenting ⟨0, h⟩)) where
  count := f.count - 1
  path i := (f.path ⟨0, h⟩).rebase (f.augmenting ⟨0, h⟩)
    (f.path ⟨i.val + 1, by omega⟩)
    (f.disjoint ⟨0, h⟩ ⟨i.val + 1, by omega⟩ (by intro he; have := congrArg Fin.val he; simp at this))
  augmenting i := AltPath.rebase_augmenting _ _ _ (f.augmenting _) _
  disjoint := by
    intro i j hij
    change (f.path ⟨i.val + 1, by omega⟩).Disjoint (f.path ⟨j.val + 1, by omega⟩)
    apply f.disjoint
    intro he
    apply hij
    apply Fin.ext
    have hv : i.val + 1 = j.val + 1 := congrArg Fin.val he
    omega

/-- Execute all supplied flips; recursion consumes one path each time. -/
def run {M : Matching G} (f : AugmentingFamily M) : Matching G :=
  if h : f.count = 0 then M else (f.tailAfterFirst (by omega)).run
termination_by f.count
decreasing_by
  dsimp [tailAfterFirst]
  omega

end AugmentingFamily

namespace AugmentingFamily
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

/-- The exact gain is the number of input paths, without a correctness oracle. -/
theorem run_cardinality {M : Matching G} (f : AugmentingFamily M) :
    f.run.cardinality = M.cardinality + f.count := by
  rw [run]
  split
  next h => simp [h]
  next h =>
    rw [run_cardinality, AltPath.augment_cardinality]
    change M.cardinality + 1 + (f.count - 1) = M.cardinality + f.count
    omega
termination_by f.count
decreasing_by
  dsimp [tailAfterFirst]
  omega

end AugmentingFamily
end MaximumMatching
