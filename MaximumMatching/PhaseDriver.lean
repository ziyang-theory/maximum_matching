import MaximumMatching.PhaseProgress
import MaximumMatching.Optimality

/-! The executable outer augmentation loop, separated from the phase search.

Every supplied phase returns actual disjoint augmenting paths and `run` flips
them. Termination and cardinality gain require no completeness premise. Maximum
cardinality additionally requires proving that this particular phase search
returns an empty family only when there is no augmenting path. The concrete
deletion-aware MIN/MAX/DDFS search instantiates this interface in `BlockingPhase`.
-/
namespace MaximumMatching
namespace PhaseDriver

variable {n : Nat} {G : Graph (Fin n)}

/-- The data computed by a phase. No shortestness or completeness is asserted. -/
abbrev Search (G : Graph (Fin n)) := (M : Matching G) → AugmentingFamily M

structure Result (G : Graph (Fin n)) where
  matching : Matching G
  positivePhases : Nat
  augmentations : Nat

/-- Run genuine flips until the supplied search returns no paths. The natural
cardinality deficit proves termination, without an arbitrary fuel limit. -/
def run (search : Search G) (M : Matching G) : Result G :=
  let f := search M
  if _h : f.count = 0 then
    ⟨M, 0, 0⟩
  else
    let rest := run search f.run
    ⟨rest.matching, rest.positivePhases + 1, rest.augmentations + f.count⟩
termination_by n / 2 - M.cardinality
decreasing_by
  change n / 2 - (search M).run.cardinality < n / 2 - M.cardinality
  change (search M).count ≠ 0 at _h
  have hgain := (search M).run_cardinality
  have hbound := (search M).run.cardinality_le
  omega

/-- Exact cumulative cardinality gain, for every search implementation. -/
theorem run_cardinality (search : Search G) (M : Matching G) :
    (run search M).matching.cardinality = M.cardinality + (run search M).augmentations := by
  rw [run]
  split
  · simp
  · dsimp only
    have ih := run_cardinality search (search M).run
    have hg := (search M).run_cardinality
    omega
termination_by n / 2 - M.cardinality
decreasing_by
  have hg := (search M).run_cardinality
  have hb := (search M).run.cardinality_le
  omega

/-- Independent specification of the search's stopping condition. This is an
obligation for the actual MV phase, not a field assumed of its implementation. -/
def Complete (search : Search G) : Prop :=
  ∀ M, (search M).count = 0 → M.NoAugmentingPath

/-- Every positive search result is a maximal family of shortest augmenting
paths. A concrete blocking-phase implementation proves this specification. -/
def ShortestBlocking (search : Search G) : Prop :=
  ∀ M, (search M).count ≠ 0 → ∃ l, (search M).MaximalShortest l

/-- Conditional assembly theorem: any complete augmenting-family search makes
this executable outer loop return a maximum matching. It does not certify MV
until its concrete phase implementation satisfies `Complete`, as proved in
`BlockingPhase`. -/
theorem run_isMaximum (search : Search G) (hsearch : Complete search) (M : Matching G) :
    (run search M).matching.IsMaximum := by
  rw [run]
  split
  next hz => exact M.noAugmentingPath_isMaximum (hsearch M hz)
  next hn =>
    exact run_isMaximum search hsearch (search M).run
termination_by n / 2 - M.cardinality
decreasing_by
  have hg := (search M).run_cardinality
  have hb := (search M).run.cardinality_le
  omega

end PhaseDriver
end MaximumMatching
