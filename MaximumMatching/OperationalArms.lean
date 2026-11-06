import MaximumMatching.CurrentBridgeRepresentation
import MaximumMatching.MatchingPathRecoveryPredecessors

/-! Computational path data for known parity labels. Each arm ends at the
actual current bud and records the exact matching-path length. These data
are distinct from the erased existential representation used for correctness. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

/-- A computed route from a labeled vertex to its current root. -/
structure ParityArm (M : Matching G) (s : State V) (F : BudForest V)
    (v : V) (k : Nat) where
  segment : ParitySegment M
  first : segment.first = v
  last : segment.last = F.root v
  length : segment.length + (s.minLabel (F.root v)).getD 0 = k
  phase : segment.phase % 2 = (k + 1) % 2
  end_phase : (segment.phase + segment.length) % 2 =
    ((s.minLabel (F.root v)).getD 0 + 1) % 2
  interior : ∀ j : Fin (segment.length + 1), j.val < segment.length →
    F.root (segment.vertex j) = F.root v

/-- Runtime arms for every available parity label. Their proofs certify the
computed segments; neither the segment nor its vertex map is erased. -/
structure OperationalArms (M : Matching G) (s : State V) (F : BudForest V) where
  get : ∀ v parity k, parityLabel s v parity = some k → ParityArm M s F v k

namespace ParityArm

def singleton (s : State V) (F : BudForest V) (v : V) (k : Nat)
    (hroot : F.root v = v) (hmin : s.minLabel v = some k) : ParityArm M s F v k where
  segment := ParitySegment.trivial M v (k + 1)
  first := rfl
  last := hroot.symm
  length := by simp only [ParitySegment.trivial, hroot, hmin, Option.getD_some, Nat.zero_add]
  phase := rfl
  end_phase := by simp only [ParitySegment.trivial, hroot, hmin, Option.getD_some, Nat.add_zero]
  interior := by intro j hj; exact False.elim (Nat.not_lt_zero _ hj)

end ParityArm

namespace OperationalArms

/-- Initial parity labels are all minimum labels at singleton roots, so their
computed arms have length zero. -/
def initial (M : Matching G) : OperationalArms M (Search.initial M)
    (uncontractedForest (Search.initial M)) where
  get v parity k hk := by
    have hmin : (Search.initial M).minLabel v = some k := by
      unfold parityLabel at hk
      cases hm : (Search.initial M).minLabel v with
      | none => simp [hm] at hk
      | some l =>
        rw [hm] at hk
        change (if l % 2 = parity then some l else none) = some k at hk
        split at hk
        · exact hk
        · contradiction
    exact ParityArm.singleton _ _ v k
      ((uncontractedForest (Search.initial M)).root_of_fixed v rfl) hmin

end OperationalArms
end MaximumMatching.Search
