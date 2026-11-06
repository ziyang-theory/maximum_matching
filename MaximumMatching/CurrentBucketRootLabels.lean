import MaximumMatching.CurrentBucketProgress
import MaximumMatching.MatchingBudStage

/-! Maximum labels belong to absorbed roots. This operational invariant is
initialized by the empty MAX state and is preserved by actual MIN, MAX, and
petal contraction. It does not assume canonical blossom/base correspondence. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

/-- Current bud roots have not received a MAX assignment. -/
def MaxLabelsOffRoots (s : State V) (F : BudForest V) : Prop :=
  ∀ v, F.root v = v → s.maxLabel v = none

theorem initial_maxLabelsOffRoots (M : Matching G) (F : BudForest V) :
    MaxLabelsOffRoots (initial M) F := by
  intro v _
  rfl

section Finite
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

namespace PetalRecord

/-- Every root surviving an actual petal was already a root beforehand. -/
theorem after_root_was_root (R : PetalRecord M) (v : Fin n)
    (hv : R.after.root v = v) : R.forest.root v = v := by
  have hr := R.after_root v
  rw [hv] at hr
  split at hr
  · have hb := R.forest.root_of_fixed R.bottleneck
      (R.selected_fixed R.bottleneck R.trees.bottleneck_mem)
    simpa only [hr] using hb
  · exact hr.symm

/-- MAX labels only the newly absorbed roots; every surviving root retains its
previously unknown maximum label, including the selected bottleneck itself. -/
theorem maxEvent_maxLabelsOffRoots [DecidableRel G.Adj] (R : PetalRecord M) (i : Nat)
    (h : MaxLabelsOffRoots R.prior R.forest) :
    MaxLabelsOffRoots (R.maxEvent i).1 R.after := by
  intro v hv
  have hold := R.after_root_was_root v hv
  have hnot : v ∉ R.newRoots := by
    intro hnew
    obtain ⟨hsel, hne⟩ := (R.mem_newRoots v).1 hnew
    have hafter := R.after_selected v (by simpa only [selectedFiber, hold] using hsel)
    exact hne (hv.symm.trans hafter)
  exact (R.maxEvent_outside i v hnot).trans (h v hold)

end PetalRecord

variable [DecidableRel G.Adj]

theorem scanLevelWithBuds_maxLabelsOffRoots (M : Matching G) (i : Nat)
    (s : State (Fin n)) (F : BudForest (Fin n)) (h : BudGraphInvariant M i s F)
    (hoff : MaxLabelsOffRoots s F) :
    MaxLabelsOffRoots (scanLevelWithBuds M i s F h).1 (scanLevelWithBuds M i s F h).2 := by
  intro v hv
  rw [scanLevelWithBuds_root] at hv
  exact (scanCandidates_maxLabel (allCandidates n) s i v).trans (hoff v hv)

namespace CurrentBucketState

theorem afterPetal_maxLabelsOffRoots {i cut : Nat} (R : PetalRecord M)
    (hP : Nonempty (CurrentBridgeRepresentation M cut R.invariant))
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hten : R.tenacity = cut + 2) (hstageTen : cut + 2 = 2 * i + 1)
    (hcap : R.cap = i + 1) (hstage : StageState M (i + 1) (2 * i + 1) R.prior)
    (hoff : MaxLabelsOffRoots R.prior R.forest) :
    MaxLabelsOffRoots (afterPetal R hP hc htop hten hstageTen hcap hstage).state
      (afterPetal R hP hc htop hten hstageTen hcap hstage).forest :=
  R.maxEvent_maxLabelsOffRoots i hoff

end CurrentBucketState

/-- The complete bucket loop preserves the absence of MAX labels at its final
roots, whether it exhausts the list or stops at a disjoint-path witness. -/
theorem runCurrentBucket_maxLabelsOffRoots {i cut : Nat}
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) (B : CurrentBucketState M i cut)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (hoff : MaxLabelsOffRoots B.state B.forest) :
    MaxLabelsOffRoots (runCurrentBucket hc htop hstageTen B es hqueued).1.state.state
      (runCurrentBucket hc htop hstageTen B es hqueued).1.state.forest := by
  induction es generalizing B with
  | nil => simpa only [runCurrentBucket, CurrentBucketOutcome.state] using hoff
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    rw [runCurrentBucket]
    split
    · exact ih B _ hoff
    · split
      · exact hoff
      · apply ih
        exact PetalRecord.maxEvent_maxLabelsOffRoots _ i hoff

end Finite
end MaximumMatching.Search
