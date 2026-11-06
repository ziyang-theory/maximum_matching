import MaximumMatching.CurrentBucket

/-! Monotone bud classes and completed-trigger accounting for the actual
current-bucket loop. Exhaustion here means the supplied bucket was processed;
semantic support coverage is a separate remaining implication. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

namespace PetalRecord

theorem starts_selected (R : PetalRecord M) :
    R.selected (R.forest.root R.left) ∧ R.selected (R.forest.root R.right) := by
  obtain ⟨p, hpf, hpb, _⟩ := R.trees.red.path R.bottleneck (Or.inl rfl)
  obtain ⟨q, hqf, hqb, _⟩ := R.trees.green.path R.bottleneck (Or.inl rfl)
  exact ⟨(R.region _).2 ⟨p, Or.inl hpf, hpb, ⟨0, by omega⟩, hpf⟩,
    (R.region _).2 ⟨q, Or.inr hqf, hqb, ⟨0, by omega⟩, hqf⟩⟩

theorem after_trigger_equal (R : PetalRecord M) :
    R.after.root R.left = R.after.root R.right :=
  (R.after_selected R.left R.starts_selected.1).trans (R.after_selected R.right R.starts_selected.2).symm

end PetalRecord

namespace CurrentBucketOutcome

def state {i cut : Nat} : CurrentBucketOutcome M i cut → CurrentBucketState M i cut
  | .exhausted B => B
  | .found B _ => B

end CurrentBucketOutcome

section
variable [DecidableRel G.Adj] {i cut : Nat}
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)

/-- Any two vertices already in one bud class remain together after the
actual bucket loop, including if a disjoint witness stops the loop early. -/
theorem runCurrentBucket_root_congr (B : CurrentBucketState M i cut)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (u v : Fin n) (heq : B.forest.root u = B.forest.root v) :
    (runCurrentBucket hc htop hstageTen B es hqueued).1.state.forest.root u =
      (runCurrentBucket hc htop hstageTen B es hqueued).1.state.forest.root v := by
  induction es generalizing B with
  | nil => simpa only [runCurrentBucket, CurrentBucketOutcome.state] using heq
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    rw [runCurrentBucket]
    split
    · exact ih B _ heq
    · split
      · exact heq
      · apply ih
        exact B.forest.mergeManyInto_root_congr _ _ u v heq

end
end MaximumMatching.Search
