import MaximumMatching.CurrentBucketCoverage
import MaximumMatching.CurrentBucketRootLabels

/-! At an exhausted complete search level every surviving bud root has
strictly greater tenacity than the level's processed bridge tenacity. This
follows from actual MAX completeness and the absence of MAX labels at roots. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

/-- Complete maximum labels and root exclusion force every surviving root
above any processed tenacity threshold. No path or base premise is used. -/
theorem MaxLabelsOffRoots.roots_high {s : State V} {F : BudForest V}
    (hoff : MaxLabelsOffRoots s F) {cutoff t : Nat}
    (hcomplete : MaxCompleteBelowTenacity M cutoff s) (ht : t < cutoff)
    (v : V) : levelLT (some t) (tenacity M (F.root v)) := by
  cases hten : tenacity M (F.root v) with
  | none => trivial
  | some k =>
    change t < k
    apply Classical.byContradiction
    intro hn
    have hkt : k < cutoff := by omega
    have hlabel := hcomplete (F.root v) k hten hkt
    have hnone := hoff (F.root v) (F.root_idempotent v)
    obtain ⟨p, _, hmax⟩ := finite_tenacity_maxlevel_path (F.root v) k hten
    rw [hnone, hmax] at hlabel
    contradiction

section Finite
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G} [DecidableRel G.Adj]
    {i cut : Nat}
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)

/-- Actual exhaustion restores the strict high-root part of the next
lower-blossom representation. Intermediate bottlenecks may still have current
tenacity; only the completed bucket has this stronger conclusion. -/
theorem runCurrentBucket_exhausted_roots_high (B : CurrentBucketState M i cut)
    (hrep : LowerBlossomRepresentation M cut B.state B.forest)
    (hoff : MaxLabelsOffRoots B.state B.forest)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (hcomplete : ∀ u v, Bridge M u v → MaximumMatching.edgeTenacity M u v = some (2 * i + 1) →
      (u, v) ∈ es ∨ (v, u) ∈ es)
    (B' : CurrentBucketState M i cut)
    (hexhausted : (runCurrentBucket hc htop hstageTen B es hqueued).1 = .exhausted B')
    (v : Fin n) : levelLT (some (2 * i + 1)) (tenacity M (B'.forest.root v)) := by
  have hs := runCurrentBucket_exhausted_stageInvariant hc htop hstageTen B hrep es hqueued
    hcomplete B' hexhausted
  have ho := runCurrentBucket_maxLabelsOffRoots hc htop hstageTen B es hqueued hoff
  rw [hexhausted] at ho
  exact ho.roots_high hs.maxComplete (by omega) v

end Finite
end MaximumMatching.Search
