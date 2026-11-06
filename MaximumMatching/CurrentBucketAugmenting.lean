import MaximumMatching.CurrentBucketCoverage
import MaximumMatching.CurrentBucketRootLabels
import MaximumMatching.Optimality

/-! Exhaustion excludes augmenting paths at the current threshold. A shortest
augmenting path gives its free terminal vertex the current tenacity; coverage
would label that vertex, although free vertices remain unlabeled bud roots. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

namespace AltPath

/-- A shortest augmenting path has terminal tenacity and maximum level equal
to its length: the free endpoint has even level zero and this shortest odd path. -/
theorem shortest_augmenting_last_levels (p : AltPath M) (hp : p.Augmenting)
    (hshort : AtMostShortestAugmenting M p.length) :
    tenacity M p.last = some p.length ∧ maxlevel M p.last = some p.length := by
  have he := (evenlevel_zero_iff_free M p.last).2 hp.2
  have ho : oddlevel M p.last = some p.length := by
    apply (level_eq_some_iff M 1 p.last p.length).2
    refine ⟨⟨p, rfl, rfl, hp.1⟩, ?_⟩
    rintro l ⟨q, hql, hlen, hpar⟩
    have hq : q.Augmenting := ⟨by omega, by rw [hql]; exact hp.2⟩
    simpa only [hlen] using hshort q hq
  simp only [tenacity, maxlevel, he, ho, levelAdd, levelMax, Nat.zero_add, Nat.zero_max,
    and_self]

end AltPath

namespace Search
variable [DecidableEq V]

/-- A free vertex has stored minimum level and forest rank zero, so it cannot
have a parent of strictly smaller rank and is its own bud root. -/
theorem BudGraphInvariant.free_root {cap : Nat} {s : State V} {F : BudForest V}
    (h : BudGraphInvariant M cap s F) (v : V) (hf : M.Free v) : F.root v = v := by
  have hl := h.minInvariant.2.1 v 0 ((minlevel_zero_iff_free v).2 hf) (Nat.zero_le cap)
  have hr : F.rank v = 0 := by simpa only [hl, Option.getD_some] using h.rankLabel v
  by_cases he : F.root v = v
  · exact he
  · have hlt := F.root_rank_lt v he
    rw [hr] at hlt
    omega

section Finite
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G} [DecidableRel G.Adj]
    {i cut : Nat} (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)

/-- Exhausting a complete current bucket rules out every augmenting path of
its current length. Initial roots being unlabeled is an operational invariant,
proved for initial states and preserved by MIN and earlier bucket processing. -/
theorem runCurrentBucket_exhausted_no_current_augmenting (B : CurrentBucketState M i cut)
    (hrep : LowerBlossomRepresentation M cut B.state B.forest)
    (hoff : MaxLabelsOffRoots B.state B.forest)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (hcomplete : ∀ u v, Bridge M u v → MaximumMatching.edgeTenacity M u v = some (2 * i + 1) →
      (u, v) ∈ es ∨ (v, u) ∈ es)
    (B' : CurrentBucketState M i cut)
    (hexhausted : (runCurrentBucket hc htop hstageTen B es hqueued).1 = .exhausted B')
    (p : AltPath M) (hp : p.Augmenting) : p.length ≠ 2 * i + 1 := by
  intro hlen
  have hshort : AtMostShortestAugmenting M p.length := by
    rw [hlen, ← hstageTen]
    exact htop
  obtain ⟨hten, hmax⟩ := p.shortest_augmenting_last_levels hp hshort
  have hlabel := runCurrentBucket_exhausted_maxComplete hc htop hstageTen B hrep es hqueued hcomplete
    B' hexhausted p.last (by rw [← hlen]; exact hten)
  have hoff' := runCurrentBucket_maxLabelsOffRoots hc htop hstageTen B es hqueued hoff
  rw [hexhausted] at hoff'
  have hnone := hoff' p.last (B'.bud.free_root p.last hp.2)
  change B'.state.maxLabel p.last = none at hnone
  rw [hnone, hmax] at hlabel
  contradiction

/-- Exhaustion raises the lower bound to the next odd search length. This
proves that proceeding to the next MIN level preserves its search threshold. -/
theorem runCurrentBucket_exhausted_next_lower_bound (B : CurrentBucketState M i cut)
    (hrep : LowerBlossomRepresentation M cut B.state B.forest)
    (hoff : MaxLabelsOffRoots B.state B.forest)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (hcomplete : ∀ u v, Bridge M u v → MaximumMatching.edgeTenacity M u v = some (2 * i + 1) →
      (u, v) ∈ es ∨ (v, u) ∈ es)
    (B' : CurrentBucketState M i cut)
    (hexhausted : (runCurrentBucket hc htop hstageTen B es hqueued).1 = .exhausted B') :
    AtMostShortestAugmenting M (2 * (i + 1) + 1) := by
  intro p hp
  have hne := runCurrentBucket_exhausted_no_current_augmenting hc htop hstageTen B hrep hoff
    es hqueued hcomplete B' hexhausted p hp
  have hle := htop p hp
  have hodd := hp.1
  omega


/-- A complete exhausted bucket beyond the finite path-length bound certifies
that the current matching is maximum. -/
theorem runCurrentBucket_exhausted_isMaximum (B : CurrentBucketState M i cut)
    (hrep : LowerBlossomRepresentation M cut B.state B.forest)
    (hoff : MaxLabelsOffRoots B.state B.forest)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (hcomplete : ∀ u v, Bridge M u v → MaximumMatching.edgeTenacity M u v = some (2 * i + 1) →
      (u, v) ∈ es ∨ (v, u) ∈ es)
    (B' : CurrentBucketState M i cut)
    (hexhausted : (runCurrentBucket hc htop hstageTen B es hqueued).1 = .exhausted B')
    (hn : n ≤ 2 * (i + 1) + 1) : M.IsMaximum := by
  apply M.noAugmentingPath_isMaximum
  intro p hp
  have hbound := runCurrentBucket_exhausted_next_lower_bound hc htop hstageTen B hrep hoff
    es hqueued hcomplete B' hexhausted p hp
  have hlen := p.length_lt_vertices
  omega

end Finite
end Search
end MaximumMatching
