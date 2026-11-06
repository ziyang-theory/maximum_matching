import MaximumMatching.CurrentBucket
import MaximumMatching.GeneralBridgeStructure
import MaximumMatching.MatchingGraphExpansion
import MaximumMatching.MatchingSearchGraph
import MaximumMatching.Optimality
import MaximumMatching.PetalBase
import MaximumMatching.PetalPathTransport
import MaximumMatching.SupportPaths

section CurrentBucketCoverage

/-! Converse support coverage through the actual current-bucket loop. A
supported vertex is either assigned its maximum level, or retains disjoint
predecessor-graph arms that prevent its trigger's buds from coinciding. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

/-- Actual disjoint predecessor-graph arms for a bridge's supported vertex.
The first ends at the supported vertex; the other reaches layer zero. -/
def SupportArms {cap : Nat} {s : State V} {F : BudForest V}
    (h : BudGraphInvariant M cap s F) (u v w : V) : Prop :=
  ∃ p q : DDFS.Path (predecessorGraph s F h), p.last = w ∧
    (predecessorGraph s F h).level q.last = 0 ∧ p.Disjoint q ∧
    ((p.first = F.root u ∧ q.first = F.root v) ∨
      (p.first = F.root v ∧ q.first = F.root u))

namespace SupportArms
variable {cap cap' : Nat} {s s' : State V} {F : BudForest V}
    {h : BudGraphInvariant M cap s F} {u v w : V}

theorem symm (ha : SupportArms h u v w) : SupportArms h v u w := by
  obtain ⟨p, q, hp, hq, hd, hs⟩ := ha
  exact ⟨p, q, hp, hq, hd, hs.elim Or.inr Or.inl⟩

theorem roots_ne (ha : SupportArms h u v w) : F.root u ≠ F.root v := by
  obtain ⟨p, q, _, _, hd, hs⟩ := ha
  intro he
  have hf : p.first = q.first := hs.elim
    (fun hh => hh.1.trans (he.trans hh.2.symm))
    (fun hh => hh.1.trans (he.symm.trans hh.2.symm))
  exact hd p.first p.contains_first (hf ▸ q.contains_first)

theorem of_same_min_data (ha : SupportArms h u v w)
    (h' : BudGraphInvariant M cap' s' F)
    (hmin : s'.minLabel = s.minLabel) (hpred : s'.predecessors = s.predecessors) :
    SupportArms h' u v w := by
  unfold SupportArms at *
  rw [predecessorGraph_eq_of_fields h h' hmin hpred]
  exact ha

end SupportArms

section Finite
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

namespace PetalRecord

theorem after_root_old_root (R : PetalRecord M) (v : Fin n) :
    R.after.root (R.forest.root v) = R.after.root v :=
  R.forest.mergeManyInto_root_congr _ _ _ _ (R.forest.root_idempotent v)

/-- If the support target survives as a root, its actual disjoint arms
survive the recorded contraction. -/
theorem transport_support_arms (R : PetalRecord M) (u v w : Fin n)
    (ha : SupportArms R.invariant u v w)
    (hw : w = R.bottleneck ∨ ¬ R.selected w) :
    SupportArms R.after_invariant u v w := by
  obtain ⟨p, q, hpw, hqb, hd, hs⟩ := ha
  have hpf : R.forest.parent p.first = p.first := by
    rcases hs with hh | hh
    · rw [hh.1]; exact R.forest.root_fixed u
    · rw [hh.1]; exact R.forest.root_fixed v
  have hqf : R.forest.parent q.first = q.first := by
    rcases hs with hh | hh
    · rw [hh.2]; exact R.forest.root_fixed v
    · rw [hh.2]; exact R.forest.root_fixed u
  have hpfix : ∀ x, p.Contains x → R.forest.root x = x := by
    rintro x ⟨j, rfl⟩
    exact R.forest.root_of_fixed _ (R.invariant.path_fixed p hpf j)
  have hqfix : ∀ x, q.Contains x → R.forest.root x = x := by
    rintro x ⟨j, rfl⟩
    exact R.forest.root_of_fixed _ (R.invariant.path_fixed q hqf j)
  obtain ⟨a, b, haf, hal, hbf, hbl, hab, _, _⟩ :=
    R.transport_disjoint_paths_of_surviving_target p q hpfix hqfix hd (by rwa [hpw]) hqb
  refine ⟨a, b, hal.trans hpw, ?_, hab, ?_⟩
  · change (R.prior.minLabel b.last).getD 0 = 0
    rw [hbl]
    exact hqb
  · rcases hs with hh | hh
    · exact Or.inl ⟨haf.trans ((congrArg R.after.root hh.1).trans (R.after_root_old_root u)),
        hbf.trans ((congrArg R.after.root hh.2).trans (R.after_root_old_root v))⟩
    · exact Or.inr ⟨haf.trans ((congrArg R.after.root hh.1).trans (R.after_root_old_root v)),
        hbf.trans ((congrArg R.after.root hh.2).trans (R.after_root_old_root u))⟩

section
variable [DecidableRel G.Adj]

/-- A petal either assigns the supported target or preserves its actual arms
through both contraction and the unchanged MIN data of the MAX event. -/
theorem maxEvent_support_progress (R : PetalRecord M) {cut : Nat}
    (P : CurrentBridgeRepresentation M cut R.invariant) (i : Nat)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hten : R.tenacity = cut + 2) (hstageTen : cut + 2 = 2 * i + 1)
    (hcap : R.cap = i + 1) (hstage : StageState M (i + 1) (2 * i + 1) R.prior)
    (hnew : BudGraphInvariant M (i + 1) (R.maxEvent i).1 R.after)
    (u v w : Fin n) (k : Nat) (hmax : maxlevel M w = some k)
    (ha : SupportArms R.invariant u v w) :
    (R.maxEvent i).1.maxLabel w = some k ∨ SupportArms hnew u v w := by
  classical
  by_cases hw : w ∈ R.newRoots
  · exact Or.inl (((R.maxEvent_correct_of_current P i _ hc htop hten hstageTen hcap hstage).2.2.1 w hw).trans hmax)
  · have hsurvive : w = R.bottleneck ∨ ¬ R.selected w := by
      by_cases he : w = R.bottleneck
      · exact Or.inl he
      · exact Or.inr (fun hs => hw ((R.mem_newRoots w).2 ⟨hs, he⟩))
    exact Or.inr ((R.transport_support_arms u v w ha hsurvive).of_same_min_data hnew
      (funext (R.maxEvent_minLabel i)) (maxProcessVertices_predecessors M i R.newRoots R.prior))

end
end PetalRecord

section
variable [DecidableRel G.Adj] {i cut : Nat}
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)

/-- Every initially witnessed support target is either assigned or keeps
actual disjoint arms throughout all processed petals, including early stops. -/
theorem runCurrentBucket_support_progress (B : CurrentBucketState M i cut)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (u v w : Fin n) (k : Nat) (hmax : maxlevel M w = some k)
    (ha : SupportArms B.bud u v w) :
    (runCurrentBucket hc htop hstageTen B es hqueued).1.state.state.maxLabel w = some k ∨
      SupportArms (runCurrentBucket hc htop hstageTen B es hqueued).1.state.bud u v w := by
  induction es generalizing B with
  | nil =>
    simp only [runCurrentBucket, CurrentBucketOutcome.state]
    exact Or.inr ha
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    rw [runCurrentBucket]
    split
    · exact ih B _ ha
    · split
      · exact Or.inr ha
      · rename_i hsame bneck S trees highest region hout
        let R : PetalRecord M := {
          cap := i + 1, prior := B.state, forest := B.forest, invariant := B.bud,
          queueSound := B.stage.classification.2.2, tenacity := 2 * i + 1,
          left := a, right := b, queued := hqueued (a, b) List.mem_cons_self,
          known := B.stage.current_bridge_known a b
            (B.stage.classification.2.2 _ a b (hqueued (a,b) List.mem_cons_self)).1
            (B.stage.classification.2.2 _ a b (hqueued (a,b) List.mem_cons_self)).2,
          different := hsame, bottleneck := bneck, selected := S, trees := trees,
          highest := highest, region := region, computed := hout }
        let next := CurrentBucketState.afterPetal R B.represented hc htop
          hstageTen.symm hstageTen rfl B.stage
        have hq : ∀ e, e ∈ es → e ∈ next.state.bucket (2 * i + 1) := by
          intro e he
          exact R.maxEvent_bucket_mono i e.1 e.2 _
            (hqueued e (List.mem_cons_of_mem (a, b) he))
        change (runCurrentBucket hc htop hstageTen next es hq).1.state.state.maxLabel w = some k ∨
          SupportArms (runCurrentBucket hc htop hstageTen next es hq).1.state.bud u v w
        obtain ⟨P⟩ := B.represented
        rcases R.maxEvent_support_progress P i hc htop hstageTen.symm hstageTen rfl
            B.stage next.bud u v w k hmax ha with hknown | hremain
        · exact Or.inl (runCurrentBucket_preserves_known_maxLabel hc htop hstageTen next es hq w k hknown)
        · exact ih next hq hremain

/-- Exhaustion of a supplied trigger forces every target witnessed by its
initial graph arms to have received the correct maximum label. -/
theorem runCurrentBucket_exhausted_support_arms (B : CurrentBucketState M i cut)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (B' : CurrentBucketState M i cut)
    (hexhausted : (runCurrentBucket hc htop hstageTen B es hqueued).1 = .exhausted B')
    (u v w : Fin n) (hmem : (u, v) ∈ es) (k : Nat) (hmax : maxlevel M w = some k)
    (ha : SupportArms B.bud u v w) : B'.state.maxLabel w = maxlevel M w := by
  have hp := runCurrentBucket_support_progress hc htop hstageTen B es hqueued u v w k hmax ha
  rw [hexhausted] at hp
  rcases hp with hknown | hremain
  · exact hknown.trans hmax.symm
  · exact False.elim (hremain.roots_ne
      (runCurrentBucket_exhausted_trigger_equal hc htop hstageTen B es hqueued B' hexhausted u v hmem))


/-- A complete supplied current bucket discovers every current-tenacity
maximum level. Only the initial lower-blossom representation is required;
its converse support witnesses are transported through all actual petals. -/
theorem runCurrentBucket_exhausted_maxComplete (B : CurrentBucketState M i cut)
    (hrep : LowerBlossomRepresentation M cut B.state B.forest)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (hcomplete : ∀ u v, Bridge M u v → MaximumMatching.edgeTenacity M u v = some (2 * i + 1) →
      (u, v) ∈ es ∨ (v, u) ∈ es)
    (B' : CurrentBucketState M i cut)
    (hexhausted : (runCurrentBucket hc htop hstageTen B es hqueued).1 = .exhausted B')
    (w : Fin n) (hwt : tenacity M w = some (2 * i + 1)) :
    B'.state.maxLabel w = maxlevel M w := by
  have ht : AtMostShortestAugmenting M (2 * i + 1) := hstageTen ▸ htop
  obtain ⟨u, v, he, hs⟩ := vertex_in_bridge_support w (2 * i + 1) ht hwt
  obtain ⟨p, _, hmax⟩ := finite_tenacity_maxlevel_path w (2 * i + 1) hwt
  have hk := B.stage.current_bridge_known u v hs.1 he
  obtain ⟨hu, hv⟩ := edgeTenacity_has_minLabels B.state u v (2 * i + 1) hk
  have ha : SupportArms B.bud u v w := B.bud.support_graph_arms hc hrep
    (by omega) u v w (by rw [hstageTen]; exact he) hu hv hs
  rcases hcomplete u v hs.1 he with hmem | hmem
  · exact runCurrentBucket_exhausted_support_arms hc htop hstageTen B es hqueued B' hexhausted
      u v w hmem p.length hmax ha
  · exact runCurrentBucket_exhausted_support_arms hc htop hstageTen B es hqueued B' hexhausted
      v u w hmem p.length hmax ha.symm

/-- Exhausting a complete bucket discharges the prior-MAX completeness
requirement for the next MIN stage. -/
theorem runCurrentBucket_exhausted_stageInvariant (B : CurrentBucketState M i cut)
    (hrep : LowerBlossomRepresentation M cut B.state B.forest)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (hcomplete : ∀ u v, Bridge M u v → MaximumMatching.edgeTenacity M u v = some (2 * i + 1) →
      (u, v) ∈ es ∨ (v, u) ∈ es)
    (B' : CurrentBucketState M i cut)
    (hexhausted : (runCurrentBucket hc htop hstageTen B es hqueued).1 = .exhausted B') :
    StageInvariant M (i + 1) B'.state := by
  refine { B'.stage with maxComplete := ?_ }
  intro w t hwt hlt
  have hodd := tenacity_odd M w t hwt
  by_cases he : t = 2 * i + 1
  · exact runCurrentBucket_exhausted_maxComplete hc htop hstageTen B hrep es hqueued hcomplete
      B' hexhausted w (he ▸ hwt)
  · exact B'.stage.maxComplete w t hwt (by omega)

end
end Finite
end MaximumMatching.Search

end CurrentBucketCoverage

section CurrentBucketEndRoots

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

end CurrentBucketEndRoots

section CurrentBucketAugmenting

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

end CurrentBucketAugmenting

section CurrentBucketBlossoms

/-! Actual current-bucket exhaustion restores the lower-blossom
representation at the next cutoff. Canonical classes are preserved through
all temporary petals; complete MAX discovery makes their final roots high. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G} [DecidableRel G.Adj]
    {i cut : Nat}
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)

/-- Every recorded contraction preserves canonical classes and the tenacity
bound on absorbed vertices. The strict augmentation bound is semantic and is
later derived from actual bucket exhaustion. -/
theorem runCurrentBucket_blossomClasses (B : CurrentBucketState M i cut)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut + 2 < p.length)
    (hlow : NonrootLow M (cut + 2) B.forest)
    (hclasses : BudBlossomClasses M (cut + 2) B.forest) :
    NonrootLow M (cut + 2) (runCurrentBucket hc htop hstageTen B es hqueued).1.state.forest ∧
      BudBlossomClasses M (cut + 2) (runCurrentBucket hc htop hstageTen B es hqueued).1.state.forest := by
  induction es generalizing B with
  | nil => simpa only [runCurrentBucket, CurrentBucketOutcome.state] using And.intro hlow hclasses
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    rw [runCurrentBucket]
    split
    · exact ih B _ hlow hclasses
    · split
      · exact ⟨hlow, hclasses⟩
      · rename_i hsame bneck S trees highest region hout
        let R : PetalRecord M := {
          cap := i + 1, prior := B.state, forest := B.forest, invariant := B.bud,
          queueSound := B.stage.classification.2.2, tenacity := 2 * i + 1,
          left := a, right := b, queued := hqueued (a, b) List.mem_cons_self,
          known := B.stage.current_bridge_known a b
            (B.stage.classification.2.2 _ a b (hqueued (a,b) List.mem_cons_self)).1
            (B.stage.classification.2.2 _ a b (hqueued (a,b) List.mem_cons_self)).2,
          different := hsame, bottleneck := bneck, selected := S, trees := trees,
          highest := highest, region := region, computed := hout }
        obtain ⟨P⟩ := B.represented
        exact ih _ _ (R.after_nonrootLow P hc htop hstageTen.symm hlow)
          (R.after_blossomClasses P hc hnoaug hstageTen.symm hlow hclasses)

/-- A complete exhausted bucket establishes the exact semantic blossom/base
representation for the next search level. All support completeness and the
strict augmentation bound are derived from the actual loop, not assumed. -/
theorem runCurrentBucket_exhausted_lower_representation (B : CurrentBucketState M i cut)
    (hrep : LowerBlossomRepresentation M cut B.state B.forest)
    (hoff : MaxLabelsOffRoots B.state B.forest)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (hcomplete : ∀ u v, Bridge M u v → MaximumMatching.edgeTenacity M u v = some (2 * i + 1) →
      (u, v) ∈ es ∨ (v, u) ∈ es)
    (B' : CurrentBucketState M i cut)
    (hexhausted : (runCurrentBucket hc htop hstageTen B es hqueued).1 = .exhausted B') :
    LowerBlossomRepresentation M (2 * i + 1) B'.state B'.forest := by
  have hnext := runCurrentBucket_exhausted_next_lower_bound hc htop hstageTen B hrep hoff
    es hqueued hcomplete B' hexhausted
  have hnoaug : ∀ p : AltPath M, p.Augmenting → cut + 2 < p.length := by
    intro p hp
    have hh := hnext p hp
    omega
  have hclasses := (runCurrentBucket_blossomClasses hc htop hstageTen B es hqueued hnoaug
    (nonrootLow_of_lower B.bud hrep) (budBlossomClasses_of_lower B.bud hc hrep)).2
  rw [hexhausted] at hclasses
  have hclasses' : BudBlossomClasses M (2 * i + 1) B'.forest := by
    simpa only [CurrentBucketOutcome.state, hstageTen] using hclasses
  exact hclasses'.lower_representation (fun v _ _ =>
    runCurrentBucket_exhausted_roots_high hc htop hstageTen B hrep hoff es hqueued hcomplete B' hexhausted v)

/-- At the processed tenacity the final bud is the vertex's canonical base,
not merely a representative of its recursive blossom. -/
theorem runCurrentBucket_exhausted_base (B : CurrentBucketState M i cut)
    (hrep : LowerBlossomRepresentation M cut B.state B.forest)
    (hoff : MaxLabelsOffRoots B.state B.forest)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (hcomplete : ∀ u v, Bridge M u v → MaximumMatching.edgeTenacity M u v = some (2 * i + 1) →
      (u, v) ∈ es ∨ (v, u) ∈ es)
    (B' : CurrentBucketState M i cut)
    (hexhausted : (runCurrentBucket hc htop hstageTen B es hqueued).1 = .exhausted B')
    (v : Fin n) (hten : tenacity M v = some (2 * i + 1)) :
    IsBase M v (B'.forest.root v) := by
  have hr := runCurrentBucket_exhausted_lower_representation hc htop hstageTen B hrep hoff
    es hqueued hcomplete B' hexhausted
  obtain ⟨e, o, he, ho, _, _, hsum⟩ := finite_levels_of_tenacity v (2 * i + 1) hten
  have hmin : minlevel M v = some (min e o) := by
    simp only [minlevel, he, ho, levelMin]
  have hv := B'.stage.min.2.1 v (min e o) hmin (by omega)
  obtain ⟨hhigh, hmem⟩ := hr v (min e o) hv
  rcases hmem with hroot | hbl
  · rw [← hroot, hten] at hhigh
    change 2 * i + 1 < 2 * i + 1 at hhigh
    omega
  · rw [← hstageTen] at hbl
    rcases hbl with hbase | ⟨w, _, _, hlow⟩
    · exact hbase.2
    · obtain ⟨a, ha, hac⟩ := blossom_tenacity_bound cut w v hlow
      have hh := Option.some.inj (ha.symm.trans hten)
      omega

/-- Functional form of the end-of-level bud/base correspondence. -/
theorem runCurrentBucket_exhausted_base_eq (B : CurrentBucketState M i cut)
    (hrep : LowerBlossomRepresentation M cut B.state B.forest)
    (hoff : MaxLabelsOffRoots B.state B.forest)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (hcomplete : ∀ u v, Bridge M u v → MaximumMatching.edgeTenacity M u v = some (2 * i + 1) →
      (u, v) ∈ es ∨ (v, u) ∈ es)
    (B' : CurrentBucketState M i cut)
    (hexhausted : (runCurrentBucket hc htop hstageTen B es hqueued).1 = .exhausted B')
    (v : Fin n) (hten : tenacity M v = some (2 * i + 1)) :
    base M v = some (B'.forest.root v) :=
  (base_eq_some_iff v (B'.forest.root v)).2
    (runCurrentBucket_exhausted_base hc htop hstageTen B hrep hoff es hqueued hcomplete B' hexhausted v hten)

end MaximumMatching.Search

end CurrentBucketBlossoms

section CurrentBucketStage

/-! Assemble actual MIN and fixed-bucket processing from a preceding stage.
Newly assigned vertices were fixed roots and lie above the lower cutoff;
consequently MIN preserves the established lower-blossom representation. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

namespace BudGraphInvariant

/-- MIN cannot discover an unassigned vertex below this cutoff: its finite
minimum level would already have been covered at the preceding stage. -/
theorem unknown_tenacity_high {i cut : Nat} {s : State (Fin n)}
    {F : BudForest (Fin n)} (h : BudGraphInvariant M i s F)
    (hcut : cut ≤ 2 * i + 1) (v : Fin n) (hv : s.minLabel v = none) :
    levelLT (some cut) (tenacity M v) := by
  cases ht : tenacity M v with
  | none => trivial
  | some t =>
    by_cases hhigh : cut < t
    · exact hhigh
    · obtain ⟨e, o, he, ho, hep, hop, _hsum⟩ := finite_levels_of_tenacity v t ht
      have hm : minlevel M v = some (min e o) := by
        simp only [minlevel, he, ho, levelMin]
      have hk : min e o ≤ i := by omega
      have hh := h.minInvariant.2.1 v (min e o) hm hk
      rw [hv] at hh
      contradiction

end BudGraphInvariant

section
variable [DecidableRel G.Adj]

/-- Rank relabeling retains all roots. Existing represented vertices keep
their fibers, and new MIN vertices enter as high singleton fibers. -/
theorem scanLevelWithBuds_lower_representation (i cut : Nat)
    (s : State (Fin n)) (F : BudForest (Fin n))
    (h : BudGraphInvariant M i s F) (hcut : cut ≤ 2 * i + 1)
    (hrep : LowerBlossomRepresentation M cut s F) :
    LowerBlossomRepresentation M cut (scanLevelWithBuds M i s F h).1
      (scanLevelWithBuds M i s F h).2 := by
  intro v k _hv
  rw [scanLevelWithBuds_root]
  cases hold : s.minLabel v with
  | none =>
    rw [F.root_of_fixed v (h.unknown_fixed v hold)]
    exact ⟨h.unknown_tenacity_high hcut v hold, Or.inl rfl⟩
  | some j => exact hrep v j hold

/-- Construct the actual post-MIN bucket node. All path representation
witnesses follow from the preceding lower-blossom invariant and are erased. -/
def prepareCurrentBucket (i cut : Nat) (s : State (Fin n))
    (F : BudForest (Fin n)) (hs : StageInvariant M i s)
    (hb : BudGraphInvariant M i s F)
    (hrep : LowerBlossomRepresentation M cut s F)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) : CurrentBucketState M i cut where
  state := (scanLevelWithBuds M i s F hb).1
  forest := (scanLevelWithBuds M i s F hb).2
  stage := scanLevel_stageState M i s hs
  bud := scanLevelWithBuds_invariant M i s F hb hs.maxComplete
  represented := ⟨CurrentBridgeRepresentation.ofLowerBlossoms _ hc
    (fun p hp => Nat.lt_of_lt_of_le (by omega) (htop p hp))
    (by omega) (by omega)
    (scanLevelWithBuds_lower_representation i cut s F hb (by omega) hrep)⟩

/-- Every semantic current bridge appears in the prepared actual bucket,
with either orientation permitted by the undirected edge representation. -/
theorem prepareCurrentBucket_complete (i cut : Nat) (s : State (Fin n))
    (F : BudForest (Fin n)) (hs : StageInvariant M i s)
    (hb : BudGraphInvariant M i s F)
    (hrep : LowerBlossomRepresentation M cut s F)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)
    (u v : Fin n) (hbridge : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (2 * i + 1)) :
    EdgeInBucket (prepareCurrentBucket i cut s F hs hb hrep hc htop hstageTen).state
      (2 * i + 1) u v :=
  scanLevel_stage_bucket_complete M i s hs u v hbridge ht

/-- Execute MIN followed by the entire bucket it produces. No bridge list
or same-stage path representation is supplied by the caller. -/
def runSearchLevel (i cut : Nat) (s : State (Fin n))
    (F : BudForest (Fin n)) (hs : StageInvariant M i s)
    (hb : BudGraphInvariant M i s F)
    (hrep : LowerBlossomRepresentation M cut s F)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) :
    CurrentBucketOutcome M i cut × List (PetalRecord M) :=
  let B := prepareCurrentBucket i cut s F hs hb hrep hc htop hstageTen
  runCurrentBucket hc htop hstageTen B (B.state.bucket (2 * i + 1)) (fun _ he => he)

/-- The entire actual MIN/MAX level restores all invariants needed by the
next level, including its semantic cutoff and absence of shorter augmentations. -/
theorem runSearchLevel_exhausted (i cut : Nat) (s : State (Fin n))
    (F : BudForest (Fin n)) (hs : StageInvariant M i s)
    (hb : BudGraphInvariant M i s F)
    (hrep : LowerBlossomRepresentation M cut s F)
    (hoff : MaxLabelsOffRoots s F)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)
    (B' : CurrentBucketState M i cut)
    (hex : (runSearchLevel i cut s F hs hb hrep hc htop hstageTen).1 = .exhausted B') :
    StageInvariant M (i + 1) B'.state ∧
      LowerBlossomRepresentation M (cut + 2) B'.state B'.forest ∧
      MaxLabelsOffRoots B'.state B'.forest ∧
      AtMostShortestAugmenting M (cut + 4) := by
  let B := prepareCurrentBucket i cut s F hs hb hrep hc htop hstageTen
  have hr : LowerBlossomRepresentation M cut B.state B.forest :=
    scanLevelWithBuds_lower_representation i cut s F hb (by omega) hrep
  have ho : MaxLabelsOffRoots B.state B.forest :=
    scanLevelWithBuds_maxLabelsOffRoots M i s F hb hoff
  have hcomplete : ∀ u v, Bridge M u v →
      MaximumMatching.edgeTenacity M u v = some (2 * i + 1) →
      (u, v) ∈ B.state.bucket (2 * i + 1) ∨ (v, u) ∈ B.state.bucket (2 * i + 1) :=
    prepareCurrentBucket_complete i cut s F hs hb hrep hc htop hstageTen
  have hsi := runCurrentBucket_exhausted_stageInvariant hc htop hstageTen B hr
    _ (fun _ he => he) hcomplete B' hex
  have hbr := runCurrentBucket_exhausted_lower_representation hc htop hstageTen B hr ho
    _ (fun _ he => he) hcomplete B' hex
  have hbound := runCurrentBucket_exhausted_next_lower_bound hc htop hstageTen B hr ho
    _ (fun _ he => he) hcomplete B' hex
  have hroot := runCurrentBucket_maxLabelsOffRoots hc htop hstageTen B
    _ (fun _ he => he) ho
  change (runCurrentBucket hc htop hstageTen B _ (fun _ he => he)).1 = .exhausted B' at hex
  rw [hex] at hroot
  refine ⟨hsi, ?_, hroot, ?_⟩
  · simpa only [hstageTen] using hbr
  · simpa only [show cut + 4 = 2 * (i + 1) + 1 by omega] using hbound

/-- When there is no free-free edge, the actual first MIN scan establishes
the next stage without any tenacity-one MAX vertices. -/
theorem first_scan_stageInvariant
    (hnoaug : ∀ p : AltPath M, p.Augmenting → 1 < p.length) :
    StageInvariant M 1 (scanLevel M 0 (initial M)) := by
  apply searchLevel_stageInvariant M 0 [] (initial M) (initial_stageInvariant M)
  · intro v hv
    exact False.elim (List.not_mem_nil hv)
  · intro v hv
    have hh := tenacity_above_one_of_no_short_augmenting hnoaug v
    rw [hv] at hh
    change 1 < 1 at hh
    omega

end
end MaximumMatching.Search

end CurrentBucketStage
