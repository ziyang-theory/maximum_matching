import MaximumMatching.CurrentBucketProgress
import MaximumMatching.PetalDisjointTransport
import MaximumMatching.MatchingSupportComplete
import MaximumMatching.GeneralSupport

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
