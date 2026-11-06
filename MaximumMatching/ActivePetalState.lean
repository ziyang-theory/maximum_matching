import MaximumMatching.ActivePetalArms
import MaximumMatching.BlockingBucketRemoval
import MaximumMatching.ActivePetalTransport

/-! The actual MAX state and computed arms after a live petal event. The full
semantic representation is reconstructed from those runtime arms and the
preserved root bound. -/
namespace MaximumMatching.Search.ActivePetalRecord
variable {n i cut : Nat} {G : Graph (Fin n)} {M : Matching G} [DecidableRel G.Adj]

/-- Execute the current MAX update and retain its full matching invariants. -/
def afterBucket (R : ActivePetalRecord M i cut)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) : CurrentBucketState M i cut where
  state := R.maxEvent.1
  forest := R.after
  stage := by
    obtain ⟨P⟩ := R.input.B.represented
    exact (R.maxEvent_correct_of_current P hc htop hstageTen).1
  bud := by
    obtain ⟨P⟩ := R.input.B.represented
    exact (R.maxEvent_correct_of_current P hc htop hstageTen).2.1
  represented := by
    obtain ⟨P⟩ := R.input.B.represented
    exact ⟨CurrentBridgeRepresentation.ofOperationalArms
      (OperationalArms.afterActiveMax R hc htop hstageTen)
      (R.maxEvent_correct_of_current P hc htop hstageTen).1
      (R.maxEvent_correct_of_current P hc htop hstageTen).2.1
      hstageTen (R.maxEvent_high P)⟩

theorem afterBucket_graph (R : ActivePetalRecord M i cut)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) :
    predecessorGraph (R.afterBucket hc htop hstageTen).state
      (R.afterBucket hc htop hstageTen).forest (R.afterBucket hc htop hstageTen).bud =
      predecessorGraph R.prior R.after R.after_invariant :=
  predecessorGraph_eq_of_fields R.after_invariant (R.afterBucket hc htop hstageTen).bud
    (funext R.maxEvent_minLabel) (maxProcessVertices_predecessors M i R.newRoots R.prior)

/-- The next live node uses the actual updated labels, forest, stored routes,
and surviving fixed roots. Every live root still reaches a live bottom. -/
def afterPetal (R : ActivePetalRecord M i cut)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) : ActiveSearchState M i cut where
  B := R.afterBucket hc htop hstageTen
  A := OperationalArms.afterActiveMax R hc htop hstageTen
  live := R.afterLive
  live_fixed := fun v hv => ((R.mem_afterLive v).1 hv).2
  reach := by
    rw [R.afterBucket_graph hc htop hstageTen]
    exact R.after_reach

theorem afterPetal_graph (R : ActivePetalRecord M i cut)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) :
    (R.afterPetal hc htop hstageTen).graph = R.afterGraph := by
  change DDFS.RecursiveRemoval.restricted
    (predecessorGraph (R.afterBucket hc htop hstageTen).state
      (R.afterBucket hc htop hstageTen).forest (R.afterBucket hc htop hstageTen).bud) R.afterLive = _
  rw [R.afterBucket_graph hc htop hstageTen]

theorem afterPetal_monotone (R : ActivePetalRecord M i cut)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) :
    R.input.Monotone (R.afterPetal hc htop hstageTen) :=
  ⟨R.after_root_congr, R.after_root_inactive⟩

theorem afterPetal_accounted (R : ActivePetalRecord M i cut)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) :
    (R.afterPetal hc htop hstageTen).Accounted R.left R.right :=
  Or.inl R.after_trigger_equal

theorem afterPetal_bucket_mono (R : ActivePetalRecord M i cut)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)
    (u v : Fin n) (t : Nat) (h : (u, v) ∈ R.prior.bucket t) :
    (u, v) ∈ (R.afterPetal hc htop hstageTen).B.state.bucket t :=
  R.maxEvent_bucket_mono u v t h

/-- Vertex-contained live arms survive the computed contraction. The MAX
assignment changes neither minimum labels nor predecessor lists. -/
theorem afterPetal_liveBridgeArms (R : ActivePetalRecord M i cut)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)
    {u v : Fin n} {Q : Fin n → Prop} (h : R.input.LiveBridgeArms u v Q) :
    (R.afterPetal hc htop hstageTen).LiveBridgeArms u v Q := by
  refine ⟨?_, ?_, ?_⟩
  · have hh := R.after_root_live (R.forest.root u) h.1
    rwa [R.after_root_congr _ _ (R.forest.root_idempotent u)] at hh
  · have hh := R.after_root_live (R.forest.root v) h.2.1
    rwa [R.after_root_congr _ _ (R.forest.root_idempotent v)] at hh
  · change BottomBridgeArms (R.afterPetal hc htop hstageTen).graph R.after u v Q
    rw [R.afterPetal_graph hc htop hstageTen]
    exact R.transport_bottom_bridge_arms h.2.2

end MaximumMatching.Search.ActivePetalRecord
