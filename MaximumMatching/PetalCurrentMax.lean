import MaximumMatching.PetalMax
import MaximumMatching.CurrentBridgeSupport

/-! Concrete MAX events throughout one search level. The path representation
is preserved across the actual assignment/incident-refresh fold and the actual
recorded bud contraction, permitting the next event to reuse proved witnesses. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

/-- The predecessor graph depends only on minimum labels and predecessor
lists; MAX's other state fields and proof witnesses do not affect it. -/
theorem predecessorGraph_eq_of_fields {cap cap' : Nat} {s s' : State V} {F : BudForest V}
    (h : BudGraphInvariant M cap s F) (h' : BudGraphInvariant M cap' s' F)
    (hmin : s'.minLabel = s.minLabel) (hpred : s'.predecessors = s.predecessors) :
    predecessorGraph s' F h' = predecessorGraph s F h := by
  unfold predecessorGraph
  congr 1
  · unfold budEdge
    rw [hmin, hpred]
  · rw [hmin]

/-- Transport actual edge/arm witnesses across state updates that preserve
MIN's data. The new stage invariant is proved separately by the state update. -/
noncomputable def CurrentBridgeRepresentation.of_same_min_data {cap cap' cut : Nat}
    {s s' : State V} {F : BudForest V} {h : BudGraphInvariant M cap s F}
    (P : CurrentBridgeRepresentation M cut h) (h' : BudGraphInvariant M cap' s' F)
    (hmin : s'.minLabel = s.minLabel) (hpred : s'.predecessors = s.predecessors) :
    CurrentBridgeRepresentation M cut h' := by
  let lift : ∀ {u v}, (DDFS.fixedRootGraph (predecessorGraph s' F h') F).Edge u v →
      (DDFS.fixedRootGraph (predecessorGraph s F h) F).Edge u v := by
    intro u v he
    simpa only [predecessorGraph_eq_of_fields h h' hmin hpred] using he
  refine {
    weighted := {
      phase := P.weighted.phase
      segment := fun he => P.weighted.segment (lift he)
      first := fun he => P.weighted.first (lift he)
      last := fun he => P.weighted.last (lift he)
      start_phase := fun he => P.weighted.start_phase (lift he)
      end_phase := fun he => P.weighted.end_phase (lift he)
      interior := fun he => P.weighted.interior (lift he) }
    phase := ?_
    drop := ?_
    high := ?_
    tops := ?_ }
  · intro v
    simpa only [hmin] using P.phase v
  · intro u v he
    simpa only [hmin] using P.drop (lift he)
  · intro v k hv
    apply P.high v k
    simpa only [hmin] using hv
  · intro u v hb ht hu hv
    have hu' : ∃ k, s.minLabel u = some k := by simpa only [hmin] using hu
    have hv' : ∃ k, s.minLabel v = some k := by simpa only [hmin] using hv
    simpa only [BridgeEndpointArms, hmin] using P.tops u v hb ht hu' hv'

private theorem refreshKnownEdge_predecessors [DecidableRel G.Adj]
    (s : State V) (u v : V) :
    (refreshKnownEdge M u v s).predecessors = s.predecessors := by
  unfold refreshKnownEdge
  split
  · split <;> rfl
  · rfl

private theorem refreshKnownEdges_predecessors [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) :
    (refreshKnownEdges M xs s).predecessors = s.predecessors := by
  induction xs generalizing s with
  | nil => rfl
  | cons e es ih =>
    exact (ih (refreshKnownEdge M e.1 e.2 s)).trans (refreshKnownEdge_predecessors s e.1 e.2)

section Finite
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G} [DecidableRel G.Adj]

theorem maxProcessVertex_predecessors (M : Matching G) (i : Nat) (v : Fin n)
    (s : State (Fin n)) : (maxProcessVertex M i v s).predecessors = s.predecessors := by
  have ha : (assignMax s (2 * i + 1) v).predecessors = s.predecessors := by
    unfold assignMax
    split <;> rfl
  unfold maxProcessVertex
  dsimp only
  split
  · exact ha
  · split
    · exact (refreshKnownEdges_predecessors _ _).trans ha
    · exact ha

theorem maxProcessVertices_predecessors (M : Matching G) (i : Nat) (vs : List (Fin n))
    (s : State (Fin n)) : (maxProcessVertices M i vs s).predecessors = s.predecessors := by
  induction vs generalizing s with
  | nil => rfl
  | cons v vs ih =>
    exact (ih (maxProcessVertex M i v s)).trans (maxProcessVertex_predecessors M i v s)

namespace PetalRecord
variable {cut : Nat}

omit [DecidableRel G.Adj] in
/-- The preserved current-level representation proves each computed new root
belongs to the actual trigger support, after any preceding same-level events. -/
theorem newRoots_support_of_current (R : PetalRecord M)
    (P : CurrentBridgeRepresentation M cut R.invariant)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hten : R.tenacity = cut + 2) (v : Fin n) (hv : v ∈ R.newRoots) :
    MaximumMatching.tenacity M v = some R.tenacity ∧ InSupport M R.left R.right v := by
  obtain ⟨hsel, hne⟩ := (R.mem_newRoots v).1 hv
  have hh := P.colored_region_support hc htop R.left R.right R.trigger.1
    (by rw [← hten]; exact R.trigger.2) R.starts_assigned.1 R.starts_assigned.2
    R.bottleneck R.selected R.trees R.region v hsel hne
  exact ⟨by simpa only [hten] using hh.1, hh.2⟩

/-- Actual assignment and incident refresh preserve the full stage and graph
invariants, and correctly label exactly the supplied computed root list. -/
theorem maxEvent_correct_of_current (R : PetalRecord M)
    (P : CurrentBridgeRepresentation M cut R.invariant) (i cutoff : Nat)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hten : R.tenacity = cut + 2) (hstageTen : cut + 2 = 2 * i + 1)
    (_hcap : R.cap = i + 1) (hstage : StageState M (i + 1) cutoff R.prior) :
    StageState M (i + 1) cutoff (R.maxEvent i).1 ∧
      BudGraphInvariant M (i + 1) (R.maxEvent i).1 (R.maxEvent i).2 ∧
      (∀ v, v ∈ R.newRoots → (R.maxEvent i).1.maxLabel v = maxlevel M v) ∧
      (∀ v k, R.prior.maxLabel v = some k → (R.maxEvent i).1.maxLabel v = some k) := by
  have hroots : ∀ v, v ∈ R.newRoots → MaximumMatching.tenacity M v = some (2 * i + 1) := by
    intro v hv
    have hh := (R.newRoots_support_of_current P hc htop hten v hv).1
    simpa only [hten, hstageTen] using hh
  have hs := maxProcessVertices_stageState M i cutoff R.newRoots R.prior hstage hroots
  refine ⟨hs, ?_, ?_, ?_⟩
  · refine ⟨hs.min, hs.minBound, ?_, ?_⟩
    · intro v k hv
      have hold : R.prior.minLabel v = some k := (R.maxEvent_minLabel i v).symm.trans hv
      obtain ⟨j, hj⟩ := R.after_invariant.rootAssigned v k hold
      exact ⟨j, (R.maxEvent_minLabel i (R.after.root v)).trans hj⟩
    · intro v
      exact (R.after_invariant.rankLabel v).trans (congrArg (fun x : Option Nat => x.getD 0)
        (R.maxEvent_minLabel i v).symm)
  · intro v hv
    exact maxProcessVertices_member_correct M i cutoff R.newRoots R.prior hstage hroots v hv
  · intro v k hv
    exact maxProcessVertices_preserves_known_maxLabel M i cutoff R.newRoots R.prior hstage hroots v k hv

/-- The actual updated state and forest carry the constructed representation
for subsequent current-level bridges. Only the independently proved graph
invariant is supplied; the path data are preserved from the preceding event. -/
noncomputable def maxEvent_representation (R : PetalRecord M)
    (P : CurrentBridgeRepresentation M cut R.invariant) (i : Nat) {cap' : Nat}
    (h' : BudGraphInvariant M cap' (R.maxEvent i).1 R.after) :
    CurrentBridgeRepresentation M cut h' :=
  (R.afterBridgeRepresentation P).of_same_min_data h'
    (funext (R.maxEvent_minLabel i)) (maxProcessVertices_predecessors M i R.newRoots R.prior)

end PetalRecord
end Finite
end MaximumMatching.Search
