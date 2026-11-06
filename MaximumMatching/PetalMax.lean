import MaximumMatching.PetalRecord
import MaximumMatching.MatchingSupportSound
import MaximumMatching.SearchStage

/-! Concrete MAX processing of the roots selected by an actual petal record.
Only selected non-bottleneck roots receive current-tenacity assignments; old
descendants in their fibers are not mistaken for new current-tenacity roots.
The executable fold includes the source's incident bridge refresh. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

section
variable [DecidableRel G.Adj]

theorem maxProcessVertices_minLabel (M : Matching G) (i : Nat) (vs : List (Fin n))
    (s : State (Fin n)) (v : Fin n) :
    (maxProcessVertices M i vs s).minLabel v = s.minLabel v := by
  induction vs generalizing s with
  | nil => rfl
  | cons u us ih => exact (ih (maxProcessVertex M i u s)).trans (maxProcessVertex_labels M i u v s).1

theorem maxProcessVertices_outside_maxLabel (M : Matching G) (i : Nat) (vs : List (Fin n))
    (s : State (Fin n)) (v : Fin n) (hv : v ∉ vs) :
    (maxProcessVertices M i vs s).maxLabel v = s.maxLabel v := by
  induction vs generalizing s with
  | nil => rfl
  | cons u us ih =>
    have hne : v ≠ u := fun he => hv (List.mem_cons.mpr (Or.inl he))
    have htail : v ∉ us := fun hm => hv (List.mem_cons_of_mem u hm)
    have ha : (assignMax s (2 * i + 1) u).maxLabel v = s.maxLabel v := by
      unfold assignMax
      split
      · rfl
      · exact ite_eq_right hne
    exact (ih (maxProcessVertex M i u s) htail).trans ((maxProcessVertex_labels M i u v s).2.trans ha)

end

namespace PetalRecord

/-- The actual computed root list used by MAX, excluding the bottleneck. -/
def newRoots (R : PetalRecord M) : List (Fin n) :=
  R.trees.vertices.filter fun v => decide (v ≠ R.bottleneck)

theorem mem_newRoots (R : PetalRecord M) (v : Fin n) :
    v ∈ R.newRoots ↔ R.selected v ∧ v ≠ R.bottleneck := by
  simp only [newRoots, List.mem_filter, decide_eq_true_eq, R.trees.mem_vertices]

theorem newRoots_fixed (R : PetalRecord M) (v : Fin n) (hv : v ∈ R.newRoots) :
    R.forest.parent v = v := R.selected_fixed v ((R.mem_newRoots v).1 hv).1

/-- Current tenacity and actual trigger support are derived for each listed
root from the computed trees and lower-blossom input representation. -/
theorem newRoots_support (R : PetalRecord M) (cut : Nat) (hc : cut % 2 = 1)
    (htop : AtMostShortestAugmenting M (cut + 2))
    (hhalf : 2 * R.cap ≤ cut + 3)
    (hrep : LowerBlossomRepresentation M cut R.prior R.forest)
    (hten : R.tenacity = cut + 2) (v : Fin n) (hv : v ∈ R.newRoots) :
    MaximumMatching.tenacity M v = some R.tenacity ∧ InSupport M R.left R.right v := by
  obtain ⟨hsel, hne⟩ := (R.mem_newRoots v).1 hv
  have hh := R.invariant.colored_region_support hc htop hhalf hrep R.left R.right
    R.trigger.1 (by rw [← hten]; exact R.trigger.2) R.starts_assigned.1 R.starts_assigned.2
    R.bottleneck R.selected R.trees R.region v hsel hne
  exact ⟨by simpa only [hten] using hh.1, hh.2⟩

section
variable [DecidableRel G.Adj]

/-- Process the computed root list using the actual assignment and incident
refresh operation, and retain the actual contracted forest. -/
def maxEvent (R : PetalRecord M) (i : Nat) : State (Fin n) × BudForest (Fin n) :=
  (maxProcessVertices M i R.newRoots R.prior, R.after)

theorem maxEvent_minLabel (R : PetalRecord M) (i : Nat) (v : Fin n) :
    (R.maxEvent i).1.minLabel v = R.prior.minLabel v :=
  maxProcessVertices_minLabel M i R.newRoots R.prior v

theorem maxEvent_outside (R : PetalRecord M) (i : Nat) (v : Fin n) (hv : v ∉ R.newRoots) :
    (R.maxEvent i).1.maxLabel v = R.prior.maxLabel v :=
  maxProcessVertices_outside_maxLabel M i R.newRoots R.prior v hv

/-- A concrete petal event preserves the complete local MIN/MAX stage state
and the matching-derived bud graph, sets every newly selected root's correct
maximum level, and preserves every prior maximum-level assignment. The only
path-representation premise is at the preceding blossom cutoff. -/
theorem maxEvent_correct (R : PetalRecord M) (i cut cutoff : Nat)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hrep : LowerBlossomRepresentation M cut R.prior R.forest)
    (hten : R.tenacity = cut + 2) (hstageTen : cut + 2 = 2 * i + 1)
    (hcap : R.cap = i + 1) (hstage : StageState M (i + 1) cutoff R.prior) :
    StageState M (i + 1) cutoff (R.maxEvent i).1 ∧
      BudGraphInvariant M (i + 1) (R.maxEvent i).1 (R.maxEvent i).2 ∧
      (∀ v, v ∈ R.newRoots → (R.maxEvent i).1.maxLabel v = maxlevel M v) ∧
      (∀ v k, R.prior.maxLabel v = some k → (R.maxEvent i).1.maxLabel v = some k) := by
  have hhalf : 2 * R.cap ≤ cut + 3 := by omega
  have hroots : ∀ v, v ∈ R.newRoots → MaximumMatching.tenacity M v = some (2 * i + 1) := by
    intro v hv
    have hh := (R.newRoots_support cut hc htop hhalf hrep hten v hv).1
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

end

end PetalRecord
end MaximumMatching.Search
