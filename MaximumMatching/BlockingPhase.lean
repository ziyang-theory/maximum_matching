import MaximumMatching.BlockingPhaseStart
import MaximumMatching.ActiveSearchInitial
import MaximumMatching.BlockingBucket
import MaximumMatching.PhaseBound

/-! Complete deletion-aware maximal shortest blocking phases and their outer
matching solver. The first computed witness is retained and expanded once;
continued live DDFS uses the same labels, matching and current bridge bucket.
The phase-count theorem does not assert a bound on concrete running time. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}
variable [DecidableRel G.Adj]

/-- Recover the already computed first witness, delete its root classes, and
continue the current bucket. Previously processed triggers are merely skipped
because their roots were merged; the first found trigger is now inactive. -/
def resumeBlockingPhase {i cut : Nat}
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)
    (B : CurrentBucketState M i cut) (A : OperationalArms M B.state B.forest)
    (W : CurrentBucketWitness B) (es : List (Fin n × Fin n))
    (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1)) :
    BlockingBucketResult (ActiveSearchState.initial B A) es := by
  let S := ActiveSearchState.initial B A
  let p := W.recover A hc htop hstageTen
  let T := S.remove (S.pathRoots p.val)
  let result := runBlockingBucket hc htop hstageTen T es hqueued
  exact BlockingBucketResult.prependRemoved S p.val p.property.1 p.property.2.2.2.1
    (fun j => ActiveSearchState.initial_root_live B A (p.val.vertex j))
    (fun j => (W.recover_coverage A hc htop hstageTen).2.2 _ ⟨j, rfl⟩) result

theorem resumeBlockingPhase_maximalShortest {i cut : Nat}
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)
    (B : CurrentBucketState M i cut) (A : OperationalArms M B.state B.forest)
    (W : CurrentBucketWitness B) (es : List (Fin n × Fin n))
    (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (hcover : ∀ p : AltPath M, p.Augmenting → p.length = 2 * i + 1 →
      ∃ u v, (u, v) ∈ es ∧
        BottomBridgeArms (predecessorGraph B.state B.forest B.bud) B.forest u v
          (fun w => ∃ j, p.vertex j = w)) :
    (resumeBlockingPhase hc htop hstageTen B A W es hqueued).family.MaximalShortest (2 * i + 1) := by
  apply BlockingBucketResult.maximalShortest _ (hstageTen ▸ htop)
  intro p hp hlen
  obtain ⟨u, v, he, ha⟩ := hcover p hp hlen
  exact ⟨u, v, he, ActiveSearchState.initial_root_live B A u,
    ActiveSearchState.initial_root_live B A v, ActiveSearchState.initial_arms B A ha⟩

/-- Computed family with its two search contracts proved from execution. -/
structure BlockingPhaseResult (M : Matching G) where
  family : AugmentingFamily M
  complete : family.count = 0 → M.NoAugmentingPath
  shortest : family.count ≠ 0 → ∃ l, family.MaximalShortest l

/-- Execute one full phase. Length one uses the greedy free-edge scan; higher
levels use MIN/MAX until the first witness, followed by deletion-aware DDFS. -/
def blockingPhaseResult (M : Matching G) : BlockingPhaseResult M :=
  let f := freeEdgePhase M
  if hz : f.count = 0 then
    let hnoaug := freeEdgePhase_empty_no_short M hz
    match locateBlockingPhase (firstHigherState M hnoaug) (firstHigherArms M hnoaug) with
    | .maximum hn => ⟨.empty, fun _ => hn, fun h => False.elim (h rfl)⟩
    | .found i cut hc ht hstageTen B A W es hqueued hcover =>
      let result := resumeBlockingPhase hc ht hstageTen B A W es hqueued
      have hmax := resumeBlockingPhase_maximalShortest hc ht hstageTen B A W es hqueued hcover
      ⟨result.family, (by
        intro hz'
        let p := W.recover A hc ht hstageTen
        exact False.elim (hmax.maximal p.val p.property.1 p.property.2.2.2.1 (by
          intro j
          have hj : j.val < result.family.count := j.isLt
          omega))), fun _ => ⟨2 * i + 1, hmax⟩⟩
  else
    ⟨f, fun he => False.elim (hz he), fun _ => ⟨1, freeEdgePhase_maximalShortest M⟩⟩

def blockingPhase (M : Matching G) : AugmentingFamily M := (blockingPhaseResult M).family

theorem blockingPhase_complete : PhaseDriver.Complete (blockingPhase (G := G)) :=
  fun M => (blockingPhaseResult M).complete

theorem blockingPhase_shortestBlocking : PhaseDriver.ShortestBlocking (blockingPhase (G := G)) :=
  fun M => (blockingPhaseResult M).shortest

/-- Repeated actual blocking phases, with executable matching flips. -/
def runBlockingPhases (M : Matching G) : PhaseDriver.Result G :=
  PhaseDriver.run (blockingPhase (G := G)) M

theorem runBlockingPhases_isMaximum (M : Matching G) :
    (runBlockingPhases M).matching.IsMaximum :=
  PhaseDriver.run_isMaximum _ blockingPhase_complete M

theorem runBlockingPhases_positivePhases_le_two_sqrt (M : Matching G) :
    (runBlockingPhases M).positivePhases ≤ 2 * Nat.sqrt n :=
  PhaseDriver.run_positivePhases_le_two_sqrt _ blockingPhase_shortestBlocking M

/-- A total maximum-cardinality matching solver for finite simple graphs. -/
def maximumMatching (G : Graph (Fin n)) [DecidableRel G.Adj] : Matching G :=
  (runBlockingPhases (Matching.empty G)).matching

theorem maximumMatching_isMaximum (G : Graph (Fin n)) [DecidableRel G.Adj] :
    (maximumMatching G).IsMaximum := runBlockingPhases_isMaximum (Matching.empty G)

end MaximumMatching.Search
