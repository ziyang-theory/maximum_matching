import MaximumMatching.CurrentBucketStage
import MaximumMatching.FreeEdgePhase

/-! Executable search through successive MIN/MAX levels. Exhausted buckets
restore the next level's invariants; a found result retains the computed DDFS
certificate and all actual petal records. Recursive matching-path recovery
and removal for a whole blocking family are separate operations. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

/-- State immediately before a higher MIN level, with erased induction
invariants. The cutoff describes already completed lower blossoms. -/
structure LevelSearchState (M : Matching G) (i cut : Nat) where
  state : State (Fin n)
  forest : BudForest (Fin n)
  stage : StageInvariant M i state
  bud : BudGraphInvariant M i state forest
  lower : LowerBlossomRepresentation M cut state forest
  offRoots : MaxLabelsOffRoots state forest
  odd : cut % 2 = 1
  threshold : cut + 2 = 2 * i + 1
  bound : AtMostShortestAugmenting M (cut + 2)

/-- Search returns either a proved stopping condition or the actual raw
shortest-path certificate. The latter is not a choice-selected matching path. -/
inductive LevelSearchOutcome (M : Matching G) where
  | maximum (noAugmenting : M.NoAugmentingPath)
  | freeEdge (path : AltPath M) (augmenting : path.Augmenting) (length_one : path.length = 1)
  | found (i cut : Nat) (state : CurrentBucketState M i cut)
      (witness : CurrentBucketWitness state) (odd : cut % 2 = 1)
      (bound : AtMostShortestAugmenting M (cut + 2))
      (threshold : cut + 2 = 2 * i + 1)

section
variable [DecidableRel G.Adj]

/-- Run consecutive concrete MIN/MAX levels, retaining petal history across
levels. The finite simple-path length bound gives a proved stopping test. -/
def runLevels {i cut : Nat} (S : LevelSearchState M i cut) :
    LevelSearchOutcome M × List (PetalRecord M) :=
  if hdone : n ≤ 2 * i + 1 then
    (.maximum (by
      intro p hp
      have hb := S.bound p hp
      have ht := S.threshold
      have hn := p.length_lt_vertices
      omega), [])
  else
    let result := runSearchLevel i cut S.state S.forest S.stage S.bud S.lower
      S.odd S.bound S.threshold
    match hout : result.1 with
    | .found B W => (.found i cut B W S.odd S.bound S.threshold, result.2)
    | .exhausted B =>
      have hnext := runSearchLevel_exhausted i cut S.state S.forest S.stage S.bud
        S.lower S.offRoots S.odd S.bound S.threshold B hout
      let next : LevelSearchState M (i + 1) (cut + 2) := {
        state := B.state, forest := B.forest,
        stage := hnext.1, bud := B.bud, lower := hnext.2.1,
        offRoots := hnext.2.2.1, odd := by have := S.odd; omega,
        threshold := by have := S.threshold; omega,
        bound := by simpa only [Nat.add_assoc] using hnext.2.2.2 }
      let tail := runLevels next
      (tail.1, result.2 ++ tail.2)
termination_by n - i
decreasing_by omega

/-- Initialize higher-level search after the length-one case has been ruled
out. MIN is executed on the real initial state; no forest is supplied. -/
def firstHigherState (M : Matching G)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → 1 < p.length) :
    LevelSearchState M 1 1 where
  state := scanLevel M 0 (initial M)
  forest := uncontractedForest (scanLevel M 0 (initial M))
  stage := first_scan_stageInvariant hnoaug
  bud := uncontractedForest_invariant _ _
    (first_scan_stageInvariant hnoaug).min (first_scan_stageInvariant hnoaug).minBound
  lower := uncontracted_lower_representation_one _ hnoaug
  offRoots := by
    intro v _
    exact scanCandidates_maxLabel (allCandidates n) (initial M) 0 v
  odd := rfl
  threshold := rfl
  bound := by
    intro p hp
    have hh := hnoaug p hp
    have hodd := hp.1
    omega

/-- Search from the actual initial matching state, handling the free-free
edge case directly before executing all higher MIN/MAX levels. -/
def findAugmenting (M : Matching G) : LevelSearchOutcome M × List (PetalRecord M) :=
  let f := freeEdgePhase M
  if hz : f.count = 0 then
    runLevels (firstHigherState M (freeEdgePhase_empty_no_short M hz))
  else
    (.freeEdge (f.path ⟨0, by omega⟩) (f.augmenting ⟨0, by omega⟩)
      (freeEdgeScan_length _ _), [])

end

namespace LevelSearchOutcome

def hasPath : LevelSearchOutcome M → Bool
  | .maximum _ => false
  | .freeEdge _ _ _ => true
  | .found _ _ _ _ _ _ _ => true

/-- The computed outcome detects existence exactly, even though converting
the raw DDFS witness into a computed matching path remains a separate step. -/
theorem hasPath_iff (O : LevelSearchOutcome M) :
    O.hasPath = true ↔ ∃ p : AltPath M, p.Augmenting := by
  cases O with
  | maximum hno =>
    constructor
    · intro h; contradiction
    · rintro ⟨p, hp⟩; exact False.elim (hno p hp)
  | freeEdge p hp _ =>
    exact ⟨fun _ => ⟨p, hp⟩, fun _ => rfl⟩
  | found i cut B W hc ht he =>
    constructor
    · intro _
      obtain ⟨p, hp, _⟩ := W.shortest_augmenting hc ht he
      exact ⟨p, hp⟩
    · intro _; rfl

theorem maximum_of_hasPath_false (O : LevelSearchOutcome M) (h : O.hasPath = false) :
    M.IsMaximum := by
  cases O with
  | maximum hn => exact M.noAugmentingPath_isMaximum hn
  | freeEdge => contradiction
  | found => contradiction

end LevelSearchOutcome

section
variable [DecidableRel G.Adj]

/-- The concrete MIN/MAX/DDFS search is a decision procedure for maximal
cardinality of the supplied matching. This does not yet construct a larger
matching from the higher-level raw certificate. -/
def isMaximum (M : Matching G) : Bool := !(findAugmenting M).1.hasPath

theorem isMaximum_iff (M : Matching G) : isMaximum M = true ↔ M.IsMaximum := by
  rw [M.isMaximum_iff_noAugmentingPath]
  constructor
  · intro h p hp
    have ht := ((findAugmenting M).1.hasPath_iff).2 ⟨p, hp⟩
    simp only [isMaximum, ht] at h
    contradiction
  · intro h
    have hf : (findAugmenting M).1.hasPath = false := by
      cases he : (findAugmenting M).1.hasPath with
      | false => rfl
      | true =>
        obtain ⟨p, hp⟩ := ((findAugmenting M).1.hasPath_iff).1 he
        exact False.elim (h p hp)
    simp only [isMaximum, hf, Bool.not_false]

end

end MaximumMatching.Search
