import MaximumMatching.LevelSearch
import MaximumMatching.RecoverableBucket
import MaximumMatching.OperationalMinArms
import MaximumMatching.OperationalBridgeArms

/-! Complete executable shortest augmenting-path search. Runtime parity arms
are carried through the same MIN/MAX decisions as the proved raw search and
expanded from the exact computed DDFS output. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

inductive ShortestAugmentingOutcome (M : Matching G) where
  | maximum (noAugmenting : M.NoAugmentingPath)
  | found (path : AltPath M) (augmenting : path.Augmenting)
      (shortest : ∀ q : AltPath M, q.Augmenting → path.length ≤ q.length)

section
variable [DecidableRel G.Adj]

/-- Search successive actual levels while retaining computed arms. On a
disjoint DDFS output, the result is an actual matching path, not an existence
proof or an enumeration over matching paths. -/
def runLevelsWithArms {i cut : Nat} (S : LevelSearchState M i cut)
    (A : OperationalArms M S.state S.forest) :
    ShortestAugmentingOutcome M × List (PetalRecord M) :=
  if hdone : n ≤ 2 * i + 1 then
    (.maximum (by
      intro p hp
      have hb := S.bound p hp
      have ht := S.threshold
      have hn := p.length_lt_vertices
      omega), [])
  else
    let B := prepareCurrentBucket i cut S.state S.forest S.stage S.bud S.lower
      S.odd S.bound S.threshold
    let nextArms : OperationalArms M B.state B.forest := A.afterMin S.bud S.stage.maxHasMin
    let result := runRecoverableBucket S.odd S.bound S.threshold B nextArms
      (B.state.bucket (2 * i + 1)) (fun _ he => he)
    match hout : result.1 with
    | .found B' A' W =>
      let p := W.recover A' S.odd S.bound S.threshold
      (.found p.val p.property.1 p.property.2.2.2.2.2, result.2)
    | .exhausted B' A' =>
      have he : (runSearchLevel i cut S.state S.forest S.stage S.bud S.lower
          S.odd S.bound S.threshold).1 = .exhausted B' := by
        have hh := runRecoverableBucket_erase S.odd S.bound S.threshold B nextArms
          (B.state.bucket (2 * i + 1)) (fun _ he => he)
        have hr := congrArg RecoverableBucketOutcome.erase hout
        exact hh.symm.trans hr
      have hnext := runSearchLevel_exhausted i cut S.state S.forest S.stage S.bud
        S.lower S.offRoots S.odd S.bound S.threshold B' he
      let next : LevelSearchState M (i + 1) (cut + 2) := {
        state := B'.state, forest := B'.forest,
        stage := hnext.1, bud := B'.bud, lower := hnext.2.1,
        offRoots := hnext.2.2.1, odd := by have := S.odd; omega,
        threshold := by have := S.threshold; omega,
        bound := by simpa only [Nat.add_assoc] using hnext.2.2.2 }
      let tail := runLevelsWithArms next A'
      (tail.1, result.2 ++ tail.2)
termination_by n - i
decreasing_by omega

/-- Initialize actual computed arms through the first MIN scan. -/
def firstHigherArms (M : Matching G)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → 1 < p.length) :
    OperationalArms M (firstHigherState M hnoaug).state (firstHigherState M hnoaug).forest :=
  (OperationalArms.initial M).afterMin (initial_budGraphInvariant M) (initial_maxLabelsHaveMin M)

/-- Total shortest augmenting-path search from a supplied matching. Both the
length-one branch and the general petal-expansion branch return computed data. -/
def findShortestAugmenting (M : Matching G) :
    ShortestAugmentingOutcome M × List (PetalRecord M) :=
  let f := freeEdgePhase M
  if hz : f.count = 0 then
    let hnoaug := freeEdgePhase_empty_no_short M hz
    runLevelsWithArms (firstHigherState M hnoaug) (firstHigherArms M hnoaug)
  else
    let p := f.path ⟨0, by omega⟩
    (.found p (f.augmenting ⟨0, by omega⟩) (by
      intro q hq
      have hp : p.length = 1 := freeEdgeScan_length _ _
      rw [hp]
      exact q.augmenting_pos hq), [])

end

namespace ShortestAugmentingOutcome

def hasPath : ShortestAugmentingOutcome M → Bool
  | .maximum _ => false
  | .found _ _ _ => true

theorem hasPath_iff (O : ShortestAugmentingOutcome M) :
    O.hasPath = true ↔ ∃ p : AltPath M, p.Augmenting := by
  cases O with
  | maximum hn =>
    constructor
    · intro h; contradiction
    · rintro ⟨p, hp⟩; exact False.elim (hn p hp)
  | found p hp hs => exact ⟨fun _ => ⟨p, hp⟩, fun _ => rfl⟩

theorem maximum_of_hasPath_false (O : ShortestAugmentingOutcome M)
    (h : O.hasPath = false) : M.IsMaximum := by
  cases O with
  | maximum hn => exact M.noAugmentingPath_isMaximum hn
  | found => contradiction

end ShortestAugmentingOutcome
end MaximumMatching.Search
