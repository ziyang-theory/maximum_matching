import MaximumMatching.CurrentBucketStage
import MaximumMatching.MatchingGraphExpansion
import MaximumMatching.MinComplete
import MaximumMatching.OperationalArms
import MaximumMatching.PhaseDriver
import MaximumMatching.RecoverableBucket
import MaximumMatching.RecursiveRemoval

section FreeEdgePhase

/-! The tenacity-one case of a phase: greedily select disjoint free-free
edges from the actual finite edge enumeration. The resulting family is a
maximal family of shortest augmenting paths whenever such an edge exists. -/
namespace MaximumMatching

namespace AugmentingFamily
variable {V : Type} {G : Graph V} {M : Matching G}

def empty : AugmentingFamily M where
  count := 0
  path i := nomatch i
  augmenting i := nomatch i
  disjoint i := nomatch i

/-- Prepend a real augmenting path disjoint from every existing path. -/
def prepend (f : AugmentingFamily M) (p : AltPath M) (hp : p.Augmenting)
    (hd : ∀ i, p.Disjoint (f.path i)) : AugmentingFamily M where
  count := f.count + 1
  path i := if h : i.val = 0 then p else f.path ⟨i.val - 1, by omega⟩
  augmenting i := by
    split
    · exact hp
    · exact f.augmenting _
  disjoint i j hij := by
    split <;> split
    · exact False.elim (hij (Fin.ext (by omega)))
    · exact hd _
    · exact AltPath.disjoint_symm (hd _)
    · apply f.disjoint
      intro he
      exact hij (Fin.ext (by have hh := congrArg Fin.val he; dsimp only at hh; omega))

section Finite
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

theorem mem_vertices_prepend (f : AugmentingFamily M) (p : AltPath M)
    (hp : p.Augmenting) (hd : ∀ i, p.Disjoint (f.path i)) (v : Fin n) :
    v ∈ (f.prepend p hp hd).vertices ↔ (∃ j, p.vertex j = v) ∨ v ∈ f.vertices := by
  rw [mem_vertices]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hz : i.val = 0
    · have he : (f.prepend p hp hd).path i = p := by
        exact dite_eq_left hz
      rw [he] at hi
      exact Or.inl hi
    · let j : Fin f.count := ⟨i.val - 1, by
        have := i.isLt; change i.val < f.count + 1 at this; omega⟩
      have he : (f.prepend p hp hd).path i = f.path j := dite_eq_right hz
      rw [he] at hi
      exact Or.inr ((f.mem_vertices v).2 ⟨j, hi⟩)
  · rintro (hpv | hv)
    · exact ⟨⟨0, by dsimp only [prepend]; omega⟩, hpv⟩
    · obtain ⟨i, hi⟩ := (f.mem_vertices v).1 hv
      refine ⟨⟨i.val + 1, by dsimp only [prepend]; omega⟩, ?_⟩
      simpa [prepend] using hi

end Finite
end AugmentingFamily

namespace Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
private theorem freeEdge_disjoint_of_not_mem (f : AugmentingFamily M)
    (u v : Fin n) (hu : M.Free u) (ha : G.Adj u v)
    (huf : u ∉ f.vertices) (hvf : v ∉ f.vertices) :
    ∀ i, (AltPath.freeEdge u v hu ha).Disjoint (f.path i) := by
  intro i j k he
  have hjlt : j.val < 2 := j.isLt
  by_cases hj : j.val = 0
  · apply huf
    apply (f.mem_vertices u).2
    refine ⟨i, k, ?_⟩
    have hjeq : j = ⟨0, by change 0 < 1 + 1; omega⟩ := Fin.ext hj
    simpa [hjeq, AltPath.freeEdge, AltPath.append, AltPath.trivial] using he.symm
  · apply hvf
    apply (f.mem_vertices v).2
    refine ⟨i, k, ?_⟩
    have hjeq : j = ⟨1, by change 1 < 1 + 1; omega⟩ := Fin.ext (show j.val = 1 by omega)
    simpa [hjeq, AltPath.freeEdge, AltPath.append, AltPath.trivial] using he.symm

/-- Greedy free-edge selection in reverse candidate order. Every decision
uses the current matching and the explicitly selected family vertices. -/
def freeEdgeScan (M : Matching G) : List (Fin n × Fin n) → AugmentingFamily M
  | [] => .empty
  | (u, v) :: es =>
    let f := freeEdgeScan M es
    if h : G.Adj u v ∧ M.mate u = none ∧ M.mate v = none ∧ u ∉ f.vertices ∧ v ∉ f.vertices then
      f.prepend (AltPath.freeEdge u v h.2.1 h.1)
        (AltPath.freeEdge_augmenting u v h.2.1 h.2.2.1 h.1)
        (freeEdge_disjoint_of_not_mem f u v h.2.1 h.1 h.2.2.2.1 h.2.2.2.2)
    else f

theorem freeEdgeScan_length (es : List (Fin n × Fin n)) :
    ∀ j, ((freeEdgeScan M es).path j).length = 1 := by
  induction es with
  | nil => intro j; exact Fin.elim0 j
  | cons e es ih =>
    rcases e with ⟨u, v⟩
    rw [freeEdgeScan]
    by_cases h : G.Adj u v ∧ M.mate u = none ∧ M.mate v = none ∧
        u ∉ (freeEdgeScan M es).vertices ∧ v ∉ (freeEdgeScan M es).vertices
    · rw [dite_eq_left h]
      intro j
      simp only [AugmentingFamily.prepend]
      split
      · rfl
      · exact ih _
    · rw [dite_eq_right h]
      exact ih

/-- Every candidate free-free edge meets the returned family. This is the
maximality invariant of the greedy scan, including rejected and repeated edges. -/
theorem freeEdgeScan_covers (es : List (Fin n × Fin n))
    (u v : Fin n) (he : (u, v) ∈ es) (ha : G.Adj u v)
    (hu : M.Free u) (hv : M.Free v) :
    u ∈ (freeEdgeScan M es).vertices ∨ v ∈ (freeEdgeScan M es).vertices := by
  induction es with
  | nil => exact False.elim (List.not_mem_nil he)
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    rw [freeEdgeScan]
    split
    next h =>
      rcases List.mem_cons.mp he with he | he
      · cases he
        left
        apply (AugmentingFamily.mem_vertices_prepend _ _ _ _ u).2
        exact Or.inl ⟨⟨0, by change 0 < 2; omega⟩, rfl⟩
      · rcases ih he with hu | hv
        · exact Or.inl ((AugmentingFamily.mem_vertices_prepend _ _ _ _ u).2 (Or.inr hu))
        · exact Or.inr ((AugmentingFamily.mem_vertices_prepend _ _ _ _ v).2 (Or.inr hv))
    next h =>
      rcases List.mem_cons.mp he with he | he
      · cases he
        by_cases huf : u ∈ (freeEdgeScan M es).vertices
        · exact Or.inl huf
        · by_cases hvf : v ∈ (freeEdgeScan M es).vertices
          · exact Or.inr hvf
          · exact False.elim (h ⟨ha, hu, hv, huf, hvf⟩)
      · exact ih he

/-- The actual finite tenacity-one phase, with correctness and maximality
proved below. -/
def freeEdgePhase (M : Matching G) : AugmentingFamily M :=
  freeEdgeScan M (allCandidates n)

theorem freeEdgePhase_maximalShortest (M : Matching G) :
    (freeEdgePhase M).MaximalShortest 1 := by
  refine ⟨fun p hp => p.augmenting_pos hp, freeEdgeScan_length _, ?_⟩
  intro p hp hlen hd
  have hadj : G.Adj p.first p.last := by
    have hh := p.adjacent ⟨0, by omega⟩
    have hi : (⟨0 + 1, by omega⟩ : Fin (p.length + 1)) = ⟨p.length, by omega⟩ := Fin.ext (show 1 = p.length by omega)
    simpa only [AltPath.first, AltPath.last, hi] using hh
  have he : (p.first, p.last) ∈ allCandidates n := by
    simp [allCandidates]
  have hcover := freeEdgeScan_covers (M := M) (allCandidates n) p.first p.last he
    hadj p.start_free hp.2
  rcases hcover with hf | hl
  · obtain ⟨i, j, hj⟩ := ((freeEdgePhase M).mem_vertices p.first).1 hf
    exact hd i j ⟨0, by omega⟩ hj
  · obtain ⟨i, j, hj⟩ := ((freeEdgePhase M).mem_vertices p.last).1 hl
    exact hd i j ⟨p.length, by omega⟩ hj

theorem freeEdgePhase_empty_no_short (M : Matching G)
    (hz : (freeEdgePhase M).count = 0) :
    ∀ p : AltPath M, p.Augmenting → 1 < p.length := by
  intro p hp
  have hpos := p.augmenting_pos hp
  by_cases he : p.length = 1
  · exact False.elim ((freeEdgePhase_maximalShortest M).maximal p hp he (by
      intro i
      have hh := i.isLt
      omega))
  · omega

/-- After executing this phase, no augmenting path of length one remains. -/
theorem freeEdgePhase_no_short (M : Matching G)
    (p : AltPath (freeEdgePhase M).run) (hp : p.Augmenting) : 1 < p.length :=
  (freeEdgePhase M).shortest_length_increases 1 (freeEdgePhase_maximalShortest M) p hp

end Search
end MaximumMatching

end FreeEdgePhase

section LevelSearch

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

end LevelSearch

section ShortestAugmentingSearch

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

end ShortestAugmentingSearch

section AugmentingPathArms

/-! Vertex-contained bottom arms for shortest augmentations. The containment
predicate is retained explicitly so deletion can preserve a disjoint path. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

def BottomBridgeArms (H : DDFS.LayeredGraph V) (F : BudForest V)
    (u v : V) (Q : V → Prop) : Prop :=
  ∃ a b : DDFS.Path H, a.ToBottom (F.root u) ∧ b.ToBottom (F.root v) ∧
    a.Disjoint b ∧ (∀ w, a.Contains w → Q w) ∧ (∀ w, b.Contains w → Q w)

namespace BottomBridgeArms

theorem symm {H : DDFS.LayeredGraph V} {F : BudForest V} {u v : V} {Q : V → Prop}
    (h : BottomBridgeArms H F u v Q) : BottomBridgeArms H F v u Q := by
  obtain ⟨a, b, ha, hb, hd, hqa, hqb⟩ := h
  exact ⟨b, a, hb, ha, (fun w hb ha => hd w ha hb), hqb, hqa⟩

theorem of_same_min_data {cap cap' : Nat} {s s' : State V} {F : BudForest V}
    {h : BudGraphInvariant M cap s F} {u v : V} {Q : V → Prop}
    (ha : BottomBridgeArms (predecessorGraph s F h) F u v Q)
    (h' : BudGraphInvariant M cap' s' F)
    (hmin : s'.minLabel = s.minLabel) (hpred : s'.predecessors = s.predecessors) :
    BottomBridgeArms (predecessorGraph s' F h') F u v Q := by
  rw [predecessorGraph_eq_of_fields h h' hmin hpred]
  exact ha

end BottomBridgeArms

namespace BudGraphInvariant
variable {cap cut : Nat} {s : State V} {F : BudForest V}

/-- Compress a shortest augmentation without losing the original-vertex
containment of either arm. Both terminal vertices are free. -/
theorem augmenting_bridge_arms (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1) (ht : AtMostShortestAugmenting M (cut + 2))
    (hrep : LowerBlossomRepresentation M cut s F) (hcap : cut + 2 ≤ 2 * cap + 1)
    (p : AltPath M) (hp : p.Augmenting) (hlen : p.length = cut + 2)
    (I : Fin p.length)
    (hIb : Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩))
    (hIt : MaximumMatching.edgeTenacity M (p.vertex ⟨I.val, by omega⟩)
      (p.vertex ⟨I.val + 1, by omega⟩) = some (cut + 2))
    (hu : ∃ k, s.minLabel (p.vertex ⟨I.val, by omega⟩) = some k)
    (hv : ∃ k, s.minLabel (p.vertex ⟨I.val + 1, by omega⟩) = some k) :
    BottomBridgeArms (predecessorGraph s F h) F
      (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩)
      (fun w => ∃ j, p.vertex j = w) := by
  obtain ⟨hpt, hmax⟩ := p.shortest_augmenting_last_levels hp (hlen ▸ ht)
  rw [hlen] at hpt
  obtain ⟨A, hAI, hA, hAh⟩ := h.current_bridge_left_root hrep p ht hpt hmax I hIb hIt hu
  obtain ⟨J, hIJ, hJ, hJt⟩ := h.current_bridge_right_root hrep p ht hpt hmax I hIb hIt hv
  have hJh : levelLT (some cut) (tenacity M (p.vertex J)) := by
    rw [hJt]; change cut < cut + 2; omega
  obtain ⟨a, haf, hal, _, hav⟩ := h.compress_early_core hc ht hrep hcap p hpt hmax I hIb hIt A hAI hAh
  obtain ⟨b, hbf, hbl, _, hbv⟩ := h.compress_late_core hc ht hrep hcap p hpt hmax I hIb hIt J hIJ hJh
  refine ⟨a, b, ⟨haf.trans hA, ?_⟩, ⟨hbf.trans hJ, ?_⟩, ?_, ?_, ?_⟩
  · have hl := h.minInvariant.2.1 p.first 0 ((minlevel_zero_iff_free p.first).2 p.start_free)
      (Nat.zero_le cap)
    change (s.minLabel a.last).getD 0 = 0
    rw [hal, hl]; rfl
  · have hl := h.minInvariant.2.1 p.last 0 ((minlevel_zero_iff_free p.last).2 hp.2)
      (Nat.zero_le cap)
    change (s.minLabel b.last).getD 0 = 0
    rw [hbl, hl]; rfl
  · intro w haw hbw
    obtain ⟨K, hKA, _, hKw⟩ := (hav w).1 haw
    obtain ⟨L, hJL, _, hLw⟩ := (hbv w).1 hbw
    have he := congrArg Fin.val (p.injective K L (hKw.trans hLw.symm))
    omega
  · intro w hw
    obtain ⟨K, _, _, hKw⟩ := (hav w).1 hw
    exact ⟨K, hKw⟩
  · intro w hw
    obtain ⟨K, _, _, hKw⟩ := (hbv w).1 hw
    exact ⟨K, hKw⟩

end BudGraphInvariant

section Finite
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

theorem CurrentBucketState.augmenting_bridge_arms {i cut : Nat}
    (B : CurrentBucketState M i cut) (hc : cut % 2 = 1)
    (ht : AtMostShortestAugmenting M (cut + 2)) (hstageTen : cut + 2 = 2 * i + 1)
    (hrep : LowerBlossomRepresentation M cut B.state B.forest)
    (p : AltPath M) (hp : p.Augmenting) (hlen : p.length = 2 * i + 1) :
    ∃ u v, Bridge M u v ∧ MaximumMatching.edgeTenacity M u v = some (2 * i + 1) ∧
      BottomBridgeArms (predecessorGraph B.state B.forest B.bud) B.forest u v
        (fun w => ∃ j, p.vertex j = w) := by
  have hl : p.length = cut + 2 := hlen.trans hstageTen.symm
  obtain ⟨hpt, hmax⟩ := p.shortest_augmenting_last_levels hp (hl ▸ ht)
  obtain ⟨I, hIb, hIt, _⟩ := p.general_maxlevel_path_unique_bridge (cut + 2) ht
    (by rwa [hl] at hpt) hmax
  have hk := B.stage.current_bridge_known _ _ hIb (by rwa [← hstageTen])
  obtain ⟨hu, hv⟩ := edgeTenacity_has_minLabels B.state _ _ (2 * i + 1) hk
  exact ⟨_, _, hIb, by rwa [← hstageTen],
    B.bud.augmenting_bridge_arms hc ht hrep (by omega) p hp hl I hIb hIt hu hv⟩

namespace PetalRecord

theorem transport_bottom_bridge_arms (R : PetalRecord M) {u v : Fin n} {Q : Fin n → Prop}
    (ha : BottomBridgeArms (predecessorGraph R.prior R.forest R.invariant) R.forest u v Q) :
    BottomBridgeArms (predecessorGraph R.prior R.after R.after_invariant) R.after u v Q := by
  obtain ⟨p, q, hp, hq, hd, hpQ, hqQ⟩ := ha
  have hpf : R.forest.parent p.first = p.first := by rw [hp.1]; exact R.forest.root_fixed u
  have hqf : R.forest.parent q.first = q.first := by rw [hq.1]; exact R.forest.root_fixed v
  have hpfix : ∀ x, p.Contains x → R.forest.root x = x := by
    rintro x ⟨j, rfl⟩
    exact R.forest.root_of_fixed _ (R.invariant.path_fixed p hpf j)
  have hqfix : ∀ x, q.Contains x → R.forest.root x = x := by
    rintro x ⟨j, rfl⟩
    exact R.forest.root_of_fixed _ (R.invariant.path_fixed q hqf j)
  obtain ⟨a, b, haf, hal, hbf, hbl, hab, hav, hbv⟩ :=
    R.transport_disjoint_bottom_paths p q hpfix hqfix hd hp.2 hq.2
  refine ⟨a, b, ⟨?_, ?_⟩, ⟨?_, ?_⟩, hab, fun w hw => hpQ w (hav w hw),
    fun w hw => hqQ w (hbv w hw)⟩
  · exact haf.trans ((congrArg R.after.root hp.1).trans (R.after_root_old_root u))
  · change (R.prior.minLabel a.last).getD 0 = 0
    rw [hal]; exact hp.2
  · exact hbf.trans ((congrArg R.after.root hq.1).trans (R.after_root_old_root v))
  · change (R.prior.minLabel b.last).getD 0 = 0
    rw [hbl]; exact hq.2

end PetalRecord
end Finite
end MaximumMatching.Search

end AugmentingPathArms

section CurrentBucketBottomArms

/-! Preserve original shortest-path arms through the prefix of the ordinary
bucket search, before the first deletion-aware continuation. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}
variable [DecidableRel G.Adj] {i cut : Nat}
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)

theorem runCurrentBucket_bottom_arms (B : CurrentBucketState M i cut)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (u v : Fin n) (Q : Fin n → Prop)
    (ha : BottomBridgeArms (predecessorGraph B.state B.forest B.bud) B.forest u v Q) :
    let T := (runCurrentBucket hc htop hstageTen B es hqueued).1.state
    BottomBridgeArms (predecessorGraph T.state T.forest T.bud) T.forest u v Q := by
  induction es generalizing B with
  | nil => simpa only [runCurrentBucket, CurrentBucketOutcome.state] using ha
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    rw [runCurrentBucket]
    split
    · exact ih B _ ha
    · split
      · exact ha
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
        exact ih next hq ((R.transport_bottom_bridge_arms ha).of_same_min_data next.bud
          (funext (R.maxEvent_minLabel i)) (maxProcessVertices_predecessors M i R.newRoots R.prior))

theorem runCurrentBucket_bucket_mono (B : CurrentBucketState M i cut)
    (es : List (Fin n × Fin n)) (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
    (u v : Fin n) (t : Nat) (he : (u, v) ∈ B.state.bucket t) :
    (u, v) ∈ (runCurrentBucket hc htop hstageTen B es hqueued).1.state.state.bucket t := by
  induction es generalizing B with
  | nil => simpa only [runCurrentBucket, CurrentBucketOutcome.state] using he
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    rw [runCurrentBucket]
    split
    · exact ih B _ he
    · split
      · exact he
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
        exact ih next hq (R.maxEvent_bucket_mono i u v t he)

end MaximumMatching.Search

end CurrentBucketBottomArms

section BlockingPhaseStart

/-! Locate the first augmenting level while retaining its actual search state
and the complete original bucket. Already processed triggers have equal roots
and are skipped by the continued blocking search. No MIN stage is restarted. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

inductive BlockingPhaseStart (M : Matching G) where
  | maximum (noAugmenting : M.NoAugmentingPath)
  | found (i cut : Nat) (odd : cut % 2 = 1)
      (bound : AtMostShortestAugmenting M (cut + 2)) (threshold : cut + 2 = 2 * i + 1)
      (B : CurrentBucketState M i cut) (A : OperationalArms M B.state B.forest)
      (witness : CurrentBucketWitness B)
      (es : List (Fin n × Fin n))
      (queued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1))
      (coverage : ∀ p : AltPath M, p.Augmenting → p.length = 2 * i + 1 →
        ∃ u v, (u, v) ∈ es ∧
          BottomBridgeArms (predecessorGraph B.state B.forest B.bud) B.forest u v
            (fun w => ∃ j, p.vertex j = w))

section
variable [DecidableRel G.Adj]

/-- The same level search as shortest augmentation, retaining the found
state and runtime arms for same-phase continuation after deletion. -/
def locateBlockingPhase {i cut : Nat} (S : LevelSearchState M i cut)
    (A : OperationalArms M S.state S.forest) : BlockingPhaseStart M :=
  if hdone : n ≤ 2 * i + 1 then
    .maximum (by
      intro p hp
      have hb := S.bound p hp
      have ht := S.threshold
      have hn := p.length_lt_vertices
      omega)
  else
    let B := prepareCurrentBucket i cut S.state S.forest S.stage S.bud S.lower
      S.odd S.bound S.threshold
    let nextArms : OperationalArms M B.state B.forest := A.afterMin S.bud S.stage.maxHasMin
    let es := B.state.bucket (2 * i + 1)
    let result := runRecoverableBucket S.odd S.bound S.threshold B nextArms es (fun _ he => he)
    match hout : result.1 with
    | .found B' A' W =>
      have herase : (runCurrentBucket S.odd S.bound S.threshold B es (fun _ he => he)).1 =
          .found B' W := by
        have hh := runRecoverableBucket_erase S.odd S.bound S.threshold B nextArms es (fun _ he => he)
        exact hh.symm.trans (congrArg RecoverableBucketOutcome.erase hout)
      .found i cut S.odd S.bound S.threshold B' A' W es
        (by
          intro e he
          have hh := runCurrentBucket_bucket_mono S.odd S.bound S.threshold B es (fun _ he => he)
            e.1 e.2 (2 * i + 1) he
          rw [herase] at hh
          exact hh)
        (by
          intro p hp hlen
          have hrep : LowerBlossomRepresentation M cut B.state B.forest :=
            scanLevelWithBuds_lower_representation i cut S.state S.forest S.bud
              (by have := S.threshold; omega) S.lower
          obtain ⟨u, v, hbridge, ht, ha⟩ := B.augmenting_bridge_arms S.odd S.bound S.threshold
            hrep p hp hlen
          have hstay := runCurrentBucket_bottom_arms S.odd S.bound S.threshold B es
            (fun _ he => he) u v _ ha
          dsimp only at hstay
          rw [herase] at hstay
          rcases prepareCurrentBucket_complete i cut S.state S.forest S.stage S.bud S.lower
              S.odd S.bound S.threshold u v hbridge ht with hm | hm
          · exact ⟨u, v, hm, hstay⟩
          · exact ⟨v, u, hm, hstay.symm⟩)
    | .exhausted B' A' =>
      have he : (runSearchLevel i cut S.state S.forest S.stage S.bud S.lower
          S.odd S.bound S.threshold).1 = .exhausted B' := by
        have hh := runRecoverableBucket_erase S.odd S.bound S.threshold B nextArms es (fun _ he => he)
        exact hh.symm.trans (congrArg RecoverableBucketOutcome.erase hout)
      have hnext := runSearchLevel_exhausted i cut S.state S.forest S.stage S.bud
        S.lower S.offRoots S.odd S.bound S.threshold B' he
      let next : LevelSearchState M (i + 1) (cut + 2) := {
        state := B'.state, forest := B'.forest,
        stage := hnext.1, bud := B'.bud, lower := hnext.2.1,
        offRoots := hnext.2.2.1, odd := by have := S.odd; omega,
        threshold := by have := S.threshold; omega,
        bound := by simpa only [Nat.add_assoc] using hnext.2.2.2 }
      locateBlockingPhase next A'
termination_by n - i
decreasing_by omega

end
end MaximumMatching.Search

end BlockingPhaseStart
