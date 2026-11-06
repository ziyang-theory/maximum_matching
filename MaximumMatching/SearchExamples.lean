import MaximumMatching.BlockingPhase
import MaximumMatching.CurrentBucket
import MaximumMatching.CurrentBucketStage
import MaximumMatching.DDFSExamples
import MaximumMatching.FoundationExamples
import MaximumMatching.Foundations
import MaximumMatching.MatchingGraphExpansion
import MaximumMatching.PetalPathTransport
import MaximumMatching.ShortestAugmentingSearch

section CurrentBucketExamples

/-! Execute the complete tenacity-three bucket of a triangle. The call must
form a petal, update both current roots, and leave the free boundary unchanged. -/
namespace MaximumMatching.Examples.CurrentBucket
open Search

instance : DecidableRel triangle.Adj := fun u v => inferInstanceAs (Decidable (u ≠ v))

private theorem no_short : ∀ p : AltPath triangleMatching, p.Augmenting → 1 < p.length := by
  intro p hp
  exact False.elim (triangle_no_augmenting ⟨p, hp⟩)

private theorem permitted : AtMostShortestAugmenting triangleMatching 3 := by
  intro p hp
  exact False.elim (triangle_no_augmenting ⟨p, hp⟩)

def firstState : State (Fin 3) := scanLevel triangleMatching 0 (initial triangleMatching)
def secondState : State (Fin 3) := scanLevel triangleMatching 1 firstState

theorem firstStage : StageInvariant triangleMatching 1 firstState := by
  apply searchLevel_stageInvariant triangleMatching 0 [] (initial triangleMatching)
    (initial_stageInvariant triangleMatching)
  · intro v hv
    exact False.elim (List.not_mem_nil hv)
  · intro v hv
    have hh := tenacity_above_one_of_no_short_augmenting no_short v
    rw [hv] at hh
    change 1 < 1 at hh
    omega

theorem secondStage : StageState triangleMatching 2 3 secondState :=
  scanLevel_stageState triangleMatching 1 firstState firstStage

def node : CurrentBucketState triangleMatching 1 1 where
  state := secondState
  forest := uncontractedForest secondState
  stage := secondStage
  bud := uncontractedForest_invariant secondState 2 secondStage.min secondStage.minBound
  represented := ⟨CurrentBridgeRepresentation.ofLowerBlossoms _ rfl no_short (by omega) (by omega)
    (uncontracted_lower_representation_one secondState no_short)⟩

def result : CurrentBucketOutcome triangleMatching 1 1 × List (PetalRecord triangleMatching) :=
  runCurrentBucket rfl permitted rfl node (node.state.bucket 3) (fun _ h => h)

/-- info: true -/
#guard_msgs in
#eval match result.1 with
  | .found _ _ => false
  | .exhausted B =>
    result.2.length == 1 &&
      (List.finRange 3).map B.forest.root == [0, 0, 0] &&
      (List.finRange 3).map B.state.maxLabel == [none, some 2, some 2]

end MaximumMatching.Examples.CurrentBucket

end CurrentBucketExamples

section CurrentBucketCompletionExamples

/-! Regression examples for the completed bucket contracts. The triangle
checks the semantic postconditions of an actual petal; the five-vertex graph
checks repeated same-level contractions through one shared free boundary. -/
namespace MaximumMatching.Examples.CurrentBucketCompletion
open Search
set_option maxRecDepth 4096

private theorem triangle_permitted : AtMostShortestAugmenting triangleMatching 3 := by
  intro p hp
  exact False.elim (triangle_no_augmenting ⟨p, hp⟩)

private theorem triangle_lower : LowerBlossomRepresentation triangleMatching 1
    CurrentBucket.node.state CurrentBucket.node.forest := by
  apply uncontracted_lower_representation_one
  intro p hp
  exact False.elim (triangle_no_augmenting ⟨p, hp⟩)

private theorem triangle_off : MaxLabelsOffRoots CurrentBucket.node.state CurrentBucket.node.forest := by
  intro v _
  exact (scanCandidates_maxLabel _ _ _ v).trans (scanCandidates_maxLabel _ _ _ v)

private theorem triangle_complete (u v : Fin 3) (hb : Bridge triangleMatching u v)
    (ht : MaximumMatching.edgeTenacity triangleMatching u v = some 3) :
    (u, v) ∈ CurrentBucket.node.state.bucket 3 ∨ (v, u) ∈ CurrentBucket.node.state.bucket 3 :=
  scanLevel_stage_bucket_complete triangleMatching 1 CurrentBucket.firstState CurrentBucket.firstStage u v hb ht

/-- The actual executable result is exhausted, not a spurious augmentation. -/
theorem triangle_exhausted :
    CurrentBucket.result.1 = .exhausted CurrentBucket.result.1.state := by
  cases he : CurrentBucket.result.1 with
  | exhausted B => rfl
  | found B W =>
    obtain ⟨p, hp, _⟩ := W.shortest_augmenting rfl triangle_permitted rfl
    exact False.elim (triangle_no_augmenting ⟨p, hp⟩)

/-- MAX coverage is obtained from the complete bucket theorem. -/
example : ∀ v, tenacity triangleMatching v = some 3 →
    CurrentBucket.result.1.state.state.maxLabel v = maxlevel triangleMatching v :=
  runCurrentBucket_exhausted_maxComplete rfl triangle_permitted rfl CurrentBucket.node
    triangle_lower (CurrentBucket.node.state.bucket 3) (fun _ h => h) triangle_complete
    _ triangle_exhausted

/-- Exhaustion raises the augmentation lower bound to five. -/
example : AtMostShortestAugmenting triangleMatching 5 :=
  runCurrentBucket_exhausted_next_lower_bound rfl triangle_permitted rfl CurrentBucket.node
    triangle_lower triangle_off (CurrentBucket.node.state.bucket 3) (fun _ h => h) triangle_complete
    _ triangle_exhausted

/-- The returned forest represents the actual tenacity-three blossoms. -/
example : LowerBlossomRepresentation triangleMatching 3
    CurrentBucket.result.1.state.state CurrentBucket.result.1.state.forest :=
  runCurrentBucket_exhausted_lower_representation rfl triangle_permitted rfl CurrentBucket.node
    triangle_lower triangle_off (CurrentBucket.node.state.bucket 3) (fun _ h => h) triangle_complete
    _ triangle_exhausted

/-- Two triangles, 0--1--2--0 and 0--3--4--0, share their free boundary. -/
def twoTriangles : Graph (Fin 5) where
  Adj u v := u ≠ v ∧ (u = 0 ∨ v = 0 ∨ (u.val ≤ 2 ↔ v.val ≤ 2))
  symm := by
    intro u v h
    exact ⟨h.1.symm, h.2.elim (fun hu => Or.inr (Or.inl hu))
      (fun hv => hv.elim Or.inl (fun hh => Or.inr (Or.inr hh.symm)))⟩
  loopless := fun _ h => h.1 rfl

instance : DecidableRel twoTriangles.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ≠ _ ∧ (_ = 0 ∨ _ = 0 ∨ (_ ≤ 2 ↔ _ ≤ 2))))

def twoTrianglesMatching : Matching twoTriangles where
  mate v := if v = 0 then none else if v = 1 then some 2 else if v = 2 then some 1
    else if v = 3 then some 4 else some 3
  symm := by decide
  edge := by dsimp [twoTriangles]; decide

private theorem twoTriangles_free (v : Fin 5) : twoTrianglesMatching.Free v ↔ v = 0 := by
  unfold Matching.Free
  revert v
  decide

private theorem twoTriangles_no_augmenting :
    ∀ p : AltPath twoTrianglesMatching, p.Augmenting → False := by
  intro p hp
  have hf := (twoTriangles_free p.first).1 p.start_free
  have hl := (twoTriangles_free p.last).1 hp.2
  exact p.augmenting_distinct hp (hf.trans hl.symm)

private theorem twoTriangles_no_short :
    ∀ p : AltPath twoTrianglesMatching, p.Augmenting → 1 < p.length :=
  fun p hp => False.elim (twoTriangles_no_augmenting p hp)

private theorem twoTriangles_permitted : AtMostShortestAugmenting twoTrianglesMatching 3 :=
  fun p hp => False.elim (twoTriangles_no_augmenting p hp)

def twoFirst : State (Fin 5) := scanLevel twoTrianglesMatching 0 (initial twoTrianglesMatching)
def twoSecond : State (Fin 5) := scanLevel twoTrianglesMatching 1 twoFirst

private theorem twoFirstStage : StageInvariant twoTrianglesMatching 1 twoFirst :=
  first_scan_stageInvariant twoTriangles_no_short

private theorem twoSecondStage : StageState twoTrianglesMatching 2 3 twoSecond :=
  scanLevel_stageState twoTrianglesMatching 1 twoFirst twoFirstStage

def twoNode : CurrentBucketState twoTrianglesMatching 1 1 where
  state := twoSecond
  forest := uncontractedForest twoSecond
  stage := twoSecondStage
  bud := uncontractedForest_invariant twoSecond 2 twoSecondStage.min twoSecondStage.minBound
  represented := ⟨CurrentBridgeRepresentation.ofLowerBlossoms _ rfl twoTriangles_no_short
    (by omega) (by omega) (uncontracted_lower_representation_one twoSecond twoTriangles_no_short)⟩

def twoResult : CurrentBucketOutcome twoTrianglesMatching 1 1 × List (PetalRecord twoTrianglesMatching) :=
  runCurrentBucket rfl twoTriangles_permitted rfl twoNode (twoNode.state.bucket 3) (fun _ h => h)

/-- info: true -/
#guard_msgs in
#eval match twoResult.1 with
  | .found _ _ => false
  | .exhausted B =>
    twoResult.2.length == 2 &&
      (List.finRange 5).map B.forest.root == [0, 0, 0, 0, 0] &&
      (List.finRange 5).map B.state.maxLabel == [none, some 2, some 2, some 2, some 2]

private theorem twoResult_exhausted : twoResult.1 = .exhausted twoResult.1.state := by
  cases he : twoResult.1 with
  | exhausted B => rfl
  | found B W =>
    obtain ⟨p, hp, _⟩ := W.shortest_augmenting rfl twoTriangles_permitted rfl
    exact False.elim (twoTriangles_no_augmenting p hp)

/-- Both actual contractions preserve the canonical class representation. -/
example : LowerBlossomRepresentation twoTrianglesMatching 3 twoResult.1.state.state twoResult.1.state.forest := by
  apply runCurrentBucket_exhausted_lower_representation rfl twoTriangles_permitted rfl twoNode
    (uncontracted_lower_representation_one twoSecond twoTriangles_no_short) ?_
    (twoNode.state.bucket 3) (fun _ h => h) ?_ _ twoResult_exhausted
  · intro v _
    exact (scanCandidates_maxLabel _ _ _ v).trans (scanCandidates_maxLabel _ _ _ v)
  · intro u v hb ht
    exact scanLevel_stage_bucket_complete twoTrianglesMatching 1 twoFirst twoFirstStage u v hb ht

end MaximumMatching.Examples.CurrentBucketCompletion

end CurrentBucketCompletionExamples

section LevelSearchExamples

/-! Execute the complete level search on boundary cases, multiple same-level
petals, and shortest augmentations at lengths one, three, and five. These are
runtime regressions alongside the universal kernel-checked search theorem. -/
namespace MaximumMatching.Examples.LevelSearch
open Search
set_option maxRecDepth 4096

instance : DecidableRel lineFour.Adj := fun u v =>
  inferInstanceAs (Decidable (u.val + 1 = v.val ∨ v.val + 1 = u.val))

private def reportedLength {n : Nat} {G : Graph (Fin n)} {M : Matching G} :
    LevelSearchOutcome M → Option Nat
  | .maximum _ => none
  | .freeEdge _ _ _ => some 1
  | .found i _ _ _ _ _ _ => some (2 * i + 1)

/-- info: (none, true, 0) -/
#guard_msgs in
#eval (reportedLength (findAugmenting triangleMatching).1,
  Search.isMaximum triangleMatching, (findAugmenting triangleMatching).2.length)

/- The five-vertex example actually executes two successive petal events
before the finite stopping test certifies maximum cardinality. -/
/-- info: (none, true, 2) -/
#guard_msgs in
#eval (reportedLength (findAugmenting CurrentBucketCompletion.twoTrianglesMatching).1,
  Search.isMaximum CurrentBucketCompletion.twoTrianglesMatching,
  (findAugmenting CurrentBucketCompletion.twoTrianglesMatching).2.length)

/- The middle matching edge hides a length-three augmentation from the
free-edge scan; the higher-level search returns the actual DDFS certificate. -/
/-- info: (some 3, false, 0) -/
#guard_msgs in
#eval (reportedLength (findAugmenting middleMatching).1,
  Search.isMaximum middleMatching, (findAugmenting middleMatching).2.length)

/- An empty matching takes the executable free-edge branch. -/
/-- info: (some 1, false) -/
#guard_msgs in
#eval (reportedLength (findAugmenting (Matching.empty lineFour)).1,
  Search.isMaximum (Matching.empty lineFour))

/- A perfect matching stops without constructing a false augmenting path. -/
/-- info: (none, true) -/
#guard_msgs in
#eval (reportedLength (findAugmenting lineAugmented).1, Search.isMaximum lineAugmented)

/-- A six-vertex path with matching edges 1--2 and 3--4. -/
def lineSix : Graph (Fin 6) where
  Adj u v := u.val + 1 = v.val ∨ v.val + 1 = u.val
  symm := fun h => h.elim Or.inr Or.inl
  loopless := by intro v h; omega

instance : DecidableRel lineSix.Adj := fun u v =>
  inferInstanceAs (Decidable (u.val + 1 = v.val ∨ v.val + 1 = u.val))

def lineSixMatching : Matching lineSix where
  mate v := if v = 1 then some 2 else if v = 2 then some 1
    else if v = 3 then some 4 else if v = 4 then some 3 else none
  symm := by decide
  edge := by dsimp [lineSix]; decide

/- The search must exhaust the length-three bucket and restore the next
stage before discovering the shortest augmentation at length five. -/
/-- info: (some 5, false, 0) -/
#guard_msgs in
#eval (reportedLength (findAugmenting lineSixMatching).1,
  Search.isMaximum lineSixMatching, (findAugmenting lineSixMatching).2.length)

/-- A length-five augmentation passes through a tenacity-three triangle.
Its middle matched edges are 1--2 and 3--4; vertices 0 and 5 are free. -/
def triangleTail : Graph (Fin 6) where
  Adj u v := u ≠ v ∧ ((u.val ≤ 2 ∧ v.val ≤ 2) ∨ u.val + 1 = v.val ∨ v.val + 1 = u.val)
  symm := by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  loopless := fun _ h => h.1 rfl

instance : DecidableRel triangleTail.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ ((u.val ≤ 2 ∧ v.val ≤ 2) ∨ u.val + 1 = v.val ∨ v.val + 1 = u.val)))

def triangleTailMatching : Matching triangleTail where
  mate v := if v = 1 then some 2 else if v = 2 then some 1
    else if v = 3 then some 4 else if v = 4 then some 3 else none
  symm := by decide
  edge := by dsimp [triangleTail]; decide

/- This case requires a petal contraction at length three before a raw
shortest-path certificate is found at length five. -/
/-- info: (some 5, false, 1) -/
#guard_msgs in
#eval (reportedLength (findAugmenting triangleTailMatching).1,
  Search.isMaximum triangleTailMatching, (findAugmenting triangleTailMatching).2.length)

/-- The zero-vertex boundary exercises the finite stopping test directly. -/
def emptyGraph : Graph (Fin 0) where
  Adj _ _ := False
  symm := False.elim
  loopless := fun _ => id

instance : DecidableRel emptyGraph.Adj := fun _ _ => isFalse id

/-- info: (none, true, 0) -/
#guard_msgs in
#eval (reportedLength (findAugmenting (Matching.empty emptyGraph)).1,
  Search.isMaximum (Matching.empty emptyGraph),
  (findAugmenting (Matching.empty emptyGraph)).2.length)

end MaximumMatching.Examples.LevelSearch

end LevelSearchExamples

section MatchingPathRecoveryExamples

/-! Computational checks for recovery from actual DDFS outputs and petal
records, including an abandoned search branch and a selected bottleneck. -/
namespace MaximumMatching.DDFS.RecoveryExamples

def vertices {n : Nat} {H : LayeredGraph (Fin n)} (p : Path H) : List Nat :=
  (List.finRange (p.length + 1)).map (fun j => (p.vertex j).val)

def linkages {n : Nat} {H : LayeredGraph (Fin n)} {r g : Fin n}
    (out : Machine.FullOutput H r g) : List (Nat × List Nat × List Nat) :=
  match out with
  | .disjoint .. => []
  | .bottleneck _b _ trees _ region =>
    (List.finRange n).filterMap fun v =>
      match hc : trees.color v with
      | none => none
      | some _ =>
        have hs := (trees.domain v).1 ⟨_, hc⟩
        let pq := trees.recoverLinkage v hs.1
          (onRootTo_level_gt ((region v).1 hs.1) hs.2)
        some (v.val, vertices pq.val.1, vertices pq.val.2)

/-- info: true -/
#guard_msgs in
#eval linkages (Machine.executeFull ExecutableExamples.fixture_reaches 0 1) ==
  [(0, [0], [1, 2, 5]), (1, [1], [0, 4, 5]), (2, [1, 2], [0, 4, 5]),
    (3, [0, 3], [1, 2, 5]), (4, [0, 4], [1, 2, 5])]

end MaximumMatching.DDFS.RecoveryExamples

namespace MaximumMatching.Examples.CurrentBucket
open Search DDFS.RecoveryExamples

def recoveredTails : List (List (Nat × List Nat)) :=
  result.2.map fun R => R.trees.vertices.attach.map fun v =>
    (v.val.val, vertices (R.recoverTail v.val ((R.trees.mem_vertices v.val).1 v.property)).val)

/-- info: true -/
#guard_msgs in
#eval recoveredTails == [[(0, [0]), (1, [1, 0]), (2, [2, 0])]]

end MaximumMatching.Examples.CurrentBucket

end MatchingPathRecoveryExamples

section ShortestAugmentingExamples

/-! Runtime regression tests for computed matching-path recovery, including a
path that traverses an earlier petal. Successful results execute a real flip;
no alternating path is supplied as a recovery witness by these examples. -/
namespace MaximumMatching.Examples.ShortestAugmenting
open Search
set_option maxRecDepth 4096

private def vertices {n : Nat} {G : Graph (Fin n)} {M : Matching G}
    (p : AltPath M) : List Nat :=
  (List.finRange (p.length + 1)).map (fun i => (p.vertex i).val)

/- The recovered five-edge path passes through the triangle contracted at
length three. Augmentation executes the recovered data and gains one edge. -/
/-- info: true -/
#guard_msgs in
#eval
  let result := findShortestAugmenting LevelSearch.triangleTailMatching
  match result.1 with
  | .maximum _ => false
  | .found p hp _ =>
    result.2.length == 1 && p.length == 5 &&
      (vertices p == [0, 1, 2, 3, 4, 5] || vertices p == [5, 4, 3, 2, 1, 0]) &&
      (p.augment hp).cardinality == 3

/- This path is found after an empty length-three bucket advances the actual
MIN/MAX state to length five. -/
/-- info: true -/
#guard_msgs in
#eval
  let result := findShortestAugmenting LevelSearch.lineSixMatching
  match result.1 with
  | .maximum _ => false
  | .found p hp _ =>
    result.2.length == 0 && p.length == 5 &&
      (vertices p == [0, 1, 2, 3, 4, 5] || vertices p == [5, 4, 3, 2, 1, 0]) &&
      (p.augment hp).cardinality == 3

/-- info: true -/
#guard_msgs in
#eval
  match (findShortestAugmenting middleMatching).1 with
  | .maximum _ => false
  | .found p hp _ =>
    p.length == 3 && (vertices p == [0, 1, 2, 3] || vertices p == [3, 2, 1, 0]) &&
      (p.augment hp).cardinality == 2

/-- info: true -/
#guard_msgs in
#eval
  match (findShortestAugmenting (Matching.empty lineFour)).1 with
  | .maximum _ => false
  | .found p hp _ => p.length == 1 && (p.augment hp).cardinality == 1

/- Two actual same-level petals are processed without manufacturing a path
between copies of their shared free boundary. -/
/-- info: true -/
#guard_msgs in
#eval
  let result := findShortestAugmenting CurrentBucketCompletion.twoTrianglesMatching
  match result.1 with
  | .maximum _ => result.2.length == 2
  | .found _ _ _ => false

/-- info: false -/
#guard_msgs in
#eval (findShortestAugmenting lineAugmented).1.hasPath

/-- info: false -/
#guard_msgs in
#eval (findShortestAugmenting (Matching.empty LevelSearch.emptyGraph)).1.hasPath

end MaximumMatching.Examples.ShortestAugmenting

end ShortestAugmentingExamples

section BlockingPhaseGraphs

/-! A disconnected blocking-phase regression fixture. Two independent
length-three augmentations coexist with a triangle and a matched branch
whose predecessor chain is lost when the first path is removed. -/
namespace MaximumMatching.Examples.BlockingPhase

/-- Triangle 0--1--2, lines 3--4--5--6 and 7--8--9--10, and branch
7--11--12. The explicit finite edge list also fixes executable adjacency. -/
def forwardEdges : List (Fin 13 × Fin 13) :=
  [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (5, 6),
    (7, 8), (8, 9), (9, 10), (7, 11), (11, 12)]

def graph : Graph (Fin 13) where
  Adj u v := (u, v) ∈ forwardEdges ∨ (v, u) ∈ forwardEdges
  symm := fun h => h.elim Or.inr Or.inl
  loopless := by decide

instance : DecidableRel graph.Adj := fun u v =>
  inferInstanceAs (Decidable ((u, v) ∈ forwardEdges ∨ (v, u) ∈ forwardEdges))

def matching : Matching graph where
  mate v := if v = 1 then some 2 else if v = 2 then some 1
    else if v = 4 then some 5 else if v = 5 then some 4
    else if v = 8 then some 9 else if v = 9 then some 8
    else if v = 11 then some 12 else if v = 12 then some 11 else none
  symm := by decide
  edge := by dsimp [graph]; decide

end MaximumMatching.Examples.BlockingPhase

end BlockingPhaseGraphs

section BlockingPhaseExamples

/-! Runtime regressions for complete blocking phases. These examples execute
MIN, live DDFS, computed expansion, recursive removal, and matching flips.
They supply no augmentation or bottleneck certificate to the solver. -/
namespace MaximumMatching.Examples.BlockingPhase
open Search
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private def vertices {n : Nat} {G : Graph (Fin n)} {M : Matching G}
    (p : AltPath M) : List Nat :=
  (List.finRange (p.length + 1)).map (fun i => (p.vertex i).val)

/- Both shortest paths are collected during one phase and their actual
flips increase cardinality by two. The vertex sequences fix the scan order. -/
/-- info: (2, [[10, 9, 8, 7], [6, 5, 4, 3]], 4, 6) -/
#guard_msgs in
#eval
  let f := blockingPhase matching
  (f.count, (List.finRange f.count).map (fun j => vertices (f.path j)),
    matching.cardinality, f.run.cardinality)

/- The triangle is still uncontracted at the first augmentation. Continued
live DDFS contracts it afterwards. The matched branch 11--12 is initially
live and is recursively pruned after its only predecessor boundary is erased. -/
/-- info: [1, 2, 0, 0, 1, 1, 0, 0] -/
#guard_msgs in
#eval
  let M := matching
  if hz : (freeEdgePhase M).count = 0 then
    let hn := freeEdgePhase_empty_no_short M hz
    match locateBlockingPhase (firstHigherState M hn) (firstHigherArms M hn) with
    | .maximum _ => ([] : List Nat)
    | .found _ _ hc ht hstageTen B A W es hqueued _ =>
      let result := resumeBlockingPhase hc ht hstageTen B A W es hqueued
      [B.forest.root 1, B.forest.root 2,
        result.state.B.forest.root 1, result.state.B.forest.root 2,
        if 11 ∈ ActiveSearchState.initialLive B then 1 else 0,
        if 12 ∈ ActiveSearchState.initialLive B then 1 else 0,
        if 11 ∈ result.state.live then 1 else 0,
        if 12 ∈ result.state.live then 1 else 0]
  else []

/- This phase expands an earlier length-three petal while recovering the
length-five augmentation. It then executes the recovered matching flip. -/
/-- info: true -/
#guard_msgs in
#eval
  let f := blockingPhase LevelSearch.triangleTailMatching
  f.count == 1 &&
    (List.finRange f.count).all (fun j => (f.path j).length == 5 &&
      (vertices (f.path j) == [0, 1, 2, 3, 4, 5] ||
        vertices (f.path j) == [5, 4, 3, 2, 1, 0])) &&
    f.run.cardinality == 3

/- Empty, perfect, and blossom-only inputs must return no false augmentation. -/
/-- info: true -/
#guard_msgs in
#eval
  (blockingPhase (Matching.empty LevelSearch.emptyGraph)).count == 0 &&
    (blockingPhase lineAugmented).count == 0 &&
    (blockingPhase triangleMatching).count == 0 &&
    (blockingPhase CurrentBucketCompletion.twoTrianglesMatching).count == 0

/- The concrete outer driver stops after this single positive phase, with
the exact number of performed augmentations and matching-cardinality gain. -/
/-- info: (6, 1, 2) -/
#guard_msgs in
#eval
  let result := runBlockingPhases matching
  (result.matching.cardinality, result.positivePhases, result.augmentations)

/- The total solver starts from the empty matching, including zero vertices. -/
/-- info: true -/
#guard_msgs in
#eval
  (maximumMatching graph).cardinality == 6 &&
    (maximumMatching lineFour).cardinality == 2 &&
    (maximumMatching LevelSearch.triangleTail).cardinality == 3 &&
    (maximumMatching LevelSearch.emptyGraph).cardinality == 0

end MaximumMatching.Examples.BlockingPhase

end BlockingPhaseExamples
