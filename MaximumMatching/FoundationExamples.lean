import MaximumMatching.BudForest
import MaximumMatching.Foundations
import MaximumMatching.Levels
import MaximumMatching.MatchingSearchGraph
import MaximumMatching.MaxBridgeRefresh
import MaximumMatching.MinScan

section Examples

/-! Small kernel-checked boundary examples. These do not replace universal proofs. -/
namespace MaximumMatching.Examples

/-- The triangle with one matching edge, 1--2, and free vertex 0. -/
def triangle : Graph (Fin 3) where
  Adj u v := u ≠ v
  symm := Ne.symm
  loopless := by intro v h; exact h rfl

def triangleMatching : Matching triangle where
  mate v := if v = 0 then none else if v = 1 then some 2 else some 1
  symm := by decide
  edge := by dsimp [triangle]; decide

theorem triangle_free (v : Fin 3) : triangleMatching.Free v ↔ v = 0 := by
  unfold Matching.Free
  revert v
  decide

def triangleEvenPath : AltPath triangleMatching where
  length := 2
  vertex := fun i => i
  injective := by intro i j h; exact h
  adjacent := by dsimp [triangle]; decide
  start_free := rfl
  alternating := by decide

def triangleOddPath : AltPath triangleMatching where
  length := 1
  vertex := fun i => if i = 0 then 0 else 2
  injective := by decide
  adjacent := by dsimp [triangle]; decide
  start_free := rfl
  alternating := by decide

theorem triangle_evenlevel : evenlevel triangleMatching 2 = some 2 := by
  apply (level_eq_some_iff _ _ _ _).2
  refine ⟨⟨triangleEvenPath, rfl, rfl, rfl⟩, ?_⟩
  rintro k ⟨p, hend, hlen, hpar⟩
  by_cases hz : k = 0
  · have hi : (⟨0, by omega⟩ : Fin (p.length + 1)) = ⟨p.length, by omega⟩ :=
      Fin.ext (by omega)
    have hf := p.start_free
    rw [hi] at hf
    change triangleMatching.Free p.last at hf
    rw [hend] at hf
    have : (2 : Fin 3) = 0 := (triangle_free 2).1 hf
    contradiction
  · omega

theorem triangle_oddlevel : oddlevel triangleMatching 2 = some 1 := by
  apply (level_eq_some_iff _ _ _ _).2
  refine ⟨⟨triangleOddPath, rfl, rfl, rfl⟩, ?_⟩
  rintro k ⟨_, _, _, hpar⟩
  omega

theorem triangle_no_augmenting : ¬ ∃ p : AltPath triangleMatching, p.Augmenting := by
  rintro ⟨p, hp⟩
  have hf : p.first = 0 := (triangle_free p.first).1 p.start_free
  have hl : p.last = 0 := (triangle_free p.last).1 hp.2
  exact p.augmenting_distinct hp (hf.trans hl.symm)

theorem triangle_oddlevel_free_infinite : oddlevel triangleMatching 0 = none := by
  apply (level_eq_none_iff _ _ _).2
  rintro ⟨k, p, hend, hlen, hpar⟩
  apply triangle_no_augmenting
  refine ⟨p, ?_, ?_⟩
  · omega
  · rw [hend]
    exact (triangle_free 0).2 rfl

/-- The alternating walk 0,1,2,0 has free endpoints but repeats its first vertex.
Treating such a walk as an augmenting *path* would give a false positive. -/
def triangleWalk (i : Fin 4) : Fin 3 := if h : i.val = 3 then 0 else ⟨i.val, by omega⟩

theorem triangleWalk_edges : ∀ i : Fin 3,
    triangle.Adj (triangleWalk ⟨i.val, by omega⟩)
      (triangleWalk ⟨i.val + 1, by omega⟩) := by dsimp [triangle]; decide

theorem triangleWalk_alternates : ∀ i : Fin 3,
    (triangleMatching.mate (triangleWalk ⟨i.val, by omega⟩) =
      some (triangleWalk ⟨i.val + 1, by omega⟩)) ↔ i.val % 2 = 1 := by decide

theorem triangleWalk_not_simple :
    ¬ (∀ i j, triangleWalk i = triangleWalk j → i = j) := by
  intro h
  have he := h 0 3 (by decide)
  contradiction

/-- A four-vertex path with its middle edge matched. -/
def lineFour : Graph (Fin 4) where
  Adj u v := u.val + 1 = v.val ∨ v.val + 1 = u.val
  symm := fun h => h.elim Or.inr Or.inl
  loopless := by intro v h; omega

def middleMatching : Matching lineFour where
  mate v := if v = 1 then some 2 else if v = 2 then some 1 else none
  symm := by decide
  edge := by dsimp [lineFour]; decide

def linePath : AltPath middleMatching where
  length := 3
  vertex := fun i => i
  injective := by intro i j h; exact h
  adjacent := by dsimp [lineFour]; decide
  start_free := rfl
  alternating := by decide

theorem linePath_augmenting : linePath.Augmenting := ⟨rfl, rfl⟩

def lineAugmented : Matching lineFour := linePath.augment linePath_augmenting

theorem lineAugmented_mates :
    (List.finRange 4).map lineAugmented.mate = [some 1, some 0, some 3, some 2] := by decide

theorem lineAugmented_size : lineAugmented.cardinality = 2 := by decide

/-- Two free roots reach vertex 2 through unmatched edges at search level zero. -/
def completeFour : Graph (Fin 4) where
  Adj u v := u ≠ v
  symm := Ne.symm
  loopless := by intro v h; exact h rfl

instance : DecidableRel completeFour.Adj := fun u v => inferInstanceAs (Decidable (u ≠ v))

def tieMatching : Matching completeFour where
  mate v := if v = 2 then some 3 else if v = 3 then some 2 else none
  symm := by decide
  edge := by dsimp [completeFour]; decide

def afterFirstScan : Search.State (Fin 4) :=
  Search.scanCandidate tieMatching 0 0 2 (Search.initial tieMatching)

theorem min_keeps_tied_predecessors :
    (Search.scanCandidate tieMatching 0 1 2 afterFirstScan).predecessors 2 = [1, 0] := by decide

def budChain : BudForest (Fin 4) where
  parent v := ⟨v.val - 1, by omega⟩
  rank := Fin.val
  decreases := by
    intro v h
    have hv : v.val ≠ 0 := by
      intro he
      apply h
      exact Fin.ext (by simp [he])
    dsimp
    omega

theorem budChain_root : budChain.root 3 = 0 := by
  simp [BudForest.root, budChain]
  decide

theorem compressed_chain_root : (budChain.compress 3).root 3 = 0 := by
  rw [BudForest.compress_root]
  exact budChain_root

end MaximumMatching.Examples

end Examples

section MinMaxExamples

/-! Concrete MIN/MAX state transitions on the four-vertex augmenting path.
The examples exercise complete enumeration, a matched bridge, and repeated
support-list assignments; the general semantic theorems remain in the imported
modules. -/
namespace MaximumMatching.Examples.MinMax
open Search

instance : DecidableRel lineFour.Adj := fun u v =>
  inferInstanceAs (Decidable (u.val + 1 = v.val ∨ v.val + 1 = u.val))

def firstMin : State (Fin 4) := scanLevel middleMatching 0 (initial middleMatching)
def secondMin : State (Fin 4) := scanLevel middleMatching 1 firstMin

theorem firstMin_correct : MinInvariant middleMatching 1 firstMin :=
  (initial_scanLevel_complete middleMatching).1

theorem firstMin_labels : (List.finRange 4).map firstMin.minLabel =
    [some 0, some 1, some 1, some 0] := by decide

theorem firstMin_predecessors : (List.finRange 4).map firstMin.predecessors =
    [[], [0], [3], []] := by decide

/-- MIN at the next odd level scans the middle matching edge once and puts it
in the tenacity-three bucket, retaining the predecessors from the first level. -/
theorem secondMin_bridge : secondMin.bridges = [(1, 2)] ∧
    secondMin.bucket 3 = [(1, 2)] ∧
    (List.finRange 4).map secondMin.predecessors = [[], [0], [3], []] := by decide

/-- The same bridge can be reconsidered after MAX without changing semantic
labels. Duplicate queue entries are permitted by this operational interface. -/
theorem refresh_middle_bridge :
    (1, 2) ∈ (refreshIncident middleMatching 1 secondMin).bucket 3 := by decide

/-- Repeated assignments arising from overlapping support lists are harmless. -/
theorem repeated_max_assignments :
    (List.finRange 4).map (assignMaxList 3 [1, 1, 2] secondMin).maxLabel =
      [none, some 2, some 2, none] := by decide

end MaximumMatching.Examples.MinMax


namespace MaximumMatching.Examples.DeferredBridge
open Search
set_option maxRecDepth 8000
set_option maxHeartbeats 800000

/-- Two matched triangles with an unmatched edge joining their inner vertices.
The cross edge's tenacity becomes known only after both MAX assignments. -/
def graph : Graph (Fin 6) where
  Adj u v := (u.val / 3 = v.val / 3 ∧ u ≠ v) ∨ (u = 2 ∧ v = 5) ∨ (u = 5 ∧ v = 2)
  symm := by decide
  loopless := by decide

instance : DecidableRel graph.Adj := fun u v => inferInstanceAs
  (Decidable ((u.val / 3 = v.val / 3 ∧ u ≠ v) ∨ (u = 2 ∧ v = 5) ∨ (u = 5 ∧ v = 2)))

def matching : Matching graph where
  mate v := if v = 1 then some 2 else if v = 2 then some 1 else
    if v = 4 then some 5 else if v = 5 then some 4 else none
  symm := by decide
  edge := by dsimp [graph]; decide

def beforeMax : State (Fin 6) :=
  scanLevel matching 1 (scanLevel matching 0 (initial matching))

def afterLeftMax : State (Fin 6) := maxProcessVertex matching 1 2 beforeMax
def afterRightMax : State (Fin 6) := maxProcessVertex matching 1 5 afterLeftMax

theorem cross_edge_not_previously_registered :
    (2, 5) ∉ beforeMax.bridges ∧ (5, 2) ∉ beforeMax.bridges ∧
    (2, 5) ∉ afterLeftMax.bridges ∧ (5, 2) ∉ afterLeftMax.bridges := by decide

theorem cross_edge_initially_unknown : Search.edgeTenacity matching beforeMax 2 5 = none ∧
    Search.edgeTenacity matching afterLeftMax 2 5 = none := by decide

/-- The second actual inner-vertex MAX step discovers and registers the
previously unregistered unmatched bridge before MIN reaches evenlevel two. -/
theorem max_registers_deferred_bridge :
    (2, 5) ∈ afterRightMax.bridges ∧ (2, 5) ∈ afterRightMax.bucket 5 ∧
    Search.edgeTenacity matching afterRightMax 2 5 = some 5 ∧
    seen afterRightMax 2 5 = false := by decide

end MaximumMatching.Examples.DeferredBridge

end MinMaxExamples

section MatchingSearchGraphExamples

/-! Kernel-checked execution of the matching-derived predecessor graph. -/
namespace MaximumMatching.Examples.MatchingSearch
open Search

theorem firstMin_invariant : BudGraphInvariant middleMatching 1 MinMax.firstMin
    (uncontractedForest MinMax.firstMin) := by
  apply uncontractedForest_invariant _ _ MinMax.firstMin_correct
  exact scanCandidates_minLabelsBound _ _ 0
    (fun v k hk => Nat.le_trans (initial_minLabelsBound middleMatching v k hk) (by omega))

def firstGraph : DDFS.LayeredGraph (Fin 4) :=
  predecessorGraph MinMax.firstMin (uncontractedForest MinMax.firstMin) firstMin_invariant

instance : DecidableRel firstGraph.Edge :=
  inferInstanceAs (DecidableRel (predecessorGraph _ _ firstMin_invariant).Edge)

theorem firstGraph_layers : (List.finRange 4).map firstGraph.level = [0, 1, 1, 0] := by decide

theorem firstGraph_edges : ∀ u v : Fin 4,
    firstGraph.Edge u v ↔ (u = 1 ∧ v = 0) ∨ (u = 2 ∧ v = 3) := by
  change ∀ u v : Fin 4, ((MinMax.firstMin.minLabel u).isSome = true ∧
    v ∈ (MinMax.firstMin.predecessors u).map (uncontractedForest MinMax.firstMin).root) ↔ _
  have hr : (uncontractedForest MinMax.firstMin).root = id :=
    funext fun v => (uncontractedForest MinMax.firstMin).root_of_fixed v rfl
  rw [hr]
  decide

/- The graph is computed from the actual first MIN pass, including both
predecessor branches of the matched-edge bridge. -/
/-- info: true -/
#guard_msgs in
#eval (allCandidates 4).filter (fun e => decide (firstGraph.Edge e.1 e.2)) == [(1, 0), (2, 3)]

/-- Initially an unmatched-search label may still be unknown at a matched
vertex. Its artificial layer-zero representation never asserts it is free. -/
theorem inactive_is_not_free :
    (predecessorGraph (initial middleMatching) (uncontractedForest (initial middleMatching))
      (initial_budGraphInvariant middleMatching)).level 1 = 0 ∧
      ¬ middleMatching.Free 1 ∧
      ∀ w, ¬ budEdge (initial middleMatching) (uncontractedForest (initial middleMatching)) 1 w := by
  refine ⟨by decide, ?_, ?_⟩
  · change ¬ middleMatching.mate 1 = none
    decide
  · intro w he
    have hz : (initial middleMatching).minLabel 1 = none := by decide
    have hsome := he.1
    simp only [hz, Option.isSome_none, Bool.false_eq_true] at hsome

end MaximumMatching.Examples.MatchingSearch

end MatchingSearchGraphExamples
