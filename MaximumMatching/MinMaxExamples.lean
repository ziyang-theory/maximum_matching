import MaximumMatching.MaxBridgeRefresh
import MaximumMatching.Examples

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
