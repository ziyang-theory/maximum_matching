import MaximumMatching.Basic

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
