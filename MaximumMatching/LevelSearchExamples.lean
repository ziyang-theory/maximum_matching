import MaximumMatching.LevelSearch
import MaximumMatching.CurrentBucketCompletionExamples

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
