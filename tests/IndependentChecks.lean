import MaximumMatching.BlockingPhase

/-! Independent exhaustive runtime checks for every simple graph on at most five
vertices. The oracle recursively considers leaving a vertex free or pairing it
with each remaining neighbor; it does not use the solver's correctness theorem,
alternating paths, or blocking phases. These finite tests supplement the proofs.

Run with `lake env lean tests/IndependentChecks.lean` after `lake build`.
-/
namespace MaximumMatching.IndependentChecks

/-- Upper-triangular bit order: (0,1), (0,2), (1,2), (0,3), ... . -/
private def pairIndex (a b : Nat) : Nat :=
  min a b + max a b * (max a b - 1) / 2

private def graph (n mask : Nat) : Graph (Fin n) where
  Adj u v := u ≠ v ∧ mask.testBit (pairIndex u.val v.val) = true
  symm := by
    intro u v h
    exact ⟨Ne.symm h.1, by simpa only [pairIndex, Nat.min_comm, Nat.max_comm] using h.2⟩
  loopless := by simp

private instance (n mask : Nat) : DecidableRel (graph n mask).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Exhaust all choices to leave the first remaining vertex free or pair it.
Fuel equal to the original vertex count suffices: every call removes its head,
and a pairing also removes the chosen partner. -/
private def optimum {n : Nat} (G : Graph (Fin n)) [DecidableRel G.Adj] :
    Nat → List (Fin n) → Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | k + 1, u :: rest =>
    rest.foldl (fun best v =>
      if G.Adj u v then max best (1 + optimum G k (rest.filter (· != v))) else best)
      (optimum G k rest)

/-- A failure records vertex count, graph mask, returned edge count, oracle
optimum, and whether symmetry, adjacency, and cardinality consistency passed. -/
private abbrev Failure := Nat × Nat × Nat × Nat × Bool

private def checkSize (n : Nat) : Nat × List Failure :=
  (List.range (2 ^ (n * (n - 1) / 2))).foldl (fun (count, failures) mask =>
    let G := graph n mask
    let M := Search.maximumMatching G
    let vertices := List.finRange n
    let edgeCount := vertices.foldl (fun count u =>
      match M.mate u with
      | none => count
      | some v => count + if u.val < v.val then 1 else 0) 0
    let valid := vertices.all (fun u =>
      match M.mate u with
      | none => true
      | some v => decide (G.Adj u v) && (M.mate v == some u)) &&
      (M.cardinality == edgeCount)
    let expected := optimum G n vertices
    (count + 1, if valid && edgeCount == expected then failures
      else (n, mask, edgeCount, expected, valid) :: failures)) (0, [])

private def checkAll : Nat × List Failure :=
  (List.range 6).foldl (fun (count, failures) n =>
    let result := checkSize n
    (count + result.1, failures ++ result.2)) (0, [])

/- 1 + 1 + 2 + 8 + 64 + 1024 = 1100 labeled simple graphs, with no failures. -/
/-- info: (1100, []) -/
#guard_msgs in
#eval checkAll

end MaximumMatching.IndependentChecks
