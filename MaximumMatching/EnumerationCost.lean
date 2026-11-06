import MaximumMatching.MinComplete

/-! Exact size of the concrete MIN candidate enumeration. This counts
candidate pairs, not machine instructions or only graph edges. It identifies
the representation cost that remains outside the abstract DDFS bounds. -/
namespace MaximumMatching.Search

/-- The current adjacency-predicate interface enumerates all ordered pairs,
including nonedges and loops, before the scan guard rejects them. -/
theorem allCandidates_length (n : Nat) : (allCandidates n).length = n * n := by
  have aux (xs : List (Fin n)) :
      (xs.flatMap fun u => (List.finRange n).map fun v => (u, v)).length = xs.length * n := by
    induction xs with
    | nil => simp
    | cons u us ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map,
        List.length_finRange, List.length_cons, ih, Nat.add_mul, Nat.one_mul]
      omega
  simpa only [allCandidates, List.length_finRange] using aux (List.finRange n)

end MaximumMatching.Search
