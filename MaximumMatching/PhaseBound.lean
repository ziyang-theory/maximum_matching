import MaximumMatching.PhaseProgress
import MaximumMatching.PhaseDriver
import Init.Data.Nat.Sqrt.Lemmas

/-! The square-root bound on the number of positive blocking phases, connected
to the executable outer loop. This is not a bound on the cost of finding a
phase: concrete MIN/MAX/DDFS implementation and cost remain separate. -/
namespace MaximumMatching
namespace PhaseDriver
variable {n : Nat} {G : Graph (Fin n)}

/-- Every positive search result is a maximal family of shortest augmenting
paths. This specification is independent of the stopping-completeness contract;
a particular MV search must establish both from its implementation. -/
def ShortestBlocking (search : Search G) : Prop :=
  ∀ M, (search M).count ≠ 0 → ∃ l, (search M).MaximalShortest l

/-- Once all augmenting paths have length at least `l`, at most `n/(l+1)`
further positive phases can occur. No shortestness premise is needed here. -/
theorem run_phases_of_long_paths (search : Search G) (M : Matching G) (l : Nat)
    (hlong : ∀ p : AltPath M, p.Augmenting → l ≤ p.length) :
    (run search M).positivePhases ≤ n / (l + 1) := by
  have hb := deficit_of_long_paths M (run search M).matching l hlong
  have hgain := run_cardinality search M
  have hdef : (run search M).matching.cardinality - M.cardinality =
      (run search M).augmentations := by omega
  rw [hdef] at hb
  exact Nat.le_trans (run_positivePhases_le_augmentations search M)
    ((Nat.le_div_iff_mul_le (by omega)).mpr hb)

/-- Split the run after at most `k` short phases. The remaining matching has
augmenting-path length at least `l+k`, and the proved packing bound controls
the remaining cardinality deficit. -/
theorem run_phases_cutoff (search : Search G) (hsearch : ShortestBlocking search)
    (k : Nat) : ∀ (M : Matching G) (l : Nat),
    (∀ p : AltPath M, p.Augmenting → l ≤ p.length) →
    (run search M).positivePhases ≤ k + n / (l + k + 1) := by
  induction k with
  | zero =>
    intro M l hlong
    simpa only [Nat.add_zero, Nat.zero_add] using run_phases_of_long_paths search M l hlong
  | succ k ih =>
    intro M l hlong
    by_cases hz : (search M).count = 0
    · rw [run]
      simp only [hz, ↓reduceDIte]
      exact Nat.zero_le _
    · obtain ⟨a, ha⟩ := hsearch M hz
      have hpos : 0 < (search M).count := by omega
      have hla : l ≤ a := by
        have hl := hlong ((search M).path ⟨0, hpos⟩) ((search M).augmenting _)
        rwa [ha.length_eq] at hl
      have hnext : ∀ p : AltPath (search M).run, p.Augmenting → l + 1 ≤ p.length := by
        intro p hp
        have hstrict := (search M).shortest_length_increases a ha p hp
        omega
      have hrest := ih (search M).run (l + 1) hnext
      rw [run]
      simp only [hz, ↓reduceDIte]
      have he : l + 1 + k + 1 = l + (k + 1) + 1 := by omega
      rw [he] at hrest
      omega

/-- A concrete integer square-root bound on positive phases of any search
satisfying `ShortestBlocking`. This theorem uses the actual loop and proved
phase progress, and does not assume a phase-count bound. -/
theorem run_positivePhases_le_two_sqrt (search : Search G)
    (hsearch : ShortestBlocking search) (M : Matching G) :
    (run search M).positivePhases ≤ 2 * Nat.sqrt n := by
  have hb := run_phases_cutoff search hsearch (Nat.sqrt n) M 0
    (fun _ _ => Nat.zero_le _)
  simp only [Nat.zero_add] at hb
  have hs := Nat.lt_succ_sqrt n
  have hdiv : n / (Nat.sqrt n + 1) < Nat.sqrt n + 1 :=
    (Nat.div_lt_iff_lt_mul (by omega)).mpr hs
  omega

end PhaseDriver
end MaximumMatching
