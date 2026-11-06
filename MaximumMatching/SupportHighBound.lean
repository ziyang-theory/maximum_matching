import MaximumMatching.GeneralStructureInduction
import MaximumMatching.MatchingSearchGraph

/-! Relevant original path vertices are already covered by MIN at the current
tenacity stage. The bound for vertices above the endpoint tenacity uses the
actual common base, its last occurrence, and its strictly smaller minimum level. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A high vertex on any shortest path to an eligible-tenacity endpoint has
minimum level strictly below half the endpoint tenacity. -/
theorem high_vertex_minlevel_lt_half (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (ht : EligibleTenacity M t) (hpt : tenacity M p.last = some t)
    (I : Fin (p.length + 1))
    (hhigh : levelLE (some t) (tenacity M (p.vertex I))) :
    ∃ k, minlevel M (p.vertex I) = some k ∧ 2 * k < t := by
  by_cases heq : tenacity M (p.vertex I) = some t
  · obtain ⟨e, o, he, ho, _, _, hsum⟩ := finite_levels_of_tenacity (p.vertex I) t heq
    refine ⟨min e o, by simp only [minlevel, he, ho, levelMin], ?_⟩
    have hle := Nat.min_le_left e o
    have hle' := Nat.min_le_right e o
    have hodd := ht.1
    omega
  · have hstrict : levelLT (some t) (tenacity M (p.vertex I)) := by
      cases hi : tenacity M (p.vertex I) with
      | none => trivial
      | some s =>
        have hs : t ≤ s := by simpa only [hi, levelLE] using hhigh
        have hne : s ≠ t := by intro h; apply heq; rw [hi, h]
        change t < s
        omega
    have hImin := (p.limited_bfs_honesty hp I (by rw [hpt]; exact hhigh)).2
      (by rw [hpt]; exact hstrict)
    obtain ⟨b, hb, _⟩ := general_unique_base M t ht p.last hpt
    obtain ⟨B, hBb, hBhigh, hBlast⟩ := hb p rfl hp
    have hIB : I.val ≤ B.val := by
      by_cases hle : I.val ≤ B.val
      · exact hle
      · exact False.elim (hBlast I (by omega) hstrict)
    have hBmin := (p.limited_bfs_honesty hp B (by rw [hpt, hBb]; exact levelLT_le hBhigh)).2
      (by rw [hpt, hBb]; exact hBhigh)
    obtain ⟨e, o, he, ho, _, _, hsum⟩ := finite_levels_of_tenacity p.last t hpt
    have hvmin : minlevel M p.last = some (min e o) := by
      simp only [minlevel, he, ho, levelMin]
    have hbbase : IsBase M p.last b := ⟨t, hpt, hb⟩
    obtain ⟨j, hj, hjlt⟩ := hbbase.minlevel_lt (min e o) hvmin
    have hBj : B.val = j := by
      rw [hBb, hj] at hBmin
      exact Option.some.inj hBmin.symm
    refine ⟨I.val, hImin, ?_⟩
    have hle := Nat.min_le_left e o
    have hle' := Nat.min_le_right e o
    omega

end MaximumMatching.AltPath

namespace MaximumMatching.Search.BudGraphInvariant
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}
variable {cap : Nat} {s : State V} {F : BudForest V}

/-- Actual MIN coverage labels every relevant high vertex of an original
shortest path; callers need no separate assignment oracle for compression. -/
theorem high_path_vertex_assigned (h : BudGraphInvariant M cap s F)
    (p : AltPath M) (hp : p.Shortest) (t : Nat) (ht : EligibleTenacity M t)
    (hpt : tenacity M p.last = some t) (hcap : t ≤ 2 * cap + 1)
    (I : Fin (p.length + 1))
    (hhigh : levelLE (some t) (tenacity M (p.vertex I))) :
    ∃ k, s.minLabel (p.vertex I) = some k ∧
      minlevel M (p.vertex I) = some k ∧ 2 * k < t ∧ k ≤ cap := by
  obtain ⟨k, hk, hkt⟩ := p.high_vertex_minlevel_lt_half hp t ht hpt I hhigh
  have hkc : k ≤ cap := by omega
  exact ⟨k, h.minInvariant.2.1 _ _ hk hkc, hk, hkt, hkc⟩

end MaximumMatching.Search.BudGraphInvariant
