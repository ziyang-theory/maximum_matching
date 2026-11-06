import MaximumMatching.Base

/-! Exact minlevel decrease in the matched outer-to-inner reduction. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

theorem minlevel_eq_even_of_outer (u : V) (hu : Outer M u) :
    minlevel M u = evenlevel M u := by
  unfold Outer at hu
  unfold minlevel
  cases he : evenlevel M u with
  | none => simp only [he, levelLT] at hu
  | some e =>
    cases ho : oddlevel M u with
    | none => rfl
    | some o =>
      have heo : e < o := by simpa only [he, ho, levelLT] using hu
      exact congrArg some (Nat.min_eq_left (by omega))

/-- The mate of a matched outer vertex has strictly smaller minlevel, even if
the larger parity level is infinite. This justifies the outer case of induction
on minlevel in the minimum-tenacity base proof. -/
theorem matched_outer_minlevel {u v : V} (hm : M.mate u = some v)
    (hu : Outer M u) (k : Nat) (huk : minlevel M u = some k) :
    0 < k ∧ minlevel M v = some (k - 1) := by
  have hue : evenlevel M u = some k := (minlevel_eq_even_of_outer u hu).symm.trans huk
  have hmate := evenlevel_matched M (M.symm hm)
  rw [hue] at hmate
  cases hvo : oddlevel M v with
  | none => simp only [hvo, Option.map_none] at hmate; contradiction
  | some o =>
    have hk : k = o + 1 := by simpa only [hvo, Option.map_some, Option.some.injEq] using hmate
    have hve := evenlevel_matched M hm
    refine ⟨by omega, ?_⟩
    unfold Outer at hu
    rw [hue] at hu
    unfold minlevel
    rw [hve, hvo]
    cases huo : oddlevel M u with
    | none => simp only [Option.map_none, levelMin]; exact congrArg some (by omega)
    | some a =>
      have hka : k < a := by simpa only [huo, levelLT] using hu
      simp only [Option.map_some, levelMin, Nat.min_eq_right (by omega : o ≤ a + 1)]
      exact congrArg some (by omega)

end MaximumMatching
