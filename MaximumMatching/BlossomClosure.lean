import MaximumMatching.Blossom
import MaximumMatching.BaseTree

/-! Closure of the source's recursively defined blossoms under actual semantic
base edges. This connects finite base chains to blossom membership without
assuming global existence of bases or any laminarity theorem. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A vertex with a common base has finite tenacity at least three. The base
strictly lowers minimum level, so its child's even level is positive and even. -/
theorem IsBase.tenacity_ge_three {v b : V} (h : IsBase M v b)
    (s : Nat) (hs : tenacity M v = some s) : 3 ≤ s := by
  obtain ⟨e, o, he, ho, hep, hop, heo⟩ := finite_levels_of_tenacity v s hs
  have hmin : minlevel M v = some (min e o) := by
    simp only [minlevel, he, ho, levelMin]
  obtain ⟨j, _, hj⟩ := h.minlevel_lt (min e o) hmin
  have hme := Nat.min_le_left e o
  have hmo := Nat.min_le_right e o
  omega

/-- A vertex belongs to the blossom of its actual base at every larger odd
threshold. Smaller indices are reached by the source's two-step recursion. -/
theorem blossom_of_base_le (t : Nat) (ht : t % 2 = 1) (b v : V)
    (hb : IsBase M v b) (hle : levelLE (tenacity M v) (some t)) :
    Blossom M t b v := by
  induction t using Nat.strongRecOn generalizing b v with
  | ind t ih =>
    obtain ⟨s, hs, _⟩ := (show IsBase M v b from hb)
    have hst : s ≤ t := by simpa only [hs, levelLE] using hle
    have hthree := hb.tenacity_ge_three s hs
    have hsodd := tenacity_odd M v s hs
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 2 := ⟨t - 2, by omega⟩
    by_cases heq : s = n + 2
    · exact Or.inl ⟨heq ▸ hs, hb⟩
    · have hsn : s ≤ n := by omega
      apply blossom_mono_step n b v hb.outer
      apply ih n (by omega) (by omega) b v hb
      simpa only [hs, levelLE] using hsn

/-- A blossom contains the children of each of its vertices under the common
base relation. The proof follows the actual recursive blossom definition. -/
theorem blossom_downward_closed (t : Nat) (ht : t % 2 = 1) (b w v : V)
    (hw : Blossom M t b w) (hbase : IsBase M v w) : Blossom M t b v := by
  induction t using Nat.strongRecOn generalizing b w v with
  | ind t ih =>
    cases t with
    | zero => exact False.elim hw
    | succ t =>
      cases t with
      | zero => exact False.elim hw
      | succ t =>
        rcases hw with hw | ⟨u, hu, huouter, huw⟩
        · obtain ⟨s, hs, _⟩ := (show IsBase M v w from hbase)
          have hhigh := hbase.high
          rw [hs, hw.1] at hhigh
          have hst : s < t + 2 := hhigh
          have hsodd := tenacity_odd M v s hs
          have hlow : levelLE (tenacity M v) (some t) := by
            rw [hs]
            change s ≤ t
            omega
          exact Or.inr ⟨w, Or.inl hw, hbase.outer,
            blossom_of_base_le t (by omega) w v hbase hlow⟩
        · exact Or.inr ⟨u, hu, huouter, ih t (by omega) (by omega) u w v huw hbase⟩

/-- Every bounded nonempty chain of actual bases is in the source blossom at
that odd cutoff. This is the reverse direction of blossom/cut correspondence. -/
theorem blossom_of_base_cut (t : Nat) (ht : t % 2 = 1) (b v : V)
    (h : BaseTree.Cut (IsBase M) (tenacity M) t b v) : Blossom M t b v := by
  induction h with
  | edge hbase hle => exact blossom_of_base_le t ht _ _ hbase hle
  | step hbase _ _ ih => exact blossom_downward_closed t ht _ _ _ ih hbase

end MaximumMatching
