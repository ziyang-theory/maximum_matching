import MaximumMatching.BridgeBuckets

/-! Correctness of MAX's concrete label assignments. A supplied support member
is checked through its actual semantic tenacity; no arithmetic bound is assumed.
Discovering all support members by the contracted DDFS phase remains separate. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The exact subtraction used by MAX follows from finite vertex tenacity. -/
theorem maxlevel_eq_tenacity_sub (v : V) (t lo : Nat)
    (ht : tenacity M v = some t) (hlo : minlevel M v = some lo) :
    lo ≤ t ∧ maxlevel M v = some (t - lo) := by
  have hadd := minlevel_add_maxlevel M v
  rw [hlo, ht] at hadd
  cases hhi : maxlevel M v with
  | none => simp only [hhi, levelAdd] at hadd; contradiction
  | some hi =>
    have heq : lo + hi = t := by simpa only [hhi, levelAdd, Option.some.injEq] using hadd
    exact ⟨by omega, congrArg some (by omega)⟩

/-- At tenacity 2i+1 the minimum level is already at most i, so MAX does not
need an uncomputed minimum label for any vertex at its current tenacity. -/
theorem minlevel_le_half_tenacity (v : V) (i : Nat)
    (ht : tenacity M v = some (2 * i + 1)) :
    ∃ lo, minlevel M v = some lo ∧ lo ≤ i := by
  obtain ⟨e, o, he, ho, _, _, hsum⟩ := finite_levels_of_tenacity v (2 * i + 1) ht
  refine ⟨min e o, ?_, ?_⟩
  · simp [minlevel, he, ho, levelMin]
  · omega

namespace Search
variable [DecidableEq V]

/-- The actual MAX assignment preserves label soundness whenever the processed
vertex has the triggering bridge's tenacity. -/
theorem assignMax_labelsSound (s : State V) (t : Nat) (v : V)
    (hs : LabelsSound M s) (ht : tenacity M v = some t) :
    LabelsSound M (assignMax s t v) := by
  unfold assignMax
  cases hlo : s.minLabel v with
  | none => exact hs
  | some lo =>
    have htrue := maxlevel_eq_tenacity_sub v t lo ht (hs.1 v lo hlo)
    refine ⟨hs.1, ?_⟩
    intro w k hw
    change (if w = v then some (t - lo) else s.maxLabel w) = some k at hw
    split at hw
    next he =>
      have hk := Option.some.inj hw
      simpa only [he, hk] using htrue.2
    next _ => exact hs.2 w k hw

/-- An actual vertex with current tenacity receives its full semantic maxlevel. -/
theorem assignMax_correct (s : State V) (i : Nat) (v : V)
    (hc : MinCompleteBelow M i s) (ht : tenacity M v = some (2 * i + 1)) :
    (assignMax s (2 * i + 1) v).maxLabel v = maxlevel M v := by
  obtain ⟨lo, hlo, hli⟩ := minlevel_le_half_tenacity v i ht
  have hslo := hc v lo hlo hli
  have hh := maxlevel_eq_tenacity_sub v (2 * i + 1) lo ht hlo
  simp [assignMax, hslo, hh.2]

theorem assignMax_minInvariant (s : State V) (i t : Nat) (v : V)
    (hi : MinInvariant M i s) (ht : tenacity M v = some t) :
    MinInvariant M i (assignMax s t v) := by
  have hs := assignMax_labelsSound s t v hi.1 ht
  unfold assignMax at hs ⊢
  cases hlo : s.minLabel v with
  | none => exact hi
  | some lo => exact ⟨by simpa only [hlo] using hs, hi.2⟩

theorem assignMax_preserves_known_maxLabel (s : State V) (t : Nat) (u v : V) (k : Nat)
    (hs : LabelsSound M s) (ht : tenacity M u = some t) (hv : s.maxLabel v = some k) :
    (assignMax s t u).maxLabel v = some k := by
  by_cases he : v = u
  · have hvtrue : maxlevel M v = some k := hs.2 v k hv
    unfold assignMax
    cases hlo : s.minLabel u with
    | none => exact hv
    | some lo =>
      have hh := (maxlevel_eq_tenacity_sub u t lo ht (hs.1 u lo hlo)).2
      rw [he] at hvtrue
      have hk := Option.some.inj (hh.symm.trans hvtrue)
      simp only [he, ite_true, hk]
  · unfold assignMax
    cases hlo : s.minLabel u with
    | none => exact hv
    | some lo => simpa only [he, ite_false] using hv

/-- A vertex in an actual bridge support has precisely the triggering tenacity. -/
theorem assignMax_support_member (s : State V) (i : Nat) (u v w : V)
    (hc : MinCompleteBelow M i s) (he : MaximumMatching.edgeTenacity M u v = some (2 * i + 1))
    (hw : InSupport M u v w) :
    (assignMax s (2 * i + 1) w).maxLabel w = maxlevel M w := by
  obtain ⟨_, t, _, het, hwt, _⟩ := hw
  have ht : t = 2 * i + 1 := Option.some.inj (het.symm.trans he)
  exact assignMax_correct s i w hc (ht ▸ hwt)

/-- Execute the actual assignment for a supplied finite support list. -/
def assignMaxList (t : Nat) (vertices : List V) (s : State V) : State V :=
  vertices.foldl (fun state v => assignMax state t v) s

theorem assignMaxList_minInvariant (s : State V) (i t : Nat) (vs : List V)
    (hi : MinInvariant M i s) (ht : ∀ v ∈ vs, tenacity M v = some t) :
    MinInvariant M i (assignMaxList t vs s) := by
  induction vs generalizing s with
  | nil => exact hi
  | cons v vs ih =>
    exact ih _ (assignMax_minInvariant s i t v hi (ht v (by simp)))
      (fun w hw => ht w (List.mem_cons_of_mem _ hw))

theorem assignMaxList_preserves_known_maxLabel (s : State V) (t : Nat) (vs : List V)
    (hs : LabelsSound M s) (ht : ∀ v ∈ vs, tenacity M v = some t)
    (v : V) (k : Nat) (hv : s.maxLabel v = some k) :
    (assignMaxList t vs s).maxLabel v = some k := by
  induction vs generalizing s with
  | nil => exact hv
  | cons u us ih =>
    exact ih _ (assignMax_labelsSound s t u hs (ht u (by simp)))
      (fun w hw => ht w (List.mem_cons_of_mem _ hw))
      (assignMax_preserves_known_maxLabel s t u v k hs (ht u (by simp)) hv)

/-- Every listed support vertex obtains its semantic maxlevel even when lists
overlap or contain duplicates; assignments to other members cannot destroy it. -/
theorem assignMaxList_member_correct (s : State V) (i : Nat) (vs : List V)
    (hi : MinInvariant M i s) (ht : ∀ v ∈ vs, tenacity M v = some (2 * i + 1))
    (v : V) (hv : v ∈ vs) :
    (assignMaxList (2 * i + 1) vs s).maxLabel v = maxlevel M v := by
  induction vs generalizing s with
  | nil => simp at hv
  | cons u us ih =>
    have hut := ht u (by simp)
    have his := assignMax_minInvariant s i (2 * i + 1) u hi hut
    rcases List.mem_cons.mp hv with he | he
    · subst u
      have hset := assignMax_correct s i v hi.2.1 hut
      obtain ⟨lo, hlo, _⟩ := minlevel_le_half_tenacity v i hut
      have hmax := (maxlevel_eq_tenacity_sub v (2 * i + 1) lo hut hlo).2
      exact (assignMaxList_preserves_known_maxLabel (assignMax s (2 * i + 1) v) (2 * i + 1) us
        his.1 (fun w hw => ht w (List.mem_cons_of_mem _ hw)) v _ (hset.trans hmax)).trans hmax.symm
    · exact ih _ his (fun w hw => ht w (List.mem_cons_of_mem _ hw)) he

end Search
end MaximumMatching
