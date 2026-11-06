import MaximumMatching.BudLink

/-! Exact old-class effects of a finite guarded bud merge. The selected
classes are expressed using roots in the input forest, before any mutation. -/
namespace MaximumMatching.BudForest
variable {V : Type} [DecidableEq V]

theorem mergeInto_root_eq_or (F : BudForest V) (x b v : V) :
    (F.mergeInto x b).root v = F.root b ∨ (F.mergeInto x b).root v = F.root v := by
  rw [F.mergeInto_root]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem mergeManyInto_root_eq_or (F : BudForest V) (xs : List V) (b v : V) :
    (F.mergeManyInto xs b).root v = F.root b ∨
      (F.mergeManyInto xs b).root v = F.root v := by
  induction xs generalizing F with
  | nil => exact Or.inr rfl
  | cons x xs ih =>
    rcases ih (F.mergeInto x b) with hb | hv
    · exact Or.inl (hb.trans (F.mergeInto_target x b))
    · rcases F.mergeInto_root_eq_or x b v with hb | hv'
      · exact Or.inl (hv.trans hb)
      · exact Or.inr (hv.trans hv')

/-- A class absent from the source list retains its original root. No rank
guard is assumed: failed merges also preserve this statement. -/
theorem mergeManyInto_outside (F : BudForest V) (xs : List V) (b v : V)
    (hout : ∀ x, x ∈ xs → F.root x ≠ F.root v) :
    (F.mergeManyInto xs b).root v = F.root v := by
  induction xs generalizing F with
  | nil => rfl
  | cons x xs ih =>
    by_cases hvb : F.root v = F.root b
    · exact ((F.mergeManyInto_root_congr (x :: xs) b v b hvb).trans
        (F.mergeManyInto_target (x :: xs) b)).trans hvb.symm
    · have hv : (F.mergeInto x b).root v = F.root v := by
        rw [F.mergeInto_root]
        apply ite_eq_right
        intro he
        exact hout x (List.mem_cons_self) he.2.symm
      have htail : ∀ y, y ∈ xs → (F.mergeInto x b).root y ≠ (F.mergeInto x b).root v := by
        intro y hy he
        rw [hv] at he
        rcases F.mergeInto_root_eq_or x b y with hb | hy'
        · exact hvb (he.symm.trans hb)
        · exact hout y (List.mem_cons_of_mem x hy) (hy'.symm.trans he)
      exact (ih (F.mergeInto x b) htail).trans hv

/-- When every listed source satisfies the operational guard (or already
has the target root), the finite merge changes exactly those old classes.
Duplicate sources and old descendants are both included by this root test. -/
theorem mergeManyInto_root_exact (F : BudForest V) (xs : List V) (b v : V)
    (hguards : ∀ x, x ∈ xs →
      F.rank (F.root b) < F.rank (F.root x) ∨ F.root x = F.root b) :
    (F.mergeManyInto xs b).root v =
      if F.root v ∈ xs.map F.root then F.root b else F.root v := by
  by_cases hv : F.root v ∈ xs.map F.root
  · rw [ite_eq_left hv]
    obtain ⟨x, hx, hxv⟩ := List.mem_map.mp hv
    exact (F.mergeManyInto_root_congr xs b v x hxv.symm).trans
      (F.mergeManyInto_source xs x b hx (hguards x hx))
  · rw [ite_eq_right hv]
    apply F.mergeManyInto_outside xs b v
    intro x hx he
    exact hv (List.mem_map.mpr ⟨x, hx, he⟩)

end MaximumMatching.BudForest
