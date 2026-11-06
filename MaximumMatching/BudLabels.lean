import MaximumMatching.Bud

/-! Updating bud ranks after new MIN labels are assigned. Existing assigned
labels are retained; unknown vertices are fixed roots, so their new ranks do
not invalidate a parent edge. No semantic base relation is assumed. -/
namespace MaximumMatching.BudForest
variable {V : Type} [DecidableEq V]

theorem fixed_of_rank_zero (F : BudForest V) (v : V) (h : F.rank v = 0) :
    F.parent v = v := by
  by_cases hn : F.parent v = v
  · exact hn
  · have := F.decreases v hn
    omega

/-- A nontrivial parent edge has assigned endpoints when ranks agree with
labels and roots of assigned vertices are assigned. -/
theorem parent_labels_some (F : BudForest V) (labels : V → Option Nat)
    (hrank : ∀ v, F.rank v = (labels v).getD 0)
    (hroots : ∀ v, (labels v).isSome → (labels (F.root v)).isSome)
    (v : V) (hv : F.parent v ≠ v) :
    (labels v).isSome ∧ (labels (F.parent v)).isSome := by
  have hs : (labels v).isSome := by
    cases he : labels v with
    | none => exact False.elim (hv (F.fixed_of_rank_zero v (by rw [hrank v, he]; rfl)))
    | some k => rfl
  refine ⟨hs, ?_⟩
  cases he : labels (F.parent v) with
  | some k => rfl
  | none =>
    have hf := F.fixed_of_rank_zero (F.parent v) (by rw [hrank (F.parent v), he]; rfl)
    have heroot : F.root v = F.parent v := by
      rw [← F.root_parent, F.root_of_fixed _ hf]
    have hroot := hroots v hs
    rw [heroot, he] at hroot
    contradiction

/-- Retain all pointers and update ranks to the operational MIN labels. -/
def withLabels (F : BudForest V) (labels next : V → Option Nat)
    (hrank : ∀ v, F.rank v = (labels v).getD 0)
    (hroots : ∀ v, (labels v).isSome → (labels (F.root v)).isSome)
    (hkeep : ∀ v k, labels v = some k → next v = some k) : BudForest V where
  parent := F.parent
  rank v := (next v).getD 0
  decreases := by
    intro v hv
    obtain ⟨hs, hp⟩ := F.parent_labels_some labels hrank hroots v hv
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp hp
    have h := F.decreases v hv
    rw [hrank v, hrank (F.parent v), hk, hl] at h
    rw [hkeep v k hk, hkeep (F.parent v) l hl]
    exact h

theorem withLabels_root (F : BudForest V) (labels next : V → Option Nat)
    (hrank : ∀ v, F.rank v = (labels v).getD 0)
    (hroots : ∀ v, (labels v).isSome → (labels (F.root v)).isSome)
    (hkeep : ∀ v k, labels v = some k → next v = some k) (v : V) :
    (F.withLabels labels next hrank hroots hkeep).root v = F.root v := by
  by_cases hf : F.parent v = v
  · exact (F.withLabels labels next hrank hroots hkeep).root_of_fixed v hf |>.trans
      (F.root_of_fixed v hf).symm
  · rw [← (F.withLabels labels next hrank hroots hkeep).root_parent]
    change (F.withLabels labels next hrank hroots hkeep).root (F.parent v) = F.root v
    rw [F.withLabels_root labels next hrank hroots hkeep, F.root_parent]
termination_by F.rank v
decreasing_by exact F.decreases v (by assumption)

theorem withLabels_assignedRoots (F : BudForest V) (labels next : V → Option Nat)
    (hrank : ∀ v, F.rank v = (labels v).getD 0)
    (hroots : ∀ v, (labels v).isSome → (labels (F.root v)).isSome)
    (hkeep : ∀ v k, labels v = some k → next v = some k) (v : V)
    (hv : (next v).isSome) :
    (next ((F.withLabels labels next hrank hroots hkeep).root v)).isSome := by
  rw [F.withLabels_root]
  cases he : labels v with
  | none =>
    have hf := F.fixed_of_rank_zero v (by rw [hrank v, he]; rfl)
    rw [F.root_of_fixed v hf]
    exact hv
  | some k =>
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (hroots v (by rw [he]; rfl))
    rw [hkeep _ l hl]
    rfl

end MaximumMatching.BudForest
