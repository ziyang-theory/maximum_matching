import MaximumMatching.Bud

/-! Executable merging of bud trees. The smaller-rank target remains a root;
every vertex in the source tree acquires that target, and all other trees keep
their roots. The rank guard is checked by the executable merging operation. -/
namespace MaximumMatching.BudForest
variable {V : Type} [DecidableEq V]

/-- Redirect one pointer to a strictly lower-ranked vertex. -/
def redirect (F : BudForest V) (x b : V) (h : F.rank b < F.rank x) : BudForest V where
  parent v := if v = x then b else F.parent v
  rank := F.rank
  decreases := by
    intro v hv
    by_cases he : v = x
    · subst v
      simpa only [ite_true] using h
    · simp only [ite_eq_right he] at hv ⊢
      exact F.decreases v hv

theorem redirect_target_fixed (F : BudForest V) (x b : V) (h : F.rank b < F.rank x)
    (hb : F.parent b = b) : (F.redirect x b h).parent b = b := by
  have hbx : b ≠ x := by intro he; rw [he] at h; omega
  simp only [redirect, ite_eq_right hbx, hb]

/-- Linking two actual roots changes precisely the source root's class. -/
theorem redirect_roots (F : BudForest V) (x b : V) (h : F.rank b < F.rank x)
    (hx : F.parent x = x) (hb : F.parent b = b) (v : V) :
    (F.redirect x b h).root v = if F.root v = x then b else F.root v := by
  by_cases hv : v = x
  · subst v
    rw [← (F.redirect x b h).root_parent]
    have hp : (F.redirect x b h).parent x = b := by simp only [redirect, ite_true]
    rw [hp, (F.redirect x b h).root_of_fixed b (F.redirect_target_fixed x b h hb),
      F.root_of_fixed x hx, ite_eq_left rfl]
  · by_cases hp : F.parent v = v
    · have hp' : (F.redirect x b h).parent v = v := by simp only [redirect, ite_eq_right hv, hp]
      rw [(F.redirect x b h).root_of_fixed v hp', F.root_of_fixed v hp, ite_eq_right hv]
    · rw [← (F.redirect x b h).root_parent]
      have hp' : (F.redirect x b h).parent v = F.parent v := by simp only [redirect, ite_eq_right hv]
      rw [hp', F.redirect_roots x b h hx hb (F.parent v), F.root_parent]
termination_by F.rank v
decreasing_by exact F.decreases v (by assumption)

/-- Merge the source's entire current tree into the target's current tree
when the target root has lower rank; otherwise leave the forest unchanged. -/
def mergeInto (F : BudForest V) (x b : V) : BudForest V :=
  if h : F.rank (F.root b) < F.rank (F.root x) then F.redirect (F.root x) (F.root b) h else F

theorem mergeInto_rank (F : BudForest V) (x b v : V) :
    (F.mergeInto x b).rank v = F.rank v := by
  unfold mergeInto
  split <;> rfl

/-- Exact root-map effect of the executable merge, including the failed guard. -/
theorem mergeInto_root (F : BudForest V) (x b v : V) :
    (F.mergeInto x b).root v =
      if F.rank (F.root b) < F.rank (F.root x) ∧ F.root v = F.root x
      then F.root b else F.root v := by
  unfold mergeInto
  split
  next h =>
    rw [F.redirect_roots (F.root x) (F.root b) h (F.root_fixed x) (F.root_fixed b) v]
    simp only [h, true_and]
  next h => simp only [h, false_and, ite_false]

theorem mergeInto_target (F : BudForest V) (x b : V) :
    (F.mergeInto x b).root b = F.root b := by
  rw [F.mergeInto_root]
  split
  · rfl
  · rfl

theorem mergeInto_source (F : BudForest V) (x b : V)
    (h : F.rank (F.root b) < F.rank (F.root x)) :
    (F.mergeInto x b).root x = F.root b := by
  rw [F.mergeInto_root, ite_eq_left ⟨h, rfl⟩]

/-- Process a finite petal's roots with the actual guarded merging operation.
The matching-specific proof must establish its rank guards and selected set. -/
def mergeManyInto (F : BudForest V) (xs : List V) (b : V) : BudForest V :=
  match xs with
  | [] => F
  | x :: rest => (F.mergeInto x b).mergeManyInto rest b

theorem mergeManyInto_rank (F : BudForest V) (xs : List V) (b v : V) :
    (F.mergeManyInto xs b).rank v = F.rank v := by
  induction xs generalizing F with
  | nil => rfl
  | cons x xs ih =>
    change ((F.mergeInto x b).mergeManyInto xs b).rank v = _
    rw [ih, F.mergeInto_rank]

theorem mergeManyInto_target (F : BudForest V) (xs : List V) (b : V) :
    (F.mergeManyInto xs b).root b = F.root b := by
  induction xs generalizing F with
  | nil => rfl
  | cons x xs ih =>
    change ((F.mergeInto x b).mergeManyInto xs b).root b = _
    rw [ih, F.mergeInto_target]

/-- Merging never splits an existing bud tree. -/
theorem mergeInto_root_congr (F : BudForest V) (x b u v : V)
    (h : F.root u = F.root v) : (F.mergeInto x b).root u = (F.mergeInto x b).root v := by
  rw [F.mergeInto_root, F.mergeInto_root, h]

theorem mergeManyInto_root_congr (F : BudForest V) (xs : List V) (b u v : V)
    (h : F.root u = F.root v) : (F.mergeManyInto xs b).root u = (F.mergeManyInto xs b).root v := by
  induction xs generalizing F with
  | nil => exact h
  | cons x xs ih => exact ih (F.mergeInto x b) (F.mergeInto_root_congr x b u v h)

/-- A listed source with a lower-ranked target is actually merged, even with
duplicates or earlier overlapping source trees in the list. -/
theorem mergeManyInto_source (F : BudForest V) (xs : List V) (x b : V)
    (hx : x ∈ xs)
    (h : F.rank (F.root b) < F.rank (F.root x) ∨ F.root x = F.root b) :
    (F.mergeManyInto xs b).root x = F.root b := by
  induction xs generalizing F with
  | nil => exact False.elim (List.not_mem_nil hx)
  | cons y xs ih =>
    rcases List.mem_cons.mp hx with hxy | hxs
    · subst y
      have he : (F.mergeInto x b).root x = (F.mergeInto x b).root b := by
        rw [F.mergeInto_target]
        rcases h with hlt | heq
        · exact F.mergeInto_source x b hlt
        · exact (F.mergeInto_root_congr x b x b heq).trans (F.mergeInto_target x b)
      change ((F.mergeInto x b).mergeManyInto xs b).root x = _
      rw [(F.mergeInto x b).mergeManyInto_root_congr xs b x b he,
        (F.mergeInto x b).mergeManyInto_target, F.mergeInto_target]
    · have h' : (F.mergeInto y b).rank ((F.mergeInto y b).root b) <
          (F.mergeInto y b).rank ((F.mergeInto y b).root x) ∨
          (F.mergeInto y b).root x = (F.mergeInto y b).root b := by
        rw [F.mergeInto_rank, F.mergeInto_rank, F.mergeInto_target, F.mergeInto_root]
        split
        · exact Or.inr rfl
        · exact h
      change ((F.mergeInto y b).mergeManyInto xs b).root x = _
      rw [ih (F.mergeInto y b) hxs h', F.mergeInto_target]

end MaximumMatching.BudForest
