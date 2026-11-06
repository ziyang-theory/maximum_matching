import Std

section Bud

/-! Terminating bud-pointer lookup and verified path compression.

This verifies the data structure under a decreasing-rank invariant. It does not
assert that MV's petal construction establishes that invariant. -/
namespace MaximumMatching

structure BudForest (V : Type) where
  parent : V → V
  rank : V → Nat
  decreases : ∀ v, parent v ≠ v → rank (parent v) < rank v

namespace BudForest
variable {V : Type} [DecidableEq V]

def root (F : BudForest V) (v : V) : V :=
  if _h : F.parent v = v then v else F.root (F.parent v)
termination_by F.rank v
decreasing_by exact F.decreases v (by assumption)

theorem root_of_fixed (F : BudForest V) (v : V) (h : F.parent v = v) :
    F.root v = v := by
  rw [root, dite_eq_left h]

theorem root_parent (F : BudForest V) (v : V) :
    F.root (F.parent v) = F.root v := by
  by_cases h : F.parent v = v
  · rw [h]
  · symm
    rw [root, dite_eq_right h]

theorem root_fixed (F : BudForest V) (v : V) :
    F.parent (F.root v) = F.root v := by
  rw [root]
  split
  · assumption
  · exact F.root_fixed (F.parent v)
termination_by F.rank v
decreasing_by exact F.decreases v (by assumption)

theorem root_idempotent (F : BudForest V) (v : V) :
    F.root (F.root v) = F.root v :=
  F.root_of_fixed _ (F.root_fixed v)

theorem root_rank_le (F : BudForest V) (v : V) :
    F.rank (F.root v) ≤ F.rank v := by
  rw [root]
  split
  · exact Nat.le_refl _
  · exact Nat.le_trans (F.root_rank_le (F.parent v)) (Nat.le_of_lt (F.decreases v ‹_›))
termination_by F.rank v
decreasing_by exact F.decreases v (by assumption)

theorem root_rank_lt (F : BudForest V) (v : V) (h : F.root v ≠ v) :
    F.rank (F.root v) < F.rank v := by
  have hp : F.parent v ≠ v := by
    intro hp
    exact h (F.root_of_fixed v hp)
  rw [← F.root_parent]
  exact Nat.lt_of_le_of_lt (F.root_rank_le _) (F.decreases v hp)

/-- Compress one pointer after a root lookup, retaining the same ranks. -/
def compress (F : BudForest V) (x : V) : BudForest V where
  parent v := if v = x then F.root x else F.parent v
  rank := F.rank
  decreases := by
    intro v h
    by_cases hv : v = x
    · subst v
      simp only [ite_true] at h ⊢
      exact F.root_rank_lt x h
    · simp only [ite_eq_right (fun h => False.elim (hv h))] at h ⊢
      exact F.decreases v h

theorem compress_fixed (F : BudForest V) (x v : V) (h : F.parent v = v) :
    (F.compress x).parent v = v := by
  by_cases hv : v = x
  · subst v
    simp [compress, F.root_of_fixed x h]
  · simp [compress, hv, h]

theorem compress_root (F : BudForest V) (x v : V) :
    (F.compress x).root v = F.root v := by
  by_cases hv : v = x
  · subst v
    rw [← (F.compress x).root_parent]
    have hp : (F.compress x).parent x = F.root x := by simp [compress]
    rw [hp]
    exact (F.compress x).root_of_fixed _ (F.compress_fixed x _ (F.root_fixed x))
  · by_cases hp : F.parent v = v
    · rw [(F.compress x).root_of_fixed v (F.compress_fixed x v hp), F.root_of_fixed v hp]
    · rw [← (F.compress x).root_parent]
      have he : (F.compress x).parent v = F.parent v := by simp [compress, hv]
      rw [he, F.compress_root x (F.parent v), F.root_parent]
termination_by F.rank v
decreasing_by exact F.decreases v (by assumption)

/-- Compress a finite sequence of inspected vertices. -/
def compressMany (F : BudForest V) : List V → BudForest V
  | [] => F
  | x :: xs => (F.compress x).compressMany xs

theorem compressMany_root (F : BudForest V) (xs : List V) (v : V) :
    (F.compressMany xs).root v = F.root v := by
  induction xs generalizing F with
  | nil => rfl
  | cons x xs ih =>
    change ((F.compress x).compressMany xs).root v = F.root v
    rw [ih, F.compress_root]

end BudForest
end MaximumMatching

end Bud

section BudLabels

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

end BudLabels

section BudLink

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

end BudLink

section BudLinkExact

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

end BudLinkExact
