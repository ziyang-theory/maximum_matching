import MaximumMatching.Structure

/-! Laminarity of cuts in a functional parent relation. A cut consists of
nonempty parent chains whose non-root vertices lie below a threshold. This
combinatorial theorem is independent of the blossom definition and does not
assume any laminarity conclusion. -/
namespace MaximumMatching.BaseTree
variable {V : Type}

/-- Every child has at most one parent; existence is a separate property. -/
def Functional (parent : V → V → Prop) : Prop :=
  ∀ v a b, parent v a → parent v b → a = b

/-- A nonempty parent chain from `v` to `b`, with every vertex except the final
root satisfying `allowed`. The root need not satisfy `allowed`. -/
inductive Below (parent : V → V → Prop) (allowed : V → Prop) : V → V → Prop where
  | edge {v b} : parent v b → allowed v → Below parent allowed b v
  | step {v w b} : parent v w → allowed v → Below parent allowed b w →
      Below parent allowed b v

namespace Below
variable {parent : V → V → Prop} {A B : V → Prop} {b c v : V}

theorem allowed (h : Below parent A b v) : A v := by
  cases h with
  | edge _ hv => exact hv
  | step _ hv _ => exact hv

/-- Enlarging the allowed region preserves a chain. -/
theorem mono (h : Below parent A b v) (hab : ∀ x, A x → B x) : Below parent B b v := by
  induction h with
  | edge hrel hv => exact .edge hrel (hab _ hv)
  | step hrel hv _ ih => exact .step hrel (hab _ hv) ih

/-- Concatenation of two nonempty parent chains. -/
theorem trans (hvb : Below parent A b v) (hbc : Below parent A c b) :
    Below parent A c v := by
  induction hvb with
  | edge hrel hv => exact .step hrel hv hbc
  | step hrel hv _ ih => exact .step hrel hv (ih hbc)

/-- If two cut chains start at the same vertex, the smaller allowed region
must end first. Otherwise the larger cut's forbidden root lies in the smaller
allowed region. Functional parents make the shared initial chain unique. -/
theorem boundary_comparison (hfun : Functional parent) (hab : ∀ x, A x → B x)
    (hc : ¬ B c) (ha : Below parent A b v) (hb : Below parent B c v) :
    b = c ∨ Below parent B c b := by
  induction ha with
  | @edge v b hrel hv =>
    cases hb with
    | edge hrel' _ => exact Or.inl (hfun v b c hrel hrel')
    | @step _ w _ hrel' _ htail =>
      have heq := hfun v b w hrel hrel'
      exact Or.inr (heq.symm ▸ htail)
  | @step v w b hrel hv htail ih =>
    cases hb with
    | edge hrel' _ =>
      have heq := hfun v w c hrel hrel'
      exact False.elim (hc (heq ▸ hab w htail.allowed))
    | @step _ w' _ hrel' _ htail' =>
      have heq := hfun v w w' hrel hrel'
      exact ih (heq.symm ▸ htail')

/-- At one threshold the first forbidden ancestor is unique. -/
theorem boundary_unique (hfun : Functional parent) (hb : ¬ A b) (hc : ¬ A c)
    (hv : Below parent A b v) (hw : Below parent A c v) : b = c := by
  rcases boundary_comparison hfun (fun _ h => h) hc hv hw with he | hbc
  · exact he
  · exact False.elim (hb hbc.allowed)

/-- One shared vertex forces inclusion of the entire smaller-threshold cut. -/
theorem subset_of_overlap (hfun : Functional parent) (hab : ∀ x, A x → B x)
    (hc : ¬ B c) (overlap : ∃ v, Below parent A b v ∧ Below parent B c v) :
    ∀ v, Below parent A b v → Below parent B c v := by
  obtain ⟨x, hxa, hxb⟩ := overlap
  rcases boundary_comparison hfun hab hc hxa hxb with he | hbc
  · subst c
    intro v hv
    exact hv.mono hab
  · intro v hv
    exact (hv.mono hab).trans hbc

/-- Intersecting cuts whose allowed regions are comparable are nested. -/
theorem laminar (hfun : Functional parent)
    (hcompare : (∀ x, A x → B x) ∨ (∀ x, B x → A x))
    (hb : ¬ A b) (hc : ¬ B c)
    (overlap : ∃ v, Below parent A b v ∧ Below parent B c v) :
    (∀ v, Below parent A b v → Below parent B c v) ∨
      (∀ v, Below parent B c v → Below parent A b v) := by
  rcases hcompare with hab | hba
  · exact Or.inl (subset_of_overlap hfun hab hc overlap)
  · exact Or.inr (subset_of_overlap hfun hba hb (by
      obtain ⟨v, ha, hb⟩ := overlap
      exact ⟨v, hb, ha⟩))

end Below

/-- A cutoff in ranks extended by infinity; all non-root ranks are finite
and at most `t`. -/
def Cut (parent : V → V → Prop) (rank : V → Option Nat) (t : Nat) (b v : V) : Prop :=
  Below parent (fun x => levelLE (rank x) (some t)) b v

private theorem not_below_of_above (rank : V → Option Nat) (t : Nat) (b : V)
    (hb : levelLT (some t) (rank b)) : ¬ levelLE (rank b) (some t) := by
  cases hr : rank b with
  | none => simp only [levelLE, not_false_eq_true]
  | some r =>
    have htr : t < r := by simpa only [hr, levelLT] using hb
    change ¬ r ≤ t
    omega

/-- Exact uniqueness of the cutoff ancestor, permitting infinite root rank. -/
theorem cut_boundary_unique {parent : V → V → Prop} {rank : V → Option Nat}
    (hfun : Functional parent) (t : Nat) (b c v : V)
    (hb : levelLT (some t) (rank b)) (hc : levelLT (some t) (rank c))
    (hvb : Cut parent rank t b v) (hvc : Cut parent rank t c v) : b = c :=
  Below.boundary_unique hfun (not_below_of_above rank t b hb)
    (not_below_of_above rank t c hc) hvb hvc

/-- For two ordered rank thresholds, intersecting cuts are included in the
same order. No acyclicity or rank-increase premise is needed: finite parent
chains and forbidden boundary roots suffice. -/
theorem cut_subset_of_overlap {parent : V → V → Prop} {rank : V → Option Nat}
    (hfun : Functional parent) (s t : Nat) (hst : s ≤ t) (b c : V)
    (hc : levelLT (some t) (rank c))
    (overlap : ∃ v, Cut parent rank s b v ∧ Cut parent rank t c v) :
    ∀ v, Cut parent rank s b v → Cut parent rank t c v := by
  apply Below.subset_of_overlap hfun ?_ (not_below_of_above rank t c hc) overlap
  intro x hx
  cases hr : rank x with
  | none => simp only [hr, levelLE] at hx
  | some r =>
    have hrs : r ≤ s := by simpa only [hr, levelLE] using hx
    simp only [levelLE]
    omega

/-- The boundary cuts of a functional parent relation form a laminar family. -/
theorem cut_laminar {parent : V → V → Prop} {rank : V → Option Nat}
    (hfun : Functional parent) (s t : Nat) (b c : V)
    (hb : levelLT (some s) (rank b)) (hc : levelLT (some t) (rank c))
    (overlap : ∃ v, Cut parent rank s b v ∧ Cut parent rank t c v) :
    (∀ v, Cut parent rank s b v → Cut parent rank t c v) ∨
      (∀ v, Cut parent rank t c v → Cut parent rank s b v) := by
  by_cases hst : s ≤ t
  · exact Or.inl (cut_subset_of_overlap hfun s t hst b c hc overlap)
  · exact Or.inr (cut_subset_of_overlap hfun t s (by omega) c b hb (by
      obtain ⟨v, hvb, hvc⟩ := overlap
      exact ⟨v, hvc, hvb⟩))

end MaximumMatching.BaseTree
