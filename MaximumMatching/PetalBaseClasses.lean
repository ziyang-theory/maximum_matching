import MaximumMatching.PetalBase

/-! Preservation of canonical blossom classes while temporary buds still have
current tenacity. Once all surviving roots are above the current threshold,
this invariant yields the next level's lower-blossom representation. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

/-- Two vertices have the same membership in every valid blossom together
with its high-tenacity boundary. No temporary bud is required to be high. -/
def SameBlossomClass (M : Matching G) (t : Nat) (u v : V) : Prop :=
  ∀ b, levelLT (some t) (tenacity M b) →
    ((u = b ∨ Blossom M t b u) ↔ (v = b ∨ Blossom M t b v))

namespace SameBlossomClass

omit [DecidableEq V] in
theorem refl (u : V) : SameBlossomClass M t u u := fun _ _ => Iff.rfl

omit [DecidableEq V] in
theorem symm (h : SameBlossomClass M t u v) : SameBlossomClass M t v u :=
  fun b hb => (h b hb).symm

omit [DecidableEq V] in
theorem trans (h : SameBlossomClass M t u v) (h' : SameBlossomClass M t v w) :
    SameBlossomClass M t u w := fun b hb => (h b hb).trans (h' b hb)

omit [DecidableEq V] in
/-- Following the actual base chain below a threshold preserves the class. -/
theorem of_blossom (ht : t % 2 = 1) (h : Blossom M t v u) : SameBlossomClass M t u v := by
  intro b hb
  have hu := blossom_to_cut t v u h
  have hfun : BaseTree.Functional (IsBase M) := fun _ _ _ h₁ h₂ => h₁.unique h₂
  constructor
  · rintro (he | hu')
    · obtain ⟨a, ha, hat⟩ := blossom_tenacity_bound t v u h
      rw [← he, ha] at hb
      change t < a at hb
      omega
    · rcases BaseTree.Below.boundary_comparison hfun (fun _ h => h) (by
        intro hlow
        cases ht' : tenacity M b with
        | none => simp only [ht', levelLE] at hlow
        | some a =>
          rw [ht'] at hb hlow
          change t < a at hb
          change a ≤ t at hlow
          omega) hu (blossom_to_cut t b u hu') with hvb | hvb
      · exact Or.inl hvb
      · exact Or.inr (blossom_of_base_cut t ht b v hvb)
  · rintro (rfl | hv)
    · exact Or.inr h
    · exact Or.inr (blossom_of_base_cut t ht b u (hu.trans (blossom_to_cut t b v hv)))

end SameBlossomClass

/-- Bud lookup preserves each vertex's canonical class at the stated cutoff. -/
def BudBlossomClasses (M : Matching G) (t : Nat) (F : BudForest V) : Prop :=
  ∀ v, SameBlossomClass M t v (F.root v)

theorem budBlossomClasses_of_lower (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1) (hrep : LowerBlossomRepresentation M cut s F) :
    BudBlossomClasses M (cut + 2) F := by
  intro v
  by_cases he : F.root v = v
  · rw [he]
    exact SameBlossomClass.refl v
  · cases hv : s.minLabel v with
    | none => exact False.elim (he (F.root_of_fixed v (h.unknown_fixed v hv)))
    | some k =>
      rcases (hrep v k hv).2 with hv' | hbl
      · exact False.elim (he hv'.symm)
      · exact SameBlossomClass.of_blossom (by omega)
          (blossom_mono cut (cut + 2) (by omega) (by omega) (F.root v) v hbl)

/-- High surviving roots turn class preservation into the exact
lower-blossom invariant needed by the next MIN stage. -/
theorem BudBlossomClasses.lower_representation (h : BudBlossomClasses M t F)
    (hhigh : ∀ v k, s.minLabel v = some k → levelLT (some t) (tenacity M (F.root v))) :
    LowerBlossomRepresentation M t s F := by
  intro v k hv
  have hh := hhigh v k hv
  exact ⟨hh, (h v (F.root v) hh).2 (Or.inl rfl)⟩

namespace PetalRecord
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G} {cut : Nat}

theorem selected_sameBlossomClass (R : PetalRecord M)
    (P : CurrentBridgeRepresentation M cut R.invariant)
    (hc : cut % 2 = 1) (hnoaug : ∀ p : AltPath M, p.Augmenting → cut + 2 < p.length)
    (hten : R.tenacity = cut + 2) (hlow : NonrootLow M (cut + 2) R.forest)
    (w : Fin n) (hw : R.selected w) :
    SameBlossomClass M (cut + 2) w R.bottleneck := by
  by_cases he : w = R.bottleneck
  · rw [he]
    exact SameBlossomClass.refl _
  · have hwt := (R.newRoots_support_of_current P hc (fun p hp => Nat.le_of_lt (hnoaug p hp))
      hten w ((R.mem_newRoots w).2 ⟨hw, he⟩)).1
    rw [hten] at hwt
    rcases R.selected_base_relation P hc hnoaug hten hlow w hw he with hb | ⟨hbt, b, hwb, hbb⟩
    · exact SameBlossomClass.of_blossom (by omega) (Or.inl ⟨hwt, hb⟩)
    · exact (SameBlossomClass.of_blossom (by omega) (show Blossom M (cut + 2) b w from
        Or.inl ⟨hwt, hwb⟩)).trans
        (SameBlossomClass.of_blossom (by omega) (show Blossom M (cut + 2) b R.bottleneck from
          Or.inl ⟨hbt, hbb⟩)).symm

/-- Actual recorded contraction preserves canonical classes, including
contractions whose temporary bottleneck has current tenacity. -/
theorem after_blossomClasses (R : PetalRecord M)
    (P : CurrentBridgeRepresentation M cut R.invariant)
    (hc : cut % 2 = 1) (hnoaug : ∀ p : AltPath M, p.Augmenting → cut + 2 < p.length)
    (hten : R.tenacity = cut + 2) (hlow : NonrootLow M (cut + 2) R.forest)
    (hclasses : BudBlossomClasses M (cut + 2) R.forest) :
    BudBlossomClasses M (cut + 2) R.after := by
  intro v
  by_cases hs : R.selectedFiber v
  · rw [R.after_selected v hs]
    exact (hclasses v).trans (R.selected_sameBlossomClass P hc hnoaug hten hlow (R.forest.root v) hs)
  · rw [R.after_outside v hs]
    exact hclasses v

end PetalRecord
end MaximumMatching.Search
