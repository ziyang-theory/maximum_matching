import MaximumMatching.Blossom
import MaximumMatching.BaseTree
import MaximumMatching.BlossomClosure

/-! Connecting source blossoms to cuts in the actual common-base relation. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Every recursive blossom member follows the actual base function to its root,
with all intermediate vertices at or below the blossom threshold. -/
theorem blossom_to_cut (t : Nat) (b v : V) (h : Blossom M t b v) :
    BaseTree.Cut (IsBase M) (tenacity M) t b v := by
  induction t using Nat.strongRecOn generalizing b v with
  | ind t ih =>
    cases t with
    | zero => exact False.elim h
    | succ t =>
      cases t with
      | zero => exact False.elim h
      | succ t =>
        rcases h with hs | ⟨w, hwb, _, hw⟩
        · exact .edge hs.2 (by rw [hs.1]; exact Nat.le_refl _)
        · have hcut := ih t (by omega) w v hw
          have hcut' : BaseTree.Cut (IsBase M) (tenacity M) (t + 2) w v := by
            apply hcut.mono
            intro x hx
            cases htx : tenacity M x with
            | none => simp only [htx, levelLE] at hx
            | some s =>
              have hst : s ≤ t := by simpa only [htx, levelLE] using hx
              change s ≤ t + 2
              omega
          rcases hwb with hs | he
          · exact hcut'.trans (.edge hs.2 (by rw [hs.1]; exact Nat.le_refl _))
          · simpa only [he] using hcut'

/-- Nonempty source blossoms necessarily have outer bases. -/
theorem blossom_outer (t : Nat) (b v : V) (h : Blossom M t b v) : Outer M b := by
  have hc := blossom_to_cut t b v h
  clear h
  induction hc with
  | edge hb _ => exact hb.outer
  | step _ _ _ ih => exact ih

/-- A matched edge preserves the actual common base relation. -/
theorem matched_isBase_iff {u v : V} (hm : M.mate u = some v) (b : V) :
    IsBase M u b ↔ IsBase M v b := by
  constructor
  · rintro ⟨t, hut, hb⟩
    exact ⟨t, (matched_tenacity M hm).1.symm.trans hut,
      (matched_common_base_iff M hm t hut b).1 hb⟩
  · rintro ⟨t, hvt, hb⟩
    have hut := (matched_tenacity M hm).1.trans hvt
    exact ⟨t, hut, (matched_common_base_iff M hm t hut b).2 hb⟩

/-- Every source blossom contains both endpoints of any matched edge or neither. -/
theorem matched_blossom_iff {u v : V} (hm : M.mate u = some v)
    (t : Nat) (b : V) : Blossom M t b u ↔ Blossom M t b v := by
  induction t using Nat.strongRecOn generalizing b with
  | ind t ih =>
    cases t with
    | zero => rfl
    | succ t =>
      cases t with
      | zero => rfl
      | succ t =>
        have hs : BaseStratum M (t + 2) b u ↔ BaseStratum M (t + 2) b v := by
          unfold BaseStratum
          rw [(matched_tenacity M hm).1, matched_isBase_iff hm b]
        constructor
        · intro h
          rcases h with h | ⟨w, hw, ho, hwm⟩
          · exact Or.inl (hs.1 h)
          · exact Or.inr ⟨w, hw, ho, (ih t (by omega) w).1 hwm⟩
        · intro h
          rcases h with h | ⟨w, hw, ho, hwm⟩
          · exact Or.inl (hs.2 h)
          · exact Or.inr ⟨w, hw, ho, (ih t (by omega) w).2 hwm⟩


/-- Source recursive blossoms are exactly cuts of the actual common-base tree.
This equivalence does not presuppose that every vertex has a base. -/
theorem blossom_iff_base_cut (t : Nat) (ht : t % 2 = 1) (b v : V) :
    Blossom M t b v ↔ BaseTree.Cut (IsBase M) (tenacity M) t b v :=
  ⟨blossom_to_cut t b v, blossom_of_base_cut t ht b v⟩

/-- Any overlapping valid blossoms are nested. This is the laminarity assertion
of Theorem 6.19(3), proved from functionality of common bases and the exact
source recursion. No laminarity or blossom correctness premise is assumed. -/
theorem blossoms_laminar (s t : Nat) (hs : s % 2 = 1) (ht : t % 2 = 1)
    (b c : V) (hb : levelLT (some s) (tenacity M b))
    (hc : levelLT (some t) (tenacity M c))
    (hover : ∃ v, Blossom M s b v ∧ Blossom M t c v) :
    (∀ v, Blossom M s b v → Blossom M t c v) ∨
      (∀ v, Blossom M t c v → Blossom M s b v) := by
  have hfun : BaseTree.Functional (IsBase M) := by
    intro v x y hx hy
    exact hx.unique hy
  have hcut : ∃ v, BaseTree.Cut (IsBase M) (tenacity M) s b v ∧
      BaseTree.Cut (IsBase M) (tenacity M) t c v := by
    obtain ⟨v, hvb, hvc⟩ := hover
    exact ⟨v, blossom_to_cut s b v hvb, blossom_to_cut t c v hvc⟩
  rcases BaseTree.cut_laminar hfun s t b c hb hc hcut with hbc | hcb
  · exact Or.inl (fun v hv => blossom_of_base_cut t ht c v (hbc v (blossom_to_cut s b v hv)))
  · exact Or.inr (fun v hv => blossom_of_base_cut s hs b v (hcb v (blossom_to_cut t c v hv)))

/-- At a fixed threshold, valid blossoms with distinct bases are disjoint. -/
theorem blossoms_disjoint_same_tenacity (t : Nat) (b c : V)
    (hb : levelLT (some t) (tenacity M b)) (hc : levelLT (some t) (tenacity M c))
    (hne : b ≠ c) : ∀ v, ¬(Blossom M t b v ∧ Blossom M t c v) := by
  rintro v ⟨hvb, hvc⟩
  apply hne
  exact BaseTree.cut_boundary_unique (fun _ _ _ hx hy => hx.unique hy) t b c v hb hc
    (blossom_to_cut t b v hvb) (blossom_to_cut t c v hvc)


/-- Lemma 7.3: a fixed-base blossom grows monotonically with its odd index. -/
theorem blossom_mono (s t : Nat) (ht : t % 2 = 1) (hst : s ≤ t)
    (b v : V) (hv : Blossom M s b v) : Blossom M t b v := by
  apply blossom_of_base_cut t ht b v
  apply (blossom_to_cut s b v hv).mono
  intro x hx
  cases htx : tenacity M x with
  | none => simp only [htx, levelLE] at hx
  | some r =>
    have hrs : r ≤ s := by simpa only [htx, levelLE] using hx
    change r ≤ t
    omega

/-- Lemma 7.5: when one valid blossom's base lies in another blossom, the first
blossom is a proper subset of the second. The witness of strictness is its base. -/
theorem blossom_strict_nested_of_base_mem (s t : Nat) (ht : t % 2 = 1)
    (b c : V) (hb : levelLT (some s) (tenacity M b)) (hbc : Blossom M t c b) :
    (∀ v, Blossom M s b v → Blossom M t c v) ∧
      (Blossom M t c b ∧ ¬Blossom M s b b) := by
  obtain ⟨r, hbr, hrt⟩ := blossom_tenacity_bound t c b hbc
  have hsr : s < r := by simpa only [hbr, levelLT] using hb
  refine ⟨?_, hbc, blossom_excludes_base s b hb⟩
  intro v hv
  have hsmall : Blossom M t b v := blossom_mono s t ht (by omega) b v hv
  exact blossom_of_base_cut t ht c v
    ((blossom_to_cut t b v hsmall).trans (blossom_to_cut t c b hbc))

end MaximumMatching
