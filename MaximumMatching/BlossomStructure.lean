import MaximumMatching.MinimumBaseStructure
import MaximumMatching.Structure

section BaseTree

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

end BaseTree

section Blossom

/-! Source Definitions 6.2 and 6.8 as actual partial base and recursive blossoms.
`IsBase` uses all shortest alternating paths. It does not assume the general
base-existence theorem: existence is proved at minimum tenacity below. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A common path-relative base, at the vertex's finite tenacity. -/
noncomputable def IsBase (M : Matching G) (v b : V) : Prop :=
  ∃ t, tenacity M v = some t ∧
    ∀ p : AltPath M, p.last = v → p.Shortest → p.BaseOnPath t b

namespace IsBase

theorem path (h : IsBase M v b) :
    ∃ (t : Nat) (p : AltPath M), tenacity M v = some t ∧ p.last = v ∧
      p.Shortest ∧ p.BaseOnPath t b := by
  obtain ⟨t, ht, hb⟩ := h
  obtain ⟨e, o, he, _, hepar, _, _⟩ := finite_levels_of_tenacity v t ht
  have hs := (level_eq_some_iff M 0 v e).1 he
  obtain ⟨p, hpv, hpl, _⟩ := hs.1
  have hp : p.Shortest := by simpa only [AltPath.Shortest, hpl, hpv, hepar] using hs
  exact ⟨t, p, ht, hpv, hp, hb p hpv hp⟩

theorem unique (h : IsBase M v b) (h' : IsBase M v c) : b = c := by
  obtain ⟨t, p, ht, hpv, hp, hpb⟩ := h.path
  obtain ⟨s, hs, hc⟩ := h'
  have hst : s = t := Option.some.inj (hs.symm.trans ht)
  subst s
  exact p.baseOnPath_unique t b c hpb (hc p hpv hp)

theorem high (h : IsBase M v b) : levelLT (tenacity M v) (tenacity M b) := by
  obtain ⟨t, p, ht, _, _, hpb⟩ := h.path
  rw [ht]
  exact hpb.choose_spec.2.1

theorem outer (h : IsBase M v b) : Outer M b := by
  obtain ⟨t, p, ht, hpv, hp, hpb⟩ := h.path
  exact p.baseOnPath_outer hp t (by rw [hpv]; exact ht) hpb

theorem ne (h : IsBase M v b) : v ≠ b := by
  intro he
  have hh := h.high
  rw [he] at hh
  cases ht : tenacity M b with
  | none => simp only [ht, levelLT] at hh
  | some k =>
    have hbad : k < k := by simpa only [ht, levelLT] using hh
    omega

/-- Following a base strictly decreases minlevel, which supplies a termination
measure for iterated bases even before a global base-existence theorem is known. -/
theorem minlevel_lt (h : IsBase M v b) (k : Nat) (hk : minlevel M v = some k) :
    ∃ j, minlevel M b = some j ∧ j < k := by
  obtain ⟨t, ht, hb⟩ := h
  obtain ⟨p, hpv, hpk⟩ := minlevel_witness M v k hk
  have hp : p.Shortest := by
    refine ⟨⟨p, rfl, rfl, rfl⟩, ?_⟩
    intro l hl
    obtain ⟨q, hqv, hql, _⟩ := hl
    have hle := minlevel_le_path M v k hk q (hqv.trans hpv)
    omega
  obtain ⟨i, hi, hhigh, _⟩ := hb p hpv hp
  have hstrict : levelLT (tenacity M p.last) (tenacity M (p.vertex i)) := by
    rw [hpv, ht, hi]
    exact hhigh
  have hbm := (p.limited_bfs_honesty hp i (levelLT_le hstrict)).2 hstrict
  have hilast : i.val < p.length := by
    by_cases hilast : i.val < p.length
    · exact hilast
    · have hie : i = ⟨p.length, by omega⟩ := Fin.ext (by change i.val = p.length; omega)
      have hbv : b = v := by rw [← hi, hie]; exact hpv
      rw [hbv, ht] at hhigh
      change t < t at hhigh
      omega
  exact ⟨i.val, by simpa only [hi] using hbm, by omega⟩

end IsBase

theorem isBase_iff_common (t : Nat) (hvt : tenacity M v = some t) :
    IsBase M v b ↔ ∀ p : AltPath M, p.last = v → p.Shortest → p.BaseOnPath t b := by
  constructor
  · rintro ⟨s, hs, hb⟩
    have hst := Option.some.inj (hs.symm.trans hvt)
    exact hst ▸ hb
  · intro hb
    exact ⟨t, hvt, hb⟩

theorem isBase_exists_iff_unique (t : Nat) (hvt : tenacity M v = some t) :
    (∃ b, IsBase M v b) ↔ HasUniqueBase M v t := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, (isBase_iff_common t hvt).1 hb, ?_⟩
    intro c hc
    exact ((isBase_iff_common t hvt).2 hc).unique hb
  · rintro ⟨b, hb, _⟩
    exact ⟨b, (isBase_iff_common t hvt).2 hb⟩

/-- The partial semantic base function. It is `none` precisely when no vertex
satisfies the common-base predicate; `some` values satisfy `IsBase`. -/
noncomputable def base (M : Matching G) (v : V) : Option V := by
  classical
  exact if h : ∃ b, IsBase M v b then some (Classical.choose h) else none

theorem base_eq_some_iff (v b : V) : base M v = some b ↔ IsBase M v b := by
  classical
  unfold base
  split
  · rename_i h
    constructor
    · intro he
      exact (Option.some.inj he) ▸ Classical.choose_spec h
    · intro hb
      exact congrArg some ((Classical.choose_spec h).unique hb)
  · rename_i h
    constructor
    · intro he; contradiction
    · intro hb; exact False.elim (h ⟨b, hb⟩)

/-- The top-tenacity stratum S_(b,t) in source Definition 6.8. -/
noncomputable def BaseStratum (M : Matching G) (t : Nat) (b v : V) : Prop :=
  tenacity M v = some t ∧ IsBase M v b

/-- Source blossom recursion, with the empty base case at tenacity 1.
The zero case makes the total function explicit; source-valid indices are odd. -/
noncomputable def Blossom (M : Matching G) : Nat → V → V → Prop
  | 0, _, _ => False
  | 1, _, _ => False
  | t + 2, b, v => BaseStratum M (t + 2) b v ∨
      ∃ w, (BaseStratum M (t + 2) b w ∨ w = b) ∧ Outer M w ∧ Blossom M t w v

/-- Every blossom member has finite tenacity bounded by its index. -/
theorem blossom_tenacity_bound (t : Nat) (b v : V) (h : Blossom M t b v) :
    ∃ s, tenacity M v = some s ∧ s ≤ t := by
  induction t using Nat.strongRecOn generalizing b v with
  | ind t ih =>
    cases t with
    | zero => exact False.elim h
    | succ t =>
      cases t with
      | zero => exact False.elim h
      | succ t =>
        rcases h with hs | ⟨w, _, _, hw⟩
        · exact ⟨t + 2, hs.1, by omega⟩
        · obtain ⟨s, hs, hst⟩ := ih t (by omega) w v hw
          exact ⟨s, hs, by omega⟩

/-- A source-valid blossom excludes its own base. -/
theorem blossom_excludes_base (t : Nat) (b : V)
    (hb : levelLT (some t) (tenacity M b)) : ¬Blossom M t b b := by
  intro h
  obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound t b b h
  rw [hs] at hb
  change t < s at hb
  omega

/-- For a fixed outer base, increasing the index by two preserves membership. -/
theorem blossom_mono_step (t : Nat) (b v : V) (hb : Outer M b)
    (h : Blossom M t b v) : Blossom M (t + 2) b v :=
  Or.inr ⟨b, Or.inr rfl, hb, h⟩

/-- At globally minimum finite tenacity, the recursion has no lower members. -/
theorem minimum_blossom_iff (t : Nat) (ht : 2 ≤ t)
    (hmin : ∀ w : V, levelLE (some t) (tenacity M w)) (b v : V) :
    Blossom M t b v ↔ BaseStratum M t b v := by
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 2 := ⟨t - 2, by omega⟩
  constructor
  · intro h
    rcases h with h | ⟨w, _, _, hw⟩
    · exact h
    · obtain ⟨s, hs, hsn⟩ := blossom_tenacity_bound n w v hw
      have hm := hmin v
      rw [hs] at hm
      change n + 2 ≤ s at hm
      omega
  · exact Or.inl

/-- Distinct minimum-tenacity blossoms are disjoint, using functionality of
actual common bases. Existence is independently supplied by minimum_unique_base. -/
theorem minimum_blossoms_disjoint (t : Nat) (ht : 2 ≤ t)
    (hmin : ∀ w : V, levelLE (some t) (tenacity M w)) (b c : V) (hne : b ≠ c) :
    ∀ v, ¬(Blossom M t b v ∧ Blossom M t c v) := by
  rintro v ⟨hb, hc⟩
  exact hne (((minimum_blossom_iff t ht hmin b v).1 hb).2.unique
    ((minimum_blossom_iff t ht hmin c v).1 hc).2)

/-- Every minimum-tenacity vertex belongs to a blossom with its proved common
base, provided the nonempty source index is at least two. -/
theorem minimum_blossom_cover (t : Nat) (ht : EligibleTenacity M t) (htwo : 2 ≤ t)
    (hmin : ∀ w : V, levelLE (some t) (tenacity M w)) (v : V)
    (hvt : tenacity M v = some t) : ∃ b, Blossom M t b v ∧ IsBase M v b := by
  obtain ⟨b, hb⟩ := (isBase_exists_iff_unique t hvt).2 (minimum_unique_base M t ht hmin v hvt)
  exact ⟨b, (minimum_blossom_iff t htwo hmin b v).2 ⟨hvt, hb⟩, hb⟩

end MaximumMatching

end Blossom

section BlossomClosure

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

end BlossomClosure

section BlossomLaminar

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
        simp only [Blossom, hs, ih t (by omega)]


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

end BlossomLaminar

section BlossomCover

/-! Coverage by a unique boundary blossom from a proved base-existence
hypothesis below a specified cutoff. The premise is explicit: this is an
induction assembly lemma, not unconditional general base existence. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- If all vertices at or below an odd threshold have actual common bases,
following those bases terminates at a vertex above that threshold. The source
blossom contains the original vertex. Strictly decreasing minimum levels prove
termination even on an infinite vertex type. -/
theorem blossom_cover_of_base_existence (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b)
    (v : V) (s : Nat) (hvs : tenacity M v = some s) (hst : s ≤ t) :
    ∃ b, levelLT (some t) (tenacity M b) ∧ Blossom M t b v := by
  have aux : ∀ k (v : V) (s : Nat), minlevel M v = some k →
      tenacity M v = some s → s ≤ t →
      ∃ b, levelLT (some t) (tenacity M b) ∧ Blossom M t b v := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro v s hvk hvs hst
      obtain ⟨w, hvw⟩ := hexists v s hvs hst
      have hdirect : Blossom M t w v := blossom_of_base_le t ht w v hvw (by
        rw [hvs]; exact hst)
      cases hw : tenacity M w with
      | none => exact ⟨w, by simp only [hw, levelLT], hdirect⟩
      | some r =>
        by_cases hhigh : t < r
        · exact ⟨w, by simpa only [hw, levelLT] using hhigh, hdirect⟩
        · obtain ⟨j, hwj, hjk⟩ := hvw.minlevel_lt k hvk
          obtain ⟨b, hb, hwb⟩ := ih j hjk w r hwj hw (by omega)
          exact ⟨b, hb, blossom_downward_closed t ht b w v hwb hvw⟩
  obtain ⟨e, o, he, ho, _, _, _⟩ := finite_levels_of_tenacity v s hvs
  exact aux (min e o) v s (by simp only [minlevel, he, ho, levelMin]) hvs hst

/-- The boundary blossom supplied by coverage is unique, by the independently
proved cut/recursive-blossom laminarity theorem at a fixed threshold. -/
theorem unique_blossom_cover_of_base_existence (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b)
    (v : V) (s : Nat) (hvs : tenacity M v = some s) (hst : s ≤ t) :
    ∃ b, levelLT (some t) (tenacity M b) ∧ Blossom M t b v ∧
      ∀ c, levelLT (some t) (tenacity M c) → Blossom M t c v → c = b := by
  obtain ⟨b, hb, hvb⟩ := blossom_cover_of_base_existence t ht hexists v s hvs hst
  refine ⟨b, hb, hvb, ?_⟩
  intro c hc hvc
  apply Classical.byContradiction
  intro hne
  exact blossoms_disjoint_same_tenacity t c b hc hb hne v ⟨hvc, hvb⟩

end MaximumMatching

end BlossomCover

section BasePaths

/-! Every iterated common base occurs on every shortest path to its descendant.
Each occurrence is an even, honest minimum-level prefix. These facts follow from
the actual common-base relation and finite parent chains, without general base
existence or blossom-confinement assumptions. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A direct common base is an internal even vertex of every shortest path,
and the prefix to it attains its minimum level. -/
theorem IsBase.on_shortest {v b : V} (h : IsBase M v b)
    (p : AltPath M) (hpv : p.last = v) (hp : p.Shortest) :
    ∃ i : Fin (p.length + 1), p.vertex i = b ∧ i.val % 2 = 0 ∧ i.val < p.length ∧
      minlevel M b = some i.val ∧ (p.take i.val (by omega)).Shortest := by
  obtain ⟨t, ht, hcommon⟩ := (show IsBase M v b from h)
  have hpb := hcommon p hpv hp
  have hpt : tenacity M p.last = some t := hpv ▸ ht
  obtain ⟨i, hi, hie⟩ := p.baseOnPath_even t hpt hpb
  have hhigh : levelLT (tenacity M p.last) (tenacity M (p.vertex i)) := by
    rw [hpt, hi]
    exact hpb.choose_spec.2.1
  obtain ⟨hhon, hmin⟩ := p.limited_bfs_honesty hp i (levelLT_le hhigh)
  have hlt : i.val < p.length := by
    by_cases hlt : i.val < p.length
    · exact hlt
    · have he : i = ⟨p.length, by omega⟩ := Fin.ext (by change i.val = p.length; omega)
      have hbv : b = v := by rw [← hi, he]; exact hpv
      exact False.elim (h.ne hbv.symm)
  refine ⟨i, hi, hie, hlt, ?_, ?_⟩
  · simpa only [hi] using hmin hhigh
  · exact hhon

/-- A finite chain of actual bases propagates through the shortest prefixes.
The allowed-region predicate only specifies the chain; no property of it is
assumed in this theorem. -/
theorem base_chain_on_shortest {A : V → Prop} {b v : V}
    (h : BaseTree.Below (IsBase M) A b v)
    (p : AltPath M) (hpv : p.last = v) (hp : p.Shortest) :
    ∃ i : Fin (p.length + 1), p.vertex i = b ∧ i.val % 2 = 0 ∧ i.val < p.length ∧
      minlevel M b = some i.val ∧ (p.take i.val (by omega)).Shortest := by
  induction h generalizing p with
  | edge hbase _ => exact hbase.on_shortest p hpv hp
  | @step v w b hbase _ _ ih =>
    obtain ⟨j, hj, hje, hjlt, hjmin, hjshort⟩ := hbase.on_shortest p hpv hp
    obtain ⟨i, hi, hie, hilt, himin, hishort⟩ := ih (p.take j.val (by omega)) hj hjshort
    have hib : i.val < p.length + 1 := by
      change i.val < j.val at hilt
      omega
    refine ⟨⟨i.val, hib⟩, ?_, hie, ?_, himin, ?_⟩
    · exact hi
    · change i.val < j.val at hilt
      change i.val < p.length
      omega
    · exact hishort

/-- In particular, every threshold-cut root is an even minimum-level prefix
of every shortest path to any vertex in that cut. -/
theorem base_cut_on_shortest (t : Nat) (b v : V)
    (h : BaseTree.Cut (IsBase M) (tenacity M) t b v)
    (p : AltPath M) (hpv : p.last = v) (hp : p.Shortest) :
    ∃ i : Fin (p.length + 1), p.vertex i = b ∧ i.val % 2 = 0 ∧ i.val < p.length ∧
      minlevel M b = some i.val ∧ (p.take i.val (by omega)).Shortest :=
  base_chain_on_shortest h p hpv hp

/-- Every member of a source-recursive blossom has its base on every shortest
path, with an even minimum-level prefix. This establishes the prefix-location
part of Theorem 6.19(4), independently of the relative suffix minimality proof. -/
theorem blossom_on_shortest (t : Nat) (b v : V) (h : Blossom M t b v)
    (p : AltPath M) (hpv : p.last = v) (hp : p.Shortest) :
    ∃ i : Fin (p.length + 1), p.vertex i = b ∧ i.val % 2 = 0 ∧ i.val < p.length ∧
      minlevel M b = some i.val ∧ (p.take i.val (by omega)).Shortest :=
  base_cut_on_shortest t b v (blossom_to_cut t b v h) p hpv hp

end MaximumMatching

end BasePaths

section MinimumBlossomPaths

/-! Path confinement and edge tenacities inside minimum-tenacity blossoms. -/
namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- After a path-relative base, the global minimum-tenacity bound turns the
last-above-threshold condition into equality of tenacity. -/
theorem minimum_after_base_tenacity (p : AltPath M) (t : Nat)
    (hmin : ∀ v : V, levelLE (some t) (tenacity M v)) (b : V)
    (hb : p.BaseOnPath t b) (i j : Fin (p.length + 1))
    (hib : p.vertex i = b) (hij : i.val < j.val) :
    tenacity M (p.vertex j) = some t := by
  obtain ⟨k, hkb, _, hlast⟩ := hb
  have hik : i = k := p.injective _ _ (hib.trans hkb.symm)
  have hj := hlast j (by rw [← hik]; exact hij)
  have hm := hmin (p.vertex j)
  cases ht : tenacity M (p.vertex j) with
  | none => exact False.elim (hj (by rw [ht]; trivial))
  | some s =>
    have hts : t ≤ s := by simpa only [ht, levelLE] using hm
    have hst : ¬t < s := by simpa only [ht, levelLT] using hj
    exact congrArg some (by omega)

/-- Restricting a path after its base preserves that base. -/
theorem baseOnPath_take_after (p : AltPath M) (t : Nat) (b : V)
    (hb : p.BaseOnPath t b) (i j : Fin (p.length + 1))
    (hib : p.vertex i = b) (hij : i.val ≤ j.val) :
    (p.take j.val (by omega)).BaseOnPath t b := by
  obtain ⟨k, hkb, hhigh, hlast⟩ := hb
  have hik : i = k := p.injective _ _ (hib.trans hkb.symm)
  refine ⟨⟨i.val, by change i.val < j.val + 1; omega⟩, hib, hhigh, ?_⟩
  intro a ha
  exact hlast ⟨a.val, by have := a.isLt; change a.val < j.val + 1 at this; omega⟩
    (by
      change i.val < a.val at ha
      change k.val < a.val
      have hki := congrArg Fin.val hik
      omega)

/-- At minimum tenacity every vertex after the base has that same actual common
base, by applying the proved minimum-base theorem to the honest prefix. -/
theorem minimum_suffix_base (p : AltPath M) (hp : p.Shortest) (t : Nat)
    (ht : EligibleTenacity M t) (hpt : tenacity M p.last = some t)
    (hmin : ∀ v : V, levelLE (some t) (tenacity M v)) (b : V)
    (hb : p.BaseOnPath t b) (i j : Fin (p.length + 1))
    (hib : p.vertex i = b) (hij : i.val < j.val) :
    IsBase M (p.vertex j) b := by
  have hjt := p.minimum_after_base_tenacity t hmin b hb i j hib hij
  have hq := p.prefixes_honest_at_minimum hp t hpt hmin j
  have hqshort : (p.take j.val (by omega)).Shortest := by
    unfold Shortest
    rw [take_length, take_last]
    exact (level_eq_some_iff M _ _ _).1 ((p.honest_iff_level j).1 hq)
  have hqb := p.baseOnPath_take_after t b hb i j hib (by omega)
  obtain ⟨c, hc, _⟩ := minimum_unique_base M t ht hmin (p.vertex j) hjt
  have hqc := hc (p.take j.val (by omega)) rfl hqshort
  have hbc := (p.take j.val (by omega)).baseOnPath_unique t b c hqb hqc
  exact ⟨t, hjt, hbc.symm ▸ hc⟩

/-- Every vertex after the base of a minimum-tenacity shortest path belongs to
that source blossom. This proves the path-confinement part of the induction basis. -/
theorem minimum_suffix_in_blossom (p : AltPath M) (hp : p.Shortest) (t : Nat)
    (ht : EligibleTenacity M t) (hpt : tenacity M p.last = some t)
    (hmin : ∀ v : V, levelLE (some t) (tenacity M v)) (b : V)
    (hb : p.BaseOnPath t b) (i j : Fin (p.length + 1))
    (hib : p.vertex i = b) (hij : i.val < j.val) :
    Blossom M t b (p.vertex j) := by
  have hjb := p.minimum_suffix_base hp t ht hpt hmin b hb i j hib hij
  have hjt := p.minimum_after_base_tenacity t hmin b hb i j hib hij
  exact blossom_of_base_le t ht.1 b (p.vertex j) hjb (by rw [hjt]; exact Nat.le_refl t)

/-- Every edge after the base has exactly the minimum tenacity, including the
first unmatched edge leaving the base. This applies to either endpoint parity. -/
theorem minimum_suffix_edge_tenacity (p : AltPath M) (hp : p.Shortest) (t : Nat)
    (hpt : tenacity M p.last = some t)
    (hmin : ∀ v : V, levelLE (some t) (tenacity M v)) (b : V)
    (hb : p.BaseOnPath t b) (i : Fin (p.length + 1)) (hib : p.vertex i = b)
    (k : Fin p.length) (hik : i.val ≤ k.val) :
    edgeTenacity M (p.vertex ⟨k.val, by omega⟩) (p.vertex ⟨k.val + 1, by omega⟩) = some t := by
  let u := p.vertex ⟨k.val, by omega⟩
  let w := p.vertex ⟨k.val + 1, by omega⟩
  have hwt : tenacity M w = some t :=
    p.minimum_after_base_tenacity t hmin b hb i ⟨k.val + 1, by omega⟩ hib (by change i.val < k.val + 1; omega)
  have hm := p.alternating k
  change edgeTenacity M u w = some t
  unfold edgeTenacity
  by_cases hmatch : M.mate u = some w
  · rw [ite_eq_left hmatch, ← (matched_tenacity M hmatch).2, hwt]
  · rw [ite_eq_right hmatch]
    have hke : k.val % 2 = 0 := by
      have hn : ¬ k.val % 2 = 1 := fun h => hmatch (hm.2 h)
      omega
    have hhu := (p.honest_iff_level ⟨k.val, by omega⟩).1
      (p.prefixes_honest_at_minimum hp t hpt hmin _)
    have hhw := (p.honest_iff_level ⟨k.val + 1, by omega⟩).1
      (p.prefixes_honest_at_minimum hp t hpt hmin _)
    have hue : evenlevel M u = some k.val := by simpa only [hke] using hhu
    have hwo : oddlevel M w = some (k.val + 1) := by
      simpa only [show (k.val + 1) % 2 = 1 by omega] using hhw
    obtain ⟨e, o, he, ho, _, _, hsum⟩ := finite_levels_of_tenacity w t hwt
    have hoeq : o = k.val + 1 := Option.some.inj (ho.symm.trans hwo)
    rw [hue, he]
    simp only [levelAdd, Option.map_some]
    exact congrArg some (by omega)

end AltPath
end MaximumMatching

end MinimumBlossomPaths
