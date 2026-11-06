import MaximumMatching.MinimumBase

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
