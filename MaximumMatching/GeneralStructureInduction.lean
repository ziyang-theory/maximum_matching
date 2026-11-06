import MaximumMatching.GeneralStructureBase
import MaximumMatching.GeneralConfinement

/-! Strong induction on eligible tenacity closes both common-base existence and
actual relative-path blossom confinement. Every lower induction hypothesis is
instantiated from the requested eligible cutoff and an actual finite member. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V}

/-- The simultaneous general common-base and blossom-confinement theorem. -/
theorem general_base_and_confinement (M : Matching G) : ∀ t : Nat,
    EligibleTenacity M t →
      (∀ v : V, tenacity M v = some t → HasUniqueBase M v t) ∧
      (∀ (b v : V), Blossom M t b v → levelLT (some t) (tenacity M b) →
        ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
          ∀ w, q.Contains w → w = b ∨ Blossom M t b w) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro ht
    have hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 →
        ∃ b, IsBase M v b := by
      intro v s hs hst
      have hsodd := tenacity_odd M v s hs
      have hst' : s < t := by have := ht.1; omega
      have helig : EligibleTenacity M s := by
        refine ⟨hsodd, ⟨v, ?_⟩, ?_⟩
        · rw [hs]
          exact Nat.le_refl _
        · intro p hp
          have htl := ht.2.2 p hp
          omega
      obtain ⟨b, hb, _⟩ := (ih s hst' helig).1 v hs
      exact ⟨b, s, hs, hb⟩
    have hconf : ∀ (b v : V), Blossom M (t - 2) b v →
        levelLT (some (t - 2)) (tenacity M b) →
        ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
          ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w := by
      intro b v hv hb q hq hqb hqv w hw
      obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound (t - 2) b v hv
      have hsodd := tenacity_odd M v s hs
      have hlt : t - 2 < t := by have := ht.1; omega
      have helig : EligibleTenacity M (t - 2) := by
        refine ⟨by have := ht.1; omega, ⟨v, ?_⟩, ?_⟩
        · rw [hs]
          exact hst
        · intro p hp
          have htl := ht.2.2 p hp
          omega
      exact (ih (t - 2) hlt helig).2 b v hv hb q hq hqb hqv w hw
    have hbase : ∀ v : V, tenacity M v = some t → HasUniqueBase M v t :=
      fun v hv => general_unique_base_of_lower M t ht hexists hconf v hv
    have hcurrent : ∀ v : V, tenacity M v = some t → ∃ b, IsBase M v b := by
      intro v hv
      obtain ⟨b, hb, _⟩ := hbase v hv
      exact ⟨b, t, hv, hb⟩
    refine ⟨hbase, ?_⟩
    intro b v hv hb q hq hqb hqv
    exact general_blossom_relative_confined_of_current t ht.1 hexists hconf hcurrent
      b v hv hb q hq hqb hqv

/-- Every vertex of eligible tenacity has a unique common base, with no
unproved structural premise or lower-tenacity oracle. -/
theorem general_unique_base (M : Matching G) (t : Nat) (ht : EligibleTenacity M t)
    (v : V) (hvt : tenacity M v = some t) : HasUniqueBase M v t :=
  (general_base_and_confinement M t ht).1 v hvt

/-- Every shortest relative path to a blossom member stays within that blossom
and its boundary, at every eligible cutoff. -/
theorem general_blossom_relative_confined (M : Matching G) (t : Nat) (ht : EligibleTenacity M t)
    (b v : V) (hv : Blossom M t b v) (hb : levelLT (some t) (tenacity M b))
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v) :
    ∀ w, q.Contains w → w = b ∨ Blossom M t b w :=
  (general_base_and_confinement M t ht).2 b v hv hb q hq hqb hqv

end MaximumMatching
