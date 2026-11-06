import MaximumMatching.GeneralEdgeBoundStep

/-! Every edge on an actual shortest relative blossom path has tenacity at most
its eligible cutoff. Strong cutoff induction closes the global and relative
edge bounds together, using the already proved base and confinement theorems. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V}

/-- Joint global and relative edge bounds at every eligible cutoff. -/
theorem general_blossom_edge_bounds (M : Matching G) : ∀ t : Nat, EligibleTenacity M t →
    (∀ (p : AltPath M), p.Shortest → ∀ (b : V), levelLT (some t) (tenacity M b) →
      Blossom M t b p.last → ∀ i : Fin (p.length + 1), p.vertex i = b →
      ∀ k : Fin p.length, i.val ≤ k.val →
        levelLE (edgeTenacity M (p.vertex ⟨k.val, by omega⟩) (p.vertex ⟨k.val + 1, by omega⟩)) (some t)) ∧
    (∀ (b v : V), Blossom M t b v → levelLT (some t) (tenacity M b) →
      ∀ (q : AltSegment M), q.Shortest → q.first = b → q.last = v → ∀ k : Fin q.length,
        levelLE (edgeTenacity M (q.vertex ⟨k.val, by omega⟩) (q.vertex ⟨k.val + 1, by omega⟩)) (some t)) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro ht
    have hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b := by
      intro v s hs hst
      have helig : EligibleTenacity M s := by
        refine ⟨tenacity_odd M v s hs, ⟨v, ?_⟩, ?_⟩
        · rw [hs]
          exact Nat.le_refl _
        · intro p hp
          have := ht.2.2 p hp
          omega
      obtain ⟨b, hb, _⟩ := general_unique_base M s helig v hs
      exact ⟨b, s, hs, hb⟩
    have lowEligible (b v : V) (hv : Blossom M (t - 2) b v) : EligibleTenacity M (t - 2) := by
      obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound (t - 2) b v hv
      have hsodd := tenacity_odd M v s hs
      refine ⟨by have := ht.1; omega, ⟨v, ?_⟩, ?_⟩
      · rw [hs]
        exact hst
      · intro p hp
        have := ht.2.2 p hp
        omega
    have hlowlt : t - 2 < t := by have := ht.1; omega
    have hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
        ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
          ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w := by
      intro b v hv hb q hq hqb hqv
      exact general_blossom_relative_confined M (t - 2) (lowEligible b v hv) b v hv hb q hq hqb hqv
    have hlow : ∀ (p : AltPath M), p.Shortest →
        ∀ (b : V), levelLT (some (t - 2)) (tenacity M b) → Blossom M (t - 2) b p.last →
        ∀ (i : Fin (p.length + 1)), p.vertex i = b → ∀ k : Fin p.length, i.val ≤ k.val →
          levelLE (edgeTenacity M (p.vertex ⟨k.val, by omega⟩) (p.vertex ⟨k.val + 1, by omega⟩)) (some (t - 2)) := by
      intro p hp b hb hv i hi k hik
      exact (ih (t - 2) hlowlt (lowEligible b p.last hv)).1 p hp b hb hv i hi k hik
    have hlowrel : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
        ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v → ∀ k : Fin q.length,
          levelLE (edgeTenacity M (q.vertex ⟨k.val, by omega⟩) (q.vertex ⟨k.val + 1, by omega⟩)) (some (t - 2)) := by
      intro b v hv hb q hq hqb hqv k
      exact (ih (t - 2) hlowlt (lowEligible b v hv)).2 b v hv hb q hq hqb hqv k
    have hglobal : ∀ (p : AltPath M), p.Shortest → ∀ (b : V), levelLT (some t) (tenacity M b) →
        Blossom M t b p.last → ∀ i : Fin (p.length + 1), p.vertex i = b →
        ∀ k : Fin p.length, i.val ≤ k.val →
          levelLE (edgeTenacity M (p.vertex ⟨k.val, by omega⟩) (p.vertex ⟨k.val + 1, by omega⟩)) (some t) := by
      intro p hp b hb hv i hi k hik
      exact AltPath.general_blossom_suffix_edge_step t ht.1 hexists hconf hlow hlowrel p hp b hb hv i hi k hik
    refine ⟨hglobal, ?_⟩
    intro b v hv hb q hq hqb hqv k
    apply blossom_relative_edge_bound_of_global t b v hv hb ?_ q hq hqb hqv k
    intro p hp hpv i hi j hij
    exact hglobal p hp b hb (by rw [hpv]; exact hv) i hi j hij

namespace AltPath
variable {M : Matching G}

/-- Every edge at or after the actual boundary on a shortest path to a blossom
member has finite edge tenacity no greater than the eligible cutoff. -/
theorem general_blossom_suffix_edge_bound (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (ht : EligibleTenacity M t) (b : V)
    (hb : levelLT (some t) (tenacity M b)) (hv : Blossom M t b p.last)
    (i : Fin (p.length + 1)) (hi : p.vertex i = b) (k : Fin p.length) (hik : i.val ≤ k.val) :
    levelLE (edgeTenacity M (p.vertex ⟨k.val, by omega⟩) (p.vertex ⟨k.val + 1, by omega⟩)) (some t) :=
  (general_blossom_edge_bounds M t ht).1 p hp b hb hv i hi k hik

end AltPath

/-- The edge-tenacity clause of Theorem 6.19(4) for every eligible cutoff and
every shortest relative path, with no lower-bound oracle left as a premise. -/
theorem general_blossom_relative_edge_bound (M : Matching G) (t : Nat) (ht : EligibleTenacity M t)
    (b v : V) (hv : Blossom M t b v) (hb : levelLT (some t) (tenacity M b))
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v)
    (k : Fin q.length) :
    levelLE (edgeTenacity M (q.vertex ⟨k.val, by omega⟩) (q.vertex ⟨k.val + 1, by omega⟩)) (some t) :=
  (general_blossom_edge_bounds M t ht).2 b v hv hb q hq hqb hqv k

end MaximumMatching
