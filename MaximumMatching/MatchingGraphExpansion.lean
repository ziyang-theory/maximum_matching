import MaximumMatching.MatchingSearchGraph
import MaximumMatching.PredecessorExpansion
import MaximumMatching.WeightedTopExpansion

/-! Expand the actual predecessor/bud graph when its assigned fibers represent
lower blossoms. This is the representation before same-level petals have been
formed; preservation through those petals is a separate obligation. Edge
segments, their phases, and their exact weights are constructed here. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

/-- Mathematical representation of assigned bud fibers at a fixed lower cut.
This does not identify a same-level petal with a whole mathematical blossom. -/
def LowerBlossomRepresentation (M : Matching G) (cut : Nat) (s : State V)
    (F : BudForest V) : Prop :=
  ∀ v k, s.minLabel v = some k →
    levelLT (some cut) (tenacity M (F.root v)) ∧
      (v = F.root v ∨ Blossom M cut (F.root v) v)

namespace BudGraphInvariant
variable {cap cut : Nat} {s : State V} {F : BudForest V}

/-- Each actual list-derived edge has a real matching-path expansion.
The half-tenacity bound is the search-stage bound, and the representation
premise concerns only the current lower-blossom fibers. -/
theorem edge_expansion (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut < p.length)
    (hhalf : 2 * cap ≤ cut + 3) (hrep : LowerBlossomRepresentation M cut s F)
    {v w : V} (he : (predecessorGraph s F h).Edge v w) :
    ∃ a : ParitySegment M, a.first = v ∧ a.last = w ∧
      a.length + (s.minLabel w).getD 0 = (s.minLabel v).getD 0 ∧
      a.phase % 2 = ((s.minLabel v).getD 0 + 1) % 2 ∧
      (a.phase + a.length) % 2 = ((s.minLabel w).getD 0 + 1) % 2 ∧
      (∀ k : Fin (a.length + 1), 0 < k.val → k.val < a.length →
        Blossom M cut w (a.vertex k)) := by
  obtain ⟨u, N, j, hv, hu, hp, rfl, hjN⟩ := h.edge_witness he
  obtain ⟨B, hB⟩ := h.rootAssigned u j hu
  have hNm := h.minInvariant.1.1 v N hv
  have hBm := h.minInvariant.1.1 (F.root u) B hB
  obtain ⟨hbhigh, hufiber⟩ := hrep u j hu
  have hbound : 2 * (N - 1) ≤ cut + 1 := by
    have := h.labelsBounded v N hv
    omega
  rcases hufiber with hueq | hubl
  · have hh := predecessor_direct_expansion cut hc u v hp
      (by rw [hueq]; exact hbhigh) N B hNm (by rw [hueq]; exact hBm) hbound
    obtain ⟨a, haf, hal, han, hap, hae, hai⟩ := hh
    refine ⟨a, haf, hal.trans hueq, ?_, ?_, ?_, ?_⟩
    · simpa only [hv, hB, Option.getD_some] using han
    · simpa only [hv, Option.getD_some] using hap
    · simpa only [hB, Option.getD_some] using hae
    · intro k hk hkl
      exact hueq ▸ hai k hk hkl
  · obtain ⟨a, ha, hac⟩ := blossom_tenacity_bound cut (F.root u) u hubl
    have helig : EligibleTenacity M cut :=
      ⟨hc, ⟨u, by simpa only [ha, levelLE] using hac⟩, hnoaug⟩
    obtain ⟨a, haf, hal, han, hap, hae, hai⟩ :=
      predecessor_blossom_expansion cut helig u v (F.root u) hp hubl hbhigh N B hNm hBm
    exact ⟨a, haf, hal, by simpa only [hv, hB, Option.getD_some] using han,
      by simpa only [hv, Option.getD_some] using hap,
      by simpa only [hB, Option.getD_some] using hae, hai⟩

/-- The weighted realization is selected from the actual predecessor-edge
witnesses proved above, not supplied as a path-expansion oracle. -/
noncomputable def weightedMatching (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut < p.length)
    (hhalf : 2 * cap ≤ cut + 3) (hrep : LowerBlossomRepresentation M cut s F) :
    DDFS.BlossomWeightedMatching M (predecessorGraph s F h) cut where
  phase v := (s.minLabel v).getD 0 + 1
  segment he := Classical.choose (h.edge_expansion hc hnoaug hhalf hrep he)
  first he := (Classical.choose_spec (h.edge_expansion hc hnoaug hhalf hrep he)).1
  last he := (Classical.choose_spec (h.edge_expansion hc hnoaug hhalf hrep he)).2.1
  start_phase he := (Classical.choose_spec (h.edge_expansion hc hnoaug hhalf hrep he)).2.2.2.1
  end_phase he := (Classical.choose_spec (h.edge_expansion hc hnoaug hhalf hrep he)).2.2.2.2.1
  interior he := (Classical.choose_spec (h.edge_expansion hc hnoaug hhalf hrep he)).2.2.2.2.2

theorem weightedMatching_drop (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut < p.length)
    (hhalf : 2 * cap ≤ cut + 3) (hrep : LowerBlossomRepresentation M cut s F)
    {v w : V} (he : (predecessorGraph s F h).Edge v w) :
    ((h.weightedMatching hc hnoaug hhalf hrep).segment he).length +
      (s.minLabel w).getD 0 = (s.minLabel v).getD 0 :=
  (Classical.choose_spec (h.edge_expansion hc hnoaug hhalf hrep he)).2.2.1

/-- Root-started active paths have only genuine high-tenacity core vertices. -/
theorem path_high (h : BudGraphInvariant M cap s F)
    (hrep : LowerBlossomRepresentation M cut s F)
    (p : DDFS.Path (predecessorGraph s F h))
    (hfixed : F.parent p.first = p.first)
    (hassigned : ∃ k, s.minLabel p.first = some k) :
    ∀ v, p.Contains v → levelLT (some cut) (tenacity M v) := by
  rintro v ⟨j, rfl⟩
  obtain ⟨k, hk⟩ := h.path_assigned p hassigned j
  have hh := (hrep (p.vertex j) k hk).1
  rwa [F.root_of_fixed _ (h.path_fixed p hfixed j)] at hh

/-- An actual root-to-bottom graph path expands, in reverse, to a genuine
minimum-level alternating path. The matching-path length is derived from
constructed edge weights and the stored endpoint levels. -/
theorem realize_bottom_path (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut < p.length)
    (hhalf : 2 * cap ≤ cut + 3) (hrep : LowerBlossomRepresentation M cut s F)
    (p : DDFS.Path (predecessorGraph s F h))
    (hfixed : F.parent p.first = p.first)
    (hassigned : ∃ k, s.minLabel p.first = some k)
    (hbottom : (predecessorGraph s F h).level p.last = 0) :
    ∃ q : AltPath M, q.first = p.last ∧ q.last = p.first ∧
      q.length = (s.minLabel p.first).getD 0 ∧
      minlevel M q.last = some q.length ∧
      (∀ v, (∃ j, q.vertex j = v) → BlossomHull M cut p.Contains v) := by
  let W := h.weightedMatching hc hnoaug hhalf hrep
  have hhigh := h.path_high hrep p hfixed hassigned
  have hp : W.phase p.last % 2 = 1 := by
    change ((s.minLabel p.last).getD 0 + 1) % 2 = 1
    change (s.minLabel p.last).getD 0 = 0 at hbottom
    simp only [hbottom]
  obtain ⟨a, haf, hal, han, hah⟩ := W.realize_reverse_altSegment p hhigh hp
  have hfree : M.Free a.first := haf ▸ h.path_bottom_free p hassigned hbottom
  let q := a.fromFree hfree
  have hqn : q.length = (s.minLabel p.first).getD 0 := by
    have he := W.weight_add_potential (fun v => (s.minLabel v).getD 0)
      (fun he => h.weightedMatching_drop hc hnoaug hhalf hrep he) p
    change (s.minLabel p.last).getD 0 = 0 at hbottom
    change a.length = _
    omega
  refine ⟨q, haf, hal, hqn, ?_, hah⟩
  obtain ⟨k, hk⟩ := hassigned
  have hm := h.minInvariant.1.1 p.first k hk
  have hqk : q.length = k := by simpa only [hk, Option.getD_some] using hqn
  have hql : q.last = p.first := hal
  rw [hql, hqk]
  exact hm

end BudGraphInvariant
end MaximumMatching.Search
