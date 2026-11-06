import MaximumMatching.BasePathTransfer
import MaximumMatching.MatchingSearchGraph
import MaximumMatching.WeightedPaths
import MaximumMatching.WeightedRecovery

section MatchingGraphExpansion

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

end MatchingGraphExpansion

section MatchingFiberExpansion

/-! Initialize actual fiber-based path expansion from lower-blossom
representation. MIN coverage forces every lower-blossom member into the
unique represented fiber, so segment containment is derived for all original
vertices, not merely assumed for those already named by a DDFS path. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}
namespace BudGraphInvariant
variable {cap cut : Nat} {s : State V} {F : BudForest V}

/-- At the actual search-stage range, all vertices in a lower blossom are
assigned by MIN and belong to its represented root's exact fiber. -/
theorem lower_blossom_fiber (h : BudGraphInvariant M cap s F)
    (hcap : cut ≤ 2 * cap + 1) (hrep : LowerBlossomRepresentation M cut s F)
    (b v : V) (hb : levelLT (some cut) (tenacity M b)) (hbl : Blossom M cut b v) :
    F.root v = b := by
  obtain ⟨t, hvt, htc⟩ := blossom_tenacity_bound cut b v hbl
  obtain ⟨e, o, he, ho, hep, hop, hsum⟩ := finite_levels_of_tenacity v t hvt
  have hmin : minlevel M v = some (min e o) := by simp only [minlevel, he, ho, levelMin]
  have hbound : min e o ≤ cap := by omega
  have hv : s.minLabel v = some (min e o) := h.minInvariant.2.1 v (min e o) hmin hbound
  obtain ⟨hrhigh, hvfiber⟩ := hrep v (min e o) hv
  rcases hvfiber with hvr | hvbl
  · rw [← hvr, hvt] at hrhigh
    change cut < t at hrhigh
    omega
  · by_cases heq : F.root v = b
    · exact heq
    · exact False.elim (blossoms_disjoint_same_tenacity cut (F.root v) b
        hrhigh hb heq v ⟨hvbl, hbl⟩)

/-- Instantiate the fiber interface from constructed predecessor segments.
This establishes the starting representation before same-level petal updates. -/
noncomputable def fiberWeightedMatching (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut < p.length)
    (hhalf : 2 * cap ≤ cut + 3) (hcap : cut ≤ 2 * cap + 1)
    (hrep : LowerBlossomRepresentation M cut s F) :
    DDFS.FiberWeightedMatching M (predecessorGraph s F h) F where
  phase := (h.weightedMatching hc hnoaug hhalf hrep).phase
  segment := (h.weightedMatching hc hnoaug hhalf hrep).segment
  first := (h.weightedMatching hc hnoaug hhalf hrep).first
  last := (h.weightedMatching hc hnoaug hhalf hrep).last
  start_phase := (h.weightedMatching hc hnoaug hhalf hrep).start_phase
  end_phase := (h.weightedMatching hc hnoaug hhalf hrep).end_phase
  interior := by
    intro u v he i hi hil
    obtain ⟨k, hk⟩ := h.edge_target_assigned he
    have hv : levelLT (some cut) (tenacity M v) := by
      have hh := (hrep v k hk).1
      rwa [F.root_of_fixed v (h.edge_target_fixed he)] at hh
    exact h.lower_blossom_fiber hcap hrep v _ hv
      ((h.weightedMatching hc hnoaug hhalf hrep).interior he i hi hil)

theorem fiberWeightedMatching_drop (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut < p.length)
    (hhalf : 2 * cap ≤ cut + 3) (hcap : cut ≤ 2 * cap + 1)
    (hrep : LowerBlossomRepresentation M cut s F)
    {u v : V} (he : (predecessorGraph s F h).Edge u v) :
    ((h.fiberWeightedMatching hc hnoaug hhalf hcap hrep).segment he).length +
      (s.minLabel v).getD 0 = (s.minLabel u).getD 0 :=
  h.weightedMatching_drop hc hnoaug hhalf hrep he

end BudGraphInvariant
end MaximumMatching.Search

end MatchingFiberExpansion

section FirstBridge

/-! The first search-level boundary. Tenacity-one edges join free vertices
and give executable length-one augmenting paths; they require no blossom
expansion or artificial negative lower cutoff. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

theorem edge_tenacity_one_iff_free (u v : V) :
    edgeTenacity M u v = some 1 ↔ M.Free u ∧ M.Free v := by
  classical
  constructor
  · intro ht
    by_cases hm : M.mate u = some v
    · have hh : (levelAdd (oddlevel M u) (oddlevel M v)).map (· + 1) = some 1 := by
        simpa only [edgeTenacity, ite_eq_left hm, matchedEdgeTenacity] using ht
      cases hu : oddlevel M u with
      | none => simp only [hu, levelAdd, Option.map_none] at hh; contradiction
      | some a =>
        cases hv : oddlevel M v with
        | none => simp only [hu, hv, levelAdd, Option.map_none] at hh; contradiction
        | some b =>
          have ha := level_parity M 1 u a hu
          have hab : a + b + 1 = 1 := by
            simpa only [hu, hv, levelAdd, Option.map_some, Option.some.injEq] using hh
          omega
    · have hh : (levelAdd (evenlevel M u) (evenlevel M v)).map (· + 1) = some 1 := by
        simpa only [edgeTenacity, ite_eq_right hm] using ht
      cases hu : evenlevel M u with
      | none => simp only [hu, levelAdd, Option.map_none] at hh; contradiction
      | some a =>
        cases hv : evenlevel M v with
        | none => simp only [hu, hv, levelAdd, Option.map_none] at hh; contradiction
        | some b =>
          have hab : a + b + 1 = 1 := by
            simpa only [hu, hv, levelAdd, Option.map_some, Option.some.injEq] using hh
          exact ⟨(evenlevel_zero_iff_free M u).1 (by simpa only [show a = 0 by omega] using hu),
            (evenlevel_zero_iff_free M v).1 (by simpa only [show b = 0 by omega] using hv)⟩
  · rintro ⟨hu, hv⟩
    have hm : M.mate u ≠ some v := by rw [hu]; intro h; contradiction
    simp only [edgeTenacity, ite_eq_right hm, (evenlevel_zero_iff_free M u).2 hu,
      (evenlevel_zero_iff_free M v).2 hv, levelAdd, Option.map_some]

namespace AltPath

/-- Execute a one-edge augmentation witness directly from its free ends. -/
def freeEdge (u v : V) (hu : M.Free u) (hadj : G.Adj u v) : AltPath M :=
  (trivial M u hu).append v
    (fun _ he => G.loopless v (he ▸ hadj)) hadj
    (by change M.mate u = some v ↔ 0 % 2 = 1; rw [hu]; simp)

theorem freeEdge_augmenting (u v : V) (hu : M.Free u) (hv : M.Free v) (hadj : G.Adj u v) :
    (freeEdge u v hu hadj).Augmenting :=
  ⟨rfl, hv⟩

theorem freeEdge_contains (u v : V) (hu : M.Free u) (hadj : G.Adj u v) :
    (freeEdge u v hu hadj).ContainsEdge u v :=
  ⟨⟨0, by change 0 < 1; omega⟩, Or.inl ⟨rfl, rfl⟩⟩

end AltPath

/-- The entire tenacity-one bridge case has a real shortest augmenting
witness independently of the later odd-cutoff blossom representation. -/
theorem tenacity_one_bridge_augmenting (u v : V) (hb : Bridge M u v)
    (ht : edgeTenacity M u v = some 1) :
    ∃ p : AltPath M, p.Augmenting ∧ p.length = 1 ∧ p.ContainsEdge u v ∧
      ∀ q : AltPath M, q.Augmenting → p.length ≤ q.length := by
  obtain ⟨hu, hv⟩ := (edge_tenacity_one_iff_free u v).1 ht
  exact ⟨AltPath.freeEdge u v hu hb.1, AltPath.freeEdge_augmenting u v hu hv hb.1,
    rfl, AltPath.freeEdge_contains u v hu hb.1, fun q hq => q.augmenting_pos hq⟩

/-- Once length-one augmenting paths are absent, every vertex is above cut
one. Thus a singleton bud forest really represents the first lower cutoff. -/
theorem tenacity_above_one_of_no_short_augmenting
    (hnoaug : ∀ p : AltPath M, p.Augmenting → 1 < p.length) (v : V) :
    levelLT (some 1) (tenacity M v) := by
  cases ht : tenacity M v with
  | none => trivial
  | some t =>
    by_cases hlarge : 1 < t
    · exact hlarge
    · obtain ⟨e, o, he, _, hep, hop, hsum⟩ := finite_levels_of_tenacity v t ht
      have he0 : e = 0 := by omega
      have hf : M.Free v := (evenlevel_zero_iff_free M v).1 (by simpa only [he0] using he)
      have hh := free_tenacity_above M 1 v hf hnoaug
      rw [ht] at hh
      exact hh

namespace Search
variable [DecidableEq V]

theorem uncontracted_lower_representation_one (s : State V)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → 1 < p.length) :
    LowerBlossomRepresentation M 1 s (uncontractedForest s) := by
  intro v k _
  rw [(uncontractedForest s).root_of_fixed v rfl]
  exact ⟨tenacity_above_one_of_no_short_augmenting hnoaug v, Or.inl rfl⟩

end Search
end MaximumMatching

end FirstBridge
