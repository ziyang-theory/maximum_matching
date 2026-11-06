import MaximumMatching.BridgeBuckets
import MaximumMatching.DDFSBud
import MaximumMatching.DDFSTrees
import MaximumMatching.GeneralEdgeGeometry
import MaximumMatching.MatchingGraphExpansion
import MaximumMatching.MatchingSearchGraph
import MaximumMatching.WeightedPaths
import MaximumMatching.WeightedRecovery

section BridgeTopSegments

/-! Construct the two real endpoint-to-bud paths for a bridge at the next
odd tenacity. These use current lower-blossom fibers and semantic bridge
classification; no endpoint path or length budget is supplied by the caller. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The unmatched-bridge endpoint uses its even relative path. A high
uncontracted endpoint is necessarily outer; a low endpoint uses its actual
lower-blossom even path. -/
theorem unmatched_bridge_top_segment (cut : Nat) (hc : cut % 2 = 1)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut < p.length)
    (u v b : V) (hbridge : Bridge M u v) (hm : M.mate u ≠ some v)
    (ht : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hb : levelLT (some cut) (tenacity M b))
    (hfiber : u = b ∨ Blossom M cut b u)
    (E B : Nat) (hE : evenlevel M u = some E) (hB : minlevel M b = some B) :
    ∃ a : ParitySegment M, a.first = u ∧ a.last = b ∧ a.length + B = E ∧
      a.phase % 2 = 1 ∧ (a.phase + a.length) % 2 = (B + 1) % 2 ∧
      (∀ k : Fin (a.length + 1), k.val < a.length →
        Blossom M cut b (a.vertex k)) := by
  rcases hfiber with rfl | hbl
  · have houter : Outer M u := by
      apply Classical.byContradiction
      intro hn
      have hEp := level_parity M 0 u E hE
      obtain ⟨k, hk, _⟩ := minlevel_le_of_level u E (by simpa only [hEp] using hE)
      obtain ⟨t, ht', htc⟩ := (unmatched_bridge_tenacity hbridge hm (cut + 2) ht).2 ⟨⟨k, hk⟩, hn⟩
      have hto := tenacity_odd M u t ht'
      rw [ht'] at hb
      change cut < t at hb
      omega
    have hBE : B = E := Option.some.inj
      (hB.symm.trans ((minlevel_eq_even_of_outer u houter).trans hE))
    have hBp : B % 2 = 0 := by have := level_parity M 0 u E hE; omega
    refine ⟨ParitySegment.trivial M u 1, rfl, rfl, ?_, rfl, ?_, ?_⟩
    · change 0 + B = E
      omega
    · change (1 + 0) % 2 = (B + 1) % 2
      omega
    · intro k hk
      change k.val < 0 at hk
      omega
  · obtain ⟨t, hut, htc⟩ := blossom_tenacity_bound cut b u hbl
    have helig : EligibleTenacity M cut := ⟨hc, ⟨u, by simpa only [hut, levelLE] using htc⟩, hnoaug⟩
    have hconf := general_blossom_relative_confined M cut helig b u hbl hb
    obtain ⟨a, haf, hal, han, hap, hae, hai⟩ := blossom_even_top_segment cut b u hbl hb hconf E B hE hB
    have hBe : evenlevel M b = some B := (minlevel_eq_even_of_outer b (blossom_outer cut b u hbl)).symm.trans hB
    have hBp := level_parity M 0 b B hBe
    have hBE : B ≤ E := by
      obtain ⟨p, hp, hl, hpar⟩ := ((level_eq_some_iff M 0 u E).1 hE).1
      have hps : p.Shortest := by
        simpa only [AltPath.Shortest, hp, hl, hpar] using (level_eq_some_iff M 0 u E).1 hE
      obtain ⟨i, _, _, _, himin, _⟩ := blossom_on_shortest cut b u hbl p hp hps
      have hiB := Option.some.inj (himin.symm.trans hB)
      have := i.isLt
      omega
    exact ⟨a, haf, hal, by omega, hap, by omega, hai⟩

end MaximumMatching

namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}
namespace BudGraphInvariant
variable {cap cut : Nat} {s : State V} {F : BudForest V}

/-- Actual bridge endpoint paths with all phase and total-budget equations
needed for weighted DDFS path lifting. The lower representation is explicit;
no same-level petal is identified with a whole mathematical blossom. -/
theorem bridge_top_segments (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut < p.length)
    (hrep : LowerBlossomRepresentation M cut s F)
    (u v : V) (hbridge : Bridge M u v) (ht : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, s.minLabel u = some k) (hv : ∃ k, s.minLabel v = some k) :
    ∃ a b : ParitySegment M,
      a.first = u ∧ a.last = F.root u ∧ b.first = v ∧ b.last = F.root v ∧
      (a.phase + a.length) % 2 = ((s.minLabel (F.root u)).getD 0 + 1) % 2 ∧
      (b.phase + b.length) % 2 = ((s.minLabel (F.root v)).getD 0 + 1) % 2 ∧
      (∀ k : Fin (a.length + 1), k.val < a.length → Blossom M cut (F.root u) (a.vertex k)) ∧
      (∀ k : Fin (b.length + 1), k.val < b.length → Blossom M cut (F.root v) (b.vertex k)) ∧
      a.phase % 2 = b.phase % 2 ∧
      ((M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1) ∧
      (a.length + (s.minLabel (F.root u)).getD 0) +
        (b.length + (s.minLabel (F.root v)).getD 0) + 1 = cut + 2 := by
  obtain ⟨U, hU⟩ := hu
  obtain ⟨V, hV⟩ := hv
  obtain ⟨B, hB⟩ := h.rootAssigned u U hU
  obtain ⟨C, hC⟩ := h.rootAssigned v V hV
  obtain ⟨hbhigh, hufiber⟩ := hrep u U hU
  obtain ⟨hchigh, hvfiber⟩ := hrep v V hV
  have hBm := h.minInvariant.1.1 (F.root u) B hB
  have hCm := h.minInvariant.1.1 (F.root v) C hC
  by_cases hm : M.mate u = some v
  · obtain ⟨i, hui, hvi, hum, hvm, _, _, hti⟩ := matched_bridge_levels hbridge hm (cut + 2) ht
    have hut : tenacity M u = some (cut + 2) := by
      have htm : matchedEdgeTenacity M u v = some (cut + 2) := by simpa only [MaximumMatching.edgeTenacity, ite_eq_left hm] using ht
      exact (matched_tenacity M hm).1.trans ((matched_tenacity M hm).2.trans htm)
    have hvt : tenacity M v = some (cut + 2) := (matched_tenacity M hm).2.trans
      (by simpa only [MaximumMatching.edgeTenacity, ite_eq_left hm] using ht)
    have hub : u = F.root u := by
      rcases hufiber with he | hb
      · exact he
      · obtain ⟨t, ht', htc⟩ := blossom_tenacity_bound cut (F.root u) u hb
        have := Option.some.inj (ht'.symm.trans hut)
        omega
    have hvc : v = F.root v := by
      rcases hvfiber with he | hb
      · exact he
      · obtain ⟨t, ht', htc⟩ := blossom_tenacity_bound cut (F.root v) v hb
        have := Option.some.inj (ht'.symm.trans hvt)
        omega
    have hBi : B = i := Option.some.inj (hBm.symm.trans (hub ▸ hum))
    have hCi : C = i := Option.some.inj (hCm.symm.trans (hvc ▸ hvm))
    have hio := level_parity M 1 u i hui
    refine ⟨ParitySegment.trivial M u 0, ParitySegment.trivial M v 0,
      rfl, hub, rfl, hvc, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
    · change (0 + 0) % 2 = ((s.minLabel (F.root u)).getD 0 + 1) % 2
      simp only [hB, Option.getD_some]
      omega
    · change (0 + 0) % 2 = ((s.minLabel (F.root v)).getD 0 + 1) % 2
      simp only [hC, Option.getD_some]
      omega
    · intro k hk; change k.val < 0 at hk; omega
    · intro k hk; change k.val < 0 at hk; omega
    · change (M.mate v = some u) ↔ (0 + 1) % 2 = 1
      exact ⟨fun _ => rfl, fun _ => M.symm hm⟩
    · change (0 + (s.minLabel (F.root u)).getD 0) + (0 + (s.minLabel (F.root v)).getD 0) + 1 = cut + 2
      simp only [hB, hC, Option.getD_some]
      omega
  · have hlevels : ∃ E D, evenlevel M u = some E ∧ evenlevel M v = some D ∧ E + D + 1 = cut + 2 := by
      have he : (levelAdd (evenlevel M u) (evenlevel M v)).map (· + 1) = some (cut + 2) :=
        by simpa only [MaximumMatching.edgeTenacity, ite_eq_right hm] using ht
      cases hEu : evenlevel M u with
      | none => simp only [hEu, levelAdd, Option.map_none] at he; contradiction
      | some E =>
        cases hDv : evenlevel M v with
        | none => simp only [hEu, hDv, levelAdd, Option.map_none] at he; contradiction
        | some D =>
          exact ⟨E, D, rfl, rfl, by simpa only [hEu, hDv, levelAdd, Option.map_some, Option.some.injEq] using he⟩
    obtain ⟨E, D, hE, hD, hsum⟩ := hlevels
    have hm' : M.mate v ≠ some u := fun hh => hm (M.symm hh)
    have ht' : MaximumMatching.edgeTenacity M v u = some (cut + 2) := (edgeTenacity_symmetric v u).trans ht
    obtain ⟨a, haf, hal, han, hap, hae, hai⟩ := unmatched_bridge_top_segment cut hc hnoaug
      u v (F.root u) hbridge hm ht hbhigh hufiber E B hE hBm
    obtain ⟨b, hbf, hbl, hbn, hbp, hbe, hbi⟩ := unmatched_bridge_top_segment cut hc hnoaug
      v u (F.root v) (bridge_symm hbridge) hm' ht' hchigh hvfiber D C hD hCm
    refine ⟨a, b, haf, hal, hbf, hbl, ?_, ?_, hai, hbi, by omega, ?_, ?_⟩
    · simpa only [hB, Option.getD_some] using hae
    · simpa only [hC, Option.getD_some] using hbe
    · rw [haf, hbf]
      constructor
      · intro hh; exact False.elim (hm' hh)
      · intro hh; omega
    · simp only [hB, hC, Option.getD_some]
      omega

end BudGraphInvariant
end MaximumMatching.Search

end BridgeTopSegments

section MatchingBridgePath

/-! Lift actual matching-derived DDFS linkages across their triggering bridge.
Under the explicit lower-blossom representation, the result is a real simple
alternating path with the bridge present and the exact tenacity budget. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}
namespace BudGraphInvariant
variable {cap cut : Nat} {s : State V} {F : BudForest V}

/-- A real DDFS linkage from one endpoint to a selected vertex and from the
other to bottom yields a real matching path through the triggering bridge. -/
theorem bridge_linkage_path (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut < p.length)
    (hhalf : 2 * cap ≤ cut + 3) (hrep : LowerBlossomRepresentation M cut s F)
    (u v : V) (hbridge : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, s.minLabel u = some k) (hv : ∃ k, s.minLabel v = some k)
    (p q : DDFS.Path (predecessorGraph s F h))
    (hpf : p.first = F.root u) (hqf : q.first = F.root v)
    (hqb : (predecessorGraph s F h).level q.last = 0) (hdis : p.Disjoint q) :
    ∃ z : AltPath M, z.first = q.last ∧ z.last = p.last ∧
      z.length + (s.minLabel p.last).getD 0 = cut + 2 ∧ z.ContainsEdge u v := by
  obtain ⟨a, b, haf, hal, hbf, hbl, hae, hbe, hai, hbi, hab, hmatch, hbudget⟩ :=
    h.bridge_top_segments hc hnoaug hrep u v hbridge ht hu hv
  let W := h.weightedMatching hc hnoaug hhalf hrep
  have hpa : ∃ k, s.minLabel p.first = some k := by
    rw [hpf]
    obtain ⟨k, hk⟩ := hu
    exact h.rootAssigned u k hk
  have hqa : ∃ k, s.minLabel q.first = some k := by
    rw [hqf]
    obtain ⟨k, hk⟩ := hv
    exact h.rootAssigned v k hk
  have hphigh := h.path_high hrep p (by rw [hpf]; exact F.root_fixed u) hpa
  have hqhigh := h.path_high hrep q (by rw [hqf]; exact F.root_fixed v) hqa
  have hap : (a.phase + a.length) % 2 = W.phase p.first % 2 := by
    change _ = ((s.minLabel p.first).getD 0 + 1) % 2
    rw [hpf]
    exact hae
  have hbp : (b.phase + b.length) % 2 = W.phase q.first % 2 := by
    change _ = ((s.minLabel q.first).getD 0 + 1) % 2
    rw [hqf]
    exact hbe
  obtain ⟨z, hzf, hzl, hzn, _, hze⟩ := W.bridge_detour_of_potential_contains p q
    hphigh hqhigh hdis a b (hal.trans hpf.symm) (hbl.trans hqf.symm) hap hbp
    (by rw [hpf]; exact hai) (by rw [hqf]; exact hbi)
    (h.path_bottom_free q hqa hqb) hab (by rw [hbf, haf]; exact G.symm hbridge.1) hmatch
    (fun w => (s.minLabel w).getD 0)
    (fun he => h.weightedMatching_drop hc hnoaug hhalf hrep he) hqb (cut + 2)
    (by rw [hpf, hqf]; exact hbudget)
  rw [hbf, haf] at hze
  exact ⟨z, hzf, hzl, hzn, (z.containsEdge_symm v u).1 hze⟩

/-- Two disjoint bottom paths in the actual predecessor/bud graph yield an
augmenting path whose length equals the triggering bridge tenacity. -/
theorem disjoint_bridge_paths_augment (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut < p.length)
    (hhalf : 2 * cap ≤ cut + 3) (hrep : LowerBlossomRepresentation M cut s F)
    (u v : V) (hbridge : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, s.minLabel u = some k) (hv : ∃ k, s.minLabel v = some k)
    (p q : DDFS.Path (predecessorGraph s F h))
    (hp : p.ToBottom (F.root u)) (hq : q.ToBottom (F.root v)) (hdis : p.Disjoint q) :
    ∃ z : AltPath M, z.Augmenting ∧ z.first = q.last ∧ z.last = p.last ∧
      z.length = cut + 2 ∧ z.ContainsEdge u v := by
  obtain ⟨z, hzf, hzl, hzn, hze⟩ := h.bridge_linkage_path hc hnoaug hhalf hrep u v
    hbridge ht hu hv p q hp.1 hq.1 hq.2 hdis
  have hpb : (s.minLabel p.last).getD 0 = 0 := hp.2
  have hlen : z.length = cut + 2 := by omega
  have hpa : ∃ k, s.minLabel p.first = some k := by
    rw [hp.1]
    obtain ⟨k, hk⟩ := hu
    exact h.rootAssigned u k hk
  have hfree : M.Free z.last := hzl ▸ h.path_bottom_free p hpa hp.2
  exact ⟨z, ⟨by rw [hlen]; omega, hfree⟩, hzf, hzl, hlen, hze⟩

/-- At the permitted bridge range, the constructed augmenting path is
shortest. This does not require that an augmenting path existed beforehand. -/
theorem disjoint_bridge_paths_shortest (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hhalf : 2 * cap ≤ cut + 3) (hrep : LowerBlossomRepresentation M cut s F)
    (u v : V) (hbridge : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, s.minLabel u = some k) (hv : ∃ k, s.minLabel v = some k)
    (p q : DDFS.Path (predecessorGraph s F h))
    (hp : p.ToBottom (F.root u)) (hq : q.ToBottom (F.root v)) (hdis : p.Disjoint q) :
    ∃ z : AltPath M, z.Augmenting ∧ z.length = cut + 2 ∧ z.ContainsEdge u v ∧
      ∀ r : AltPath M, r.Augmenting → z.length ≤ r.length := by
  have hnoaug : ∀ r : AltPath M, r.Augmenting → cut < r.length := by
    intro r hr
    have := htop r hr
    omega
  obtain ⟨z, hz, _, _, hlen, hze⟩ := h.disjoint_bridge_paths_augment hc hnoaug hhalf hrep
    u v hbridge ht hu hv p q hp hq hdis
  exact ⟨z, hz, hlen, hze, fun r hr => hlen ▸ htop r hr⟩

end BudGraphInvariant
end MaximumMatching.Search

end MatchingBridgePath

section MatchingBottleneckParity

/-! A computed bottleneck of a current bridge has even minimum level when
input fibers are lower blossoms. Odd roots cannot contain a lower blossom;
every incoming edge would then be the root's unique matched edge. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}
namespace BudGraphInvariant
variable {cap cut : Nat} {s : State V} {F : BudForest V}

/-- An odd-level root cannot have a nontrivial lower-blossom fiber. -/
theorem odd_root_fiber_singleton (h : BudGraphInvariant M cap s F)
    (hrep : LowerBlossomRepresentation M cut s F) (v : V) (k B : Nat)
    (hv : s.minLabel v = some k) (hb : s.minLabel (F.root v) = some B)
    (hodd : B % 2 = 1) : v = F.root v := by
  rcases (hrep v k hv).2 with he | hbl
  · exact he
  · have he : evenlevel M (F.root v) = some B :=
      (minlevel_eq_even_of_outer _ (blossom_outer cut _ v hbl)).symm.trans
        (h.minInvariant.1.1 _ B hb)
    have := level_parity M 0 (F.root v) B he
    omega

/-- Every graph edge entering an odd-level root comes from its unique
matched neighbor. The MIN range bound makes the predecessor honest at its
minimum level before contraction. -/
theorem odd_root_incoming_matched (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1) (hhalf : 2 * cap ≤ cut + 3)
    (hrep : LowerBlossomRepresentation M cut s F)
    (v b : V) (B : Nat) (hb : s.minLabel b = some B) (hodd : B % 2 = 1)
    (hedge : (predecessorGraph s F h).Edge v b) : M.mate b = some v := by
  obtain ⟨u, N, j, hv, hu, hp, hub, hjN⟩ := h.edge_witness hedge
  have hue : u = b := (h.odd_root_fiber_singleton hrep u j B hu
    (by rw [hub]; exact hb) hodd).trans hub
  subst u
  have hhigh : levelLT (some cut) (tenacity M b) := by
    have hh := (hrep b j hu).1
    rw [hub] at hh
    exact hh
  have hNm := h.minInvariant.1.1 v N hv
  have hBm := h.minInvariant.1.1 b B hb
  have hBpred := predecessor_high_minlevel b v N cut hp hNm hc
    (by have := h.labelsBounded v N hv; omega) hhigh
  have hBN : B = N - 1 := Option.some.inj (hBm.symm.trans hBpred)
  have hpos : 0 < N := by omega
  have hguard := ((predecessor_iff_level_guard b v (N - 1)
    (by simpa only [Nat.sub_add_cancel hpos] using hNm)).1 hp).2.2
  exact hguard.mpr (by omega)

/-- If a triggering endpoint's bud has odd minimum level, both endpoints
are singleton roots of equal level and the triggering bridge is matched. -/
theorem odd_trigger_roots (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1) (hrep : LowerBlossomRepresentation M cut s F)
    (u v : V) (hbridge : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, s.minLabel u = some k) (hv : ∃ k, s.minLabel v = some k)
    (B : Nat) (hb : s.minLabel (F.root u) = some B) (hodd : B % 2 = 1) :
    u = F.root u ∧ v = F.root v ∧ s.minLabel (F.root v) = some B := by
  obtain ⟨k, hk⟩ := hu
  obtain ⟨l, hl⟩ := hv
  have hue := h.odd_root_fiber_singleton hrep u k B hk hb hodd
  have hum : minlevel M u = some B := by rw [hue]; exact h.minInvariant.1.1 _ B hb
  have hhigh : levelLT (some cut) (tenacity M u) := by
    have hh := (hrep u k hk).1
    rwa [← hue] at hh
  have hinner : Inner M u := by
    refine ⟨⟨B, hum⟩, ?_⟩
    intro houter
    have he : evenlevel M u = some B := (minlevel_eq_even_of_outer u houter).symm.trans hum
    have := level_parity M 0 u B he
    omega
  have hm : M.mate u = some v := by
    by_cases hm : M.mate u = some v
    · exact hm
    · obtain ⟨t, ht', hlt⟩ := (unmatched_bridge_tenacity hbridge hm (cut + 2) ht).2 hinner
      have htodd := tenacity_odd M u t ht'
      rw [ht'] at hhigh
      change cut < t at hhigh
      omega
  obtain ⟨j, _, _, huj, hvj, _, _, _⟩ := matched_bridge_levels hbridge hm (cut + 2) ht
  have hjB : j = B := Option.some.inj (huj.symm.trans hum)
  have hlB : l = B := Option.some.inj ((h.minInvariant.1.1 v l hl).symm.trans (by simpa only [hjB] using hvj))
  have hvt : tenacity M v = some (cut + 2) :=
    (matched_tenacity M hm).2.trans (by simpa only [MaximumMatching.edgeTenacity, ite_eq_left hm] using ht)
  have hve : v = F.root v := by
    rcases (hrep v l hl).2 with he | hbl
    · exact he
    · obtain ⟨t, ht', hle⟩ := blossom_tenacity_bound cut (F.root v) v hbl
      have := Option.some.inj (ht'.symm.trans hvt)
      omega
  exact ⟨hue, hve, by rw [← hve]; simpa only [hlB] using hl⟩

section Finite
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}
    {cap cut : Nat} {s : State (Fin n)} {F : BudForest (Fin n)}

/-- Both actual colored trees force their common bottleneck to have even
minimum level. This does not assume the bottleneck has higher tenacity. -/
theorem colored_bottleneck_even (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1) (hhalf : 2 * cap ≤ cut + 3)
    (hrep : LowerBlossomRepresentation M cut s F)
    (u v : Fin n) (hbridge : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, s.minLabel u = some k) (hv : ∃ k, s.minLabel v = some k)
    (b : Fin n) (S : Fin n → Prop)
    (T : DDFS.ColoredTrees (predecessorGraph s F h) S (F.root u) (F.root v) b) :
    ∃ B, s.minLabel b = some B ∧ B % 2 = 0 := by
  obtain ⟨p, hpf, hpb, hps, _⟩ := T.red.path_within b (Or.inl rfl)
  obtain ⟨q, hqf, hqb, hqt, _⟩ := T.green.path_within b (Or.inl rfl)
  have hrootu : ∃ k, s.minLabel (F.root u) = some k := by
    obtain ⟨k, hk⟩ := hu
    exact h.rootAssigned u k hk
  have hbassign : ∃ k, s.minLabel b = some k := by
    have hh := h.path_assigned p (by rw [hpf]; exact hrootu) ⟨p.length, by omega⟩
    simpa only [show p.vertex ⟨p.length, by omega⟩ = b from hpb] using hh
  obtain ⟨B, hB⟩ := hbassign
  refine ⟨B, hB, ?_⟩
  by_cases heven : B % 2 = 0
  · exact heven
  have hodd : B % 2 = 1 := by omega
  have distinct_from_root (a c : Fin n) (hac : Bridge M a c)
      (hact : MaximumMatching.edgeTenacity M a c = some (cut + 2))
      (ha : ∃ k, s.minLabel a = some k) (hc' : ∃ k, s.minLabel c = some k)
      (r : DDFS.Path (predecessorGraph s F h))
      (hrf : r.first = F.root c) (hrb : r.last = b) : b ≠ F.root a := by
    intro he
    have hBa : s.minLabel (F.root a) = some B := he ▸ hB
    obtain ⟨hae, hce, hBc⟩ := h.odd_trigger_roots hc hrep a c hac hact ha hc' B hBa hodd
    have heq : r.last = r.first := r.eq_of_contains_level_eq r.contains_last r.contains_first (by
      change (s.minLabel r.last).getD 0 = (s.minLabel r.first).getD 0
      rw [hrb, hrf, hB, hBc])
    have hacEq : a = c := hae.trans (he.symm.trans (hrb.symm.trans (heq.trans (hrf.trans hce.symm))))
    exact G.loopless c (hacEq ▸ hac.1)
  have hbu := distinct_from_root u v hbridge ht hu hv q hqf hqb
  have hbv := distinct_from_root v u (bridge_symm hbridge)
    ((edgeTenacity_symmetric v u).trans ht) hv hu p hpf hpb
  have hpPos : 0 < p.length := by
    by_cases hz : p.length = 0
    · have he : p.first = p.last := congrArg p.vertex (Fin.ext (by omega))
      exact False.elim (hbu (hpb.symm.trans (he.symm.trans hpf)))
    · omega
  have hqPos : 0 < q.length := by
    by_cases hz : q.length = 0
    · have he : q.first = q.last := congrArg q.vertex (Fin.ext (by omega))
      exact False.elim (hbv (hqb.symm.trans (he.symm.trans hqf)))
    · omega
  let I : Fin (p.length + 1) := ⟨p.length - 1, by omega⟩
  let J : Fin (q.length + 1) := ⟨q.length - 1, by omega⟩
  have hep : (predecessorGraph s F h).Edge (p.vertex I) b := by
    have hh := p.adjacent ⟨p.length - 1, by omega⟩
    simpa only [I, show p.length - 1 + 1 = p.length by omega,
      show p.vertex ⟨p.length, by omega⟩ = b from hpb] using hh
  have heq : (predecessorGraph s F h).Edge (q.vertex J) b := by
    have hh := q.adjacent ⟨q.length - 1, by omega⟩
    simpa only [J, show q.length - 1 + 1 = q.length by omega,
      show q.vertex ⟨q.length, by omega⟩ = b from hqb] using hh
  have hpMatch := h.odd_root_incoming_matched hc hhalf hrep (p.vertex I) b B hB hodd hep
  have hqMatch := h.odd_root_incoming_matched hc hhalf hrep (q.vertex J) b B hB hodd heq
  have hsame := M.mate_unique hpMatch hqMatch
  have hred := hps (p.vertex I) ⟨I, rfl⟩
  have hgreen : p.vertex I = b ∨ T.color (p.vertex I) = some true := by
    rw [hsame]
    exact hqt (q.vertex J) ⟨J, rfl⟩
  have he := (T.overlap (p.vertex I)).1 ⟨hred, hgreen⟩
  have hdrop := (predecessorGraph s F h).decreases hep
  rw [he] at hdrop
  omega

end Finite

end BudGraphInvariant
end MaximumMatching.Search

end MatchingBottleneckParity

section MatchingSupportSound

namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A real complementary-length path pins down both tenacity and maxlevel
when the endpoint is above the preceding odd cutoff. -/
theorem maxlevel_of_complementary_length (p : AltPath M) (cut k : Nat)
    (hc : cut % 2 = 1) (hk : minlevel M p.last = some k)
    (hhigh : levelLT (some cut) (tenacity M p.last))
    (hbudget : p.length + k = cut + 2) :
    tenacity M p.last = some (cut + 2) ∧ maxlevel M p.last = some p.length := by
  have hmin : levelLE (some (cut + 2)) (tenacity M p.last) := by
    cases ht : tenacity M p.last with
    | none => trivial
    | some t =>
      have htodd := tenacity_odd M p.last t ht
      rw [ht] at hhigh
      change cut < t at hhigh
      change cut + 2 ≤ t
      omega
  have ht := (levels_of_opposite_bound p.last k (cut + 2)
    (level_of_minlevel p.last k hk) (by omega) hmin
    ⟨p.length, ⟨p, rfl, rfl, by omega⟩, by omega⟩).1
  refine ⟨ht, ?_⟩
  have hmax := (maxlevel_eq_tenacity_sub p.last (cut + 2) k ht hk).2
  simpa only [show cut + 2 - k = p.length by omega] using hmax

end MaximumMatching.AltPath

namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}
namespace BudGraphInvariant
variable {cap cut : Nat} {s : State (Fin n)} {F : BudForest (Fin n)}

/-- Every non-bottleneck root selected by the actual colored region belongs
to the triggering bridge's semantic support, when the input forest represents
lower blossoms. Both the vertex tenacity and a maxlevel witness containing
the trigger edge are derived from expanded colored-tree linkages. -/
theorem colored_region_support (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hhalf : 2 * cap ≤ cut + 3) (hrep : LowerBlossomRepresentation M cut s F)
    (u v : Fin n) (hbridge : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, s.minLabel u = some k) (hv : ∃ k, s.minLabel v = some k)
    (b : Fin n) (S : Fin n → Prop)
    (T : DDFS.ColoredTrees (predecessorGraph s F h) S (F.root u) (F.root v) b)
    (region : ∀ w, S w ↔ DDFS.OnRootTo (H := predecessorGraph s F h) (F.root u) (F.root v) b w)
    (w : Fin n) (hw : S w) (hwb : w ≠ b) :
    tenacity M w = some (cut + 2) ∧ InSupport M u v w := by
  have hnoaug : ∀ p : AltPath M, p.Augmenting → cut < p.length := by
    intro p hp
    have := htop p hp
    omega
  have hlevel := DDFS.onRootTo_level_gt ((region w).1 hw) hwb
  obtain ⟨p, q, hpw, hqb, hdis, hstart⟩ := T.bottom_linkage h.reachBottom w hw hlevel
  have hrootu : ∃ k, s.minLabel (F.root u) = some k := by
    obtain ⟨k, hk⟩ := hu
    exact h.rootAssigned u k hk
  have hrootv : ∃ k, s.minLabel (F.root v) = some k := by
    obtain ⟨k, hk⟩ := hv
    exact h.rootAssigned v k hk
  have hpa : ∃ k, s.minLabel p.first = some k := by
    rcases hstart with ⟨hpu, _, _⟩ | ⟨hpv, _, _⟩
    · rw [hpu]; exact hrootu
    · rw [hpv]; exact hrootv
  have hpf : F.parent p.first = p.first := by
    rcases hstart with ⟨hpu, _, _⟩ | ⟨hpv, _, _⟩
    · rw [hpu]; exact F.root_fixed u
    · rw [hpv]; exact F.root_fixed v
  have hwfixed : F.parent w = w := by
    have hh := h.path_fixed p hpf ⟨p.length, by omega⟩
    simpa only [show p.vertex ⟨p.length, by omega⟩ = w from hpw] using hh
  have hwassigned : ∃ k, s.minLabel w = some k := by
    have hh := h.path_assigned p hpa ⟨p.length, by omega⟩
    simpa only [show p.vertex ⟨p.length, by omega⟩ = w from hpw] using hh
  obtain ⟨k, hk⟩ := hwassigned
  have hwhigh : levelLT (some cut) (tenacity M w) := by
    have hh := (hrep w k hk).1
    rwa [F.root_of_fixed w hwfixed] at hh
  have hex : ∃ z : AltPath M, z.last = w ∧ z.length + k = cut + 2 ∧ z.ContainsEdge u v := by
    rcases hstart with ⟨hpu, hqv, _⟩ | ⟨hpv, hqu, _⟩
    · obtain ⟨z, _, hzw, hlen, he⟩ := h.bridge_linkage_path hc hnoaug hhalf hrep u v
        hbridge ht hu hv p q hpu hqv hqb hdis
      rw [hpw, hk] at hlen
      exact ⟨z, hzw.trans hpw, hlen, he⟩
    · obtain ⟨z, _, hzw, hlen, he⟩ := h.bridge_linkage_path hc hnoaug hhalf hrep v u
        (bridge_symm hbridge) ((edgeTenacity_symmetric v u).trans ht) hv hu p q hpv hqu hqb hdis
      rw [hpw, hk] at hlen
      exact ⟨z, hzw.trans hpw, hlen, (z.containsEdge_symm v u).1 he⟩
  obtain ⟨z, hzw, hlen, he⟩ := hex
  have hmin : minlevel M z.last = some k := by rw [hzw]; exact h.minInvariant.1.1 w k hk
  obtain ⟨hzt, hmax⟩ := z.maxlevel_of_complementary_length cut k hc hmin
    (by rw [hzw]; exact hwhigh) hlen
  have hwt : tenacity M w = some (cut + 2) := by rwa [hzw] at hzt
  exact ⟨hwt, hbridge, cut + 2, htop, ht, hwt, z, hzw,
    by rwa [hzw] at hmax, he⟩

end BudGraphInvariant
end MaximumMatching.Search

end MatchingSupportSound
