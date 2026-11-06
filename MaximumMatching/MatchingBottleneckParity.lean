import MaximumMatching.MatchingBridgePath
import MaximumMatching.DDFSColoredLinkage

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
