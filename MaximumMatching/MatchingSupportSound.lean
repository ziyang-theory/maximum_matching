import MaximumMatching.MatchingBridgePath
import MaximumMatching.MatchingDDFSBud
import MaximumMatching.DDFSColoredLinkage

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
