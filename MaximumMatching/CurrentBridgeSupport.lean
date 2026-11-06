import MaximumMatching.CurrentBridgePath
import MaximumMatching.MatchingSupportSound

/-! Support soundness of actual DDFS outputs throughout one search level.
The path representation is initialized from lower blossoms and preserved by
actual same-level petal merges, so it is not reinstated as a blossom oracle. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}
namespace CurrentBridgeRepresentation
variable {cap cut : Nat} {s : State (Fin n)} {F : BudForest (Fin n)}
    {h : BudGraphInvariant M cap s F}

/-- Every non-bottleneck root selected by the actual colored region belongs
to the triggering bridge's semantic support, throughout the current MAX level. Both the vertex tenacity and a maxlevel
witness containing the trigger edge are derived from the preserved actual
fiber paths, including after earlier same-level contractions. -/
theorem colored_region_support (P : CurrentBridgeRepresentation M cut h)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (u v : Fin n) (hbridge : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, s.minLabel u = some k) (hv : ∃ k, s.minLabel v = some k)
    (b : Fin n) (S : Fin n → Prop)
    (T : DDFS.ColoredTrees (predecessorGraph s F h) S (F.root u) (F.root v) b)
    (region : ∀ w, S w ↔ DDFS.OnRootTo (H := predecessorGraph s F h) (F.root u) (F.root v) b w)
    (w : Fin n) (hw : S w) (hwb : w ≠ b) :
    tenacity M w = some (cut + 2) ∧ InSupport M u v w := by
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
    have hh := P.high w k hk
    rwa [F.root_of_fixed w hwfixed] at hh
  have hex : ∃ z : AltPath M, z.last = w ∧ z.length + k = cut + 2 ∧ z.ContainsEdge u v := by
    rcases hstart with ⟨hpu, hqv, _⟩ | ⟨hpv, hqu, _⟩
    · obtain ⟨z, _, hzw, hlen, he⟩ := P.bridge_linkage_path u v
        hbridge ht hu hv p q hpu hqv hqb hdis
      rw [hpw, hk] at hlen
      exact ⟨z, hzw.trans hpw, hlen, he⟩
    · obtain ⟨z, _, hzw, hlen, he⟩ := P.bridge_linkage_path v u
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

/-- The permitted bridge bound makes the expanded disjoint outcome globally
shortest among all augmenting paths. -/
theorem disjoint_bridge_paths_shortest (P : CurrentBridgeRepresentation M cut h)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (u v : Fin n) (hb : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, s.minLabel u = some k) (hv : ∃ k, s.minLabel v = some k)
    (p q : DDFS.Path (predecessorGraph s F h))
    (hp : p.ToBottom (F.root u)) (hq : q.ToBottom (F.root v)) (hdis : p.Disjoint q) :
    ∃ z : AltPath M, z.Augmenting ∧ z.length = cut + 2 ∧ z.ContainsEdge u v ∧
      ∀ r : AltPath M, r.Augmenting → z.length ≤ r.length := by
  obtain ⟨z, hz, _, _, hlen, hze⟩ := P.disjoint_bridge_paths_augment hc u v hb ht hu hv p q hp hq hdis
  exact ⟨z, hz, hlen, hze, fun r hr => hlen ▸ htop r hr⟩

/-- Both branches of the actual executable DDFS have matching-level
soundness: a real shortest augmenting path or actual support members.
The support assertion excludes the reported bottleneck. -/
theorem execute_output_sound (P : CurrentBridgeRepresentation M cut h)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (u v : Fin n) (hb : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, s.minLabel u = some k) (hv : ∃ k, s.minLabel v = some k) :
    match DDFS.Machine.executeFull h.reachBottom (F.root u) (F.root v) with
    | .disjoint _ _ _ _ _ => ∃ z : AltPath M, z.Augmenting ∧ z.length = cut + 2 ∧
        z.ContainsEdge u v ∧ ∀ r : AltPath M, r.Augmenting → z.length ≤ r.length
    | .bottleneck b S _ _ _ => ∀ w, S w → w ≠ b →
        tenacity M w = some (cut + 2) ∧ InSupport M u v w := by
  cases DDFS.Machine.executeFull h.reachBottom (F.root u) (F.root v) with
  | disjoint p q hp hq hd => exact P.disjoint_bridge_paths_shortest hc htop u v hb ht hu hv p q hp hq hd
  | bottleneck b S T highest region =>
    exact P.colored_region_support hc htop u v hb ht hu hv b S T region

end CurrentBridgeRepresentation
end MaximumMatching.Search
