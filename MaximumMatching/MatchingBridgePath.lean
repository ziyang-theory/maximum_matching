import MaximumMatching.BridgeTopSegments
import MaximumMatching.WeightedBridgePath
import MaximumMatching.DDFSTrees

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
