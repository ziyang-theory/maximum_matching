import MaximumMatching.CurrentBridgeRepresentation

/-! Bridge path lifting throughout a fixed MAX level. These results use the
path representation preserved by actual same-level petal contractions, without
reimposing a lower-blossom identity on the updated fibers. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}
namespace CurrentBridgeRepresentation
variable {cap cut : Nat} {s : State V} {F : BudForest V} {h : BudGraphInvariant M cap s F}

/-- A root-to-vertex/bottom linkage lifts through its actual trigger bridge,
even after earlier same-level petal contractions. -/
theorem bridge_linkage_path (P : CurrentBridgeRepresentation M cut h)
    (u v : V) (hb : Bridge M u v) (ht : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, s.minLabel u = some k) (hv : ∃ k, s.minLabel v = some k)
    (p q : DDFS.Path (predecessorGraph s F h))
    (hpf : p.first = F.root u) (hqf : q.first = F.root v)
    (hqb : (predecessorGraph s F h).level q.last = 0) (hdis : p.Disjoint q) :
    ∃ z : AltPath M, z.first = q.last ∧ z.last = p.last ∧
      z.length + (s.minLabel p.last).getD 0 = cut + 2 ∧ z.ContainsEdge u v := by
  obtain ⟨a, b, haf, hal, hbf, hbl, hae, hbe, hai, hbi, hab, hmatch, hbudget⟩ := P.tops u v hb ht hu hv
  have hpa : ∃ k, s.minLabel p.first = some k := by
    rw [hpf]
    obtain ⟨k, hk⟩ := hu
    exact h.rootAssigned u k hk
  have hqa : ∃ k, s.minLabel q.first = some k := by
    rw [hqf]
    obtain ⟨k, hk⟩ := hv
    exact h.rootAssigned v k hk
  have hpfix : ∀ w, p.Contains w → F.root w = w := by
    rintro w ⟨i, rfl⟩
    exact F.root_of_fixed _ (h.path_fixed p (by rw [hpf]; exact F.root_fixed u) i)
  have hqfix : ∀ w, q.Contains w → F.root w = w := by
    rintro w ⟨i, rfl⟩
    exact F.root_of_fixed _ (h.path_fixed q (by rw [hqf]; exact F.root_fixed v) i)
  let pr := p.restrictRoots F hpfix
  let qr := q.restrictRoots F hqfix
  have hap : (a.phase + a.length) % 2 = P.weighted.phase pr.first % 2 := by
    rw [P.phase]
    change _ = ((s.minLabel p.first).getD 0 + 1) % 2
    rw [hpf]
    exact hae
  have hbp : (b.phase + b.length) % 2 = P.weighted.phase qr.first % 2 := by
    rw [P.phase]
    change _ = ((s.minLabel q.first).getD 0 + 1) % 2
    rw [hqf]
    exact hbe
  obtain ⟨z, hzf, hzl, hzn, _, hze⟩ := P.weighted.bridge_detour_of_potential_contains pr qr
    hpfix hqfix hdis a b (hal.trans hpf.symm) (hbl.trans hqf.symm) hap hbp
    (by change ∀ j, j.val < a.length → F.root (a.vertex j) = p.first; rw [hpf]; exact hai)
    (by change ∀ j, j.val < b.length → F.root (b.vertex j) = q.first; rw [hqf]; exact hbi)
    (h.path_bottom_free q hqa hqb) hab (by rw [hbf, haf]; exact G.symm hb.1) hmatch
    (fun w => (s.minLabel w).getD 0) P.drop hqb (cut + 2)
    (by change _ + _ + 1 = cut + 2; change (a.length + (s.minLabel p.first).getD 0) +
          (b.length + (s.minLabel q.first).getD 0) + 1 = cut + 2
        rw [hpf, hqf]; exact hbudget)
  rw [hbf, haf] at hze
  exact ⟨z, hzf, hzl, hzn, (z.containsEdge_symm v u).1 hze⟩

/-- The disjoint case yields a real augmenting path throughout the level,
with the exact bridge tenacity as its matching-graph length. -/
theorem disjoint_bridge_paths_augment (P : CurrentBridgeRepresentation M cut h)
    (hc : cut % 2 = 1) (u v : V) (hb : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, s.minLabel u = some k) (hv : ∃ k, s.minLabel v = some k)
    (p q : DDFS.Path (predecessorGraph s F h))
    (hp : p.ToBottom (F.root u)) (hq : q.ToBottom (F.root v)) (hdis : p.Disjoint q) :
    ∃ z : AltPath M, z.Augmenting ∧ z.first = q.last ∧ z.last = p.last ∧
      z.length = cut + 2 ∧ z.ContainsEdge u v := by
  obtain ⟨z, hzf, hzl, hzn, hze⟩ := P.bridge_linkage_path u v hb ht hu hv p q hp.1 hq.1 hq.2 hdis
  have hpb : (s.minLabel p.last).getD 0 = 0 := hp.2
  have hlen : z.length = cut + 2 := by omega
  have hpa : ∃ k, s.minLabel p.first = some k := by
    rw [hp.1]
    obtain ⟨k, hk⟩ := hu
    exact h.rootAssigned u k hk
  have hfree : M.Free z.last := hzl ▸ h.path_bottom_free p hpa hp.2
  exact ⟨z, ⟨by rw [hlen]; omega, hfree⟩, hzf, hzl, hlen, hze⟩

section Finite
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}
    {cap cut : Nat} {s : State (Fin n)} {F : BudForest (Fin n)} {h : BudGraphInvariant M cap s F}

/-- The actual executable DDFS disjoint outcome supplies the constructed
augmenting witness; there is no separate path-lifting certificate input. -/
theorem execute_disjoint_augment (P : CurrentBridgeRepresentation M cut h)
    (hc : cut % 2 = 1) (u v : Fin n) (hb : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, s.minLabel u = some k) (hv : ∃ k, s.minLabel v = some k) :
    match DDFS.Machine.executeFull h.reachBottom (F.root u) (F.root v) with
    | .disjoint p q _ _ _ => ∃ z : AltPath M, z.Augmenting ∧ z.first = q.last ∧
        z.last = p.last ∧ z.length = cut + 2 ∧ z.ContainsEdge u v
    | .bottleneck _ _ _ _ _ => True := by
  cases DDFS.Machine.executeFull h.reachBottom (F.root u) (F.root v) with
  | disjoint p q hp hq hd => exact P.disjoint_bridge_paths_augment hc u v hb ht hu hv p q hp hq hd
  | bottleneck => trivial

end Finite
end CurrentBridgeRepresentation
end MaximumMatching.Search
