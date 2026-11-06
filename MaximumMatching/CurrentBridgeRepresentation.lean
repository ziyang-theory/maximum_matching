import MaximumMatching.MatchingBridgePath
import MaximumMatching.PetalRecord
import MaximumMatching.SearchStage

section CurrentBridgeRepresentation

/-! A path representation for every bridge at one fixed search tenacity.
The initial witnesses are constructed from lower blossoms; actual petal
merges preserve them through recorded old root paths. The record contains
path data and budgets, not support membership or MAX correctness. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

/-- Actual two endpoint arms for one triggering edge, with an exact total
budget. All vertices before each final root remain in its current fiber. -/
def BridgeEndpointArms (M : Matching G) (t : Nat) (s : State V)
    (F : BudForest V) (u v : V) : Prop :=
  ∃ a b : ParitySegment M,
    a.first = u ∧ a.last = F.root u ∧ b.first = v ∧ b.last = F.root v ∧
    (a.phase + a.length) % 2 = ((s.minLabel (F.root u)).getD 0 + 1) % 2 ∧
    (b.phase + b.length) % 2 = ((s.minLabel (F.root v)).getD 0 + 1) % 2 ∧
    (∀ k : Fin (a.length + 1), k.val < a.length → F.root (a.vertex k) = F.root u) ∧
    (∀ k : Fin (b.length + 1), k.val < b.length → F.root (b.vertex k) = F.root v) ∧
    a.phase % 2 = b.phase % 2 ∧
    ((M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1) ∧
    (a.length + (s.minLabel (F.root u)).getD 0) +
      (b.length + (s.minLabel (F.root v)).getD 0) + 1 = t

/-- Representation retained throughout one MAX search level. It permits
same-level petals and refers to their actual fibers, not whole blossoms. -/
structure CurrentBridgeRepresentation (M : Matching G) (cut : Nat)
    {cap : Nat} {s : State V} {F : BudForest V} (h : BudGraphInvariant M cap s F) where
  weighted : DDFS.FiberWeightedMatching M (DDFS.fixedRootGraph (predecessorGraph s F h) F) F
  phase : ∀ v, weighted.phase v % 2 = ((s.minLabel v).getD 0 + 1) % 2
  drop : ∀ {u v} (he : (DDFS.fixedRootGraph (predecessorGraph s F h) F).Edge u v),
    (weighted.segment he).length + (s.minLabel v).getD 0 = (s.minLabel u).getD 0
  high : ∀ v k, s.minLabel v = some k → levelLT (some cut) (MaximumMatching.tenacity M (F.root v))
  tops : ∀ u v, Bridge M u v → MaximumMatching.edgeTenacity M u v = some (cut + 2) →
    (∃ k, s.minLabel u = some k) → (∃ k, s.minLabel v = some k) →
      BridgeEndpointArms M (cut + 2) s F u v

namespace CurrentBridgeRepresentation
variable {cap cut : Nat} {s : State V} {F : BudForest V}

/-- Initialize the complete current-bridge path record from established
lower blossoms and actual MIN coverage. Every edge and endpoint witness is
constructed by the preceding matching-specific expansion theorems. -/
noncomputable def ofLowerBlossoms (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut < p.length)
    (hhalf : 2 * cap ≤ cut + 3) (hcap : cut ≤ 2 * cap + 1)
    (hrep : LowerBlossomRepresentation M cut s F) : CurrentBridgeRepresentation M cut h where
  weighted := (h.fiberWeightedMatching hc hnoaug hhalf hcap hrep).restrictRoots
  phase _ := rfl
  drop he := h.fiberWeightedMatching_drop hc hnoaug hhalf hcap hrep he.1
  high v k hv := (hrep v k hv).1
  tops := by
    intro u v hb ht hu hv
    obtain ⟨a, b, haf, hal, hbf, hbl, hae, hbe, hai, hbi, hab, hm, hbudget⟩ :=
      h.bridge_top_segments hc hnoaug hrep u v hb ht hu hv
    have huhigh : levelLT (some cut) (MaximumMatching.tenacity M (F.root u)) := by
      obtain ⟨k, hk⟩ := hu
      exact (hrep u k hk).1
    have hvhigh : levelLT (some cut) (MaximumMatching.tenacity M (F.root v)) := by
      obtain ⟨k, hk⟩ := hv
      exact (hrep v k hk).1
    refine ⟨a, b, haf, hal, hbf, hbl, hae, hbe, ?_, ?_, hab, hm, hbudget⟩
    · intro j hj
      exact h.lower_blossom_fiber hcap hrep (F.root u) _ huhigh (hai j hj)
    · intro j hj
      exact h.lower_blossom_fiber hcap hrep (F.root v) _ hvhigh (hbi j hj)

end CurrentBridgeRepresentation

namespace PetalRecord
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G} {cut : Nat}

/-- Preserve all current-bridge endpoint arms through this actual recorded
petal event, including bridges not yet processed. -/
theorem after_bridge_arms (R : PetalRecord M) (P : CurrentBridgeRepresentation M cut R.invariant)
    (u v : Fin n) (hb : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, R.prior.minLabel u = some k) (hv : ∃ k, R.prior.minLabel v = some k) :
    BridgeEndpointArms M (cut + 2) R.prior R.after u v := by
  obtain ⟨a, b, haf, hal, hbf, hbl, hae, hbe, hai, hbi, hab, hm, hbudget⟩ := P.tops u v hb ht hu hv
  obtain ⟨c, hcf, hcl, hcn, hcp, hce, hci⟩ :=
    R.after_arm_expansion P.weighted P.phase P.drop u a haf hal hae hai
  obtain ⟨d, hdf, hdl, hdn, hdp, hde, hdi⟩ :=
    R.after_arm_expansion P.weighted P.phase P.drop v b hbf hbl hbe hbi
  refine ⟨c, d, hcf, hcl, hdf, hdl, hce, hde, (fun j _ => hci j), (fun j _ => hdi j),
    by simpa only [hcp, hdp] using hab, ?_, by omega⟩
  simpa only [hcf, hdf, haf, hbf, hdp] using hm

/-- Same-level contraction keeps every assigned root above the lower cut:
the new bottleneck is itself one of the old assigned fixed roots. -/
theorem after_roots_high (R : PetalRecord M) (P : CurrentBridgeRepresentation M cut R.invariant)
    (v : Fin n) (k : Nat) (hv : R.prior.minLabel v = some k) :
    levelLT (some cut) (MaximumMatching.tenacity M (R.after.root v)) := by
  have hr := R.after_root v
  split at hr
  · obtain ⟨j, hj⟩ := R.selected_assigned.1
    have hb := P.high R.bottleneck j hj
    rw [R.forest.root_of_fixed _ (R.selected_fixed _ R.trees.bottleneck_mem)] at hb
    rw [hr]
    exact hb
  · rw [hr]
    exact P.high v k hv

/-- An actual petal merge preserves the entire fixed-tenacity path
representation. No support-identification or output-validity premise is
added: all new paths are built from the previous ones and the recorded run. -/
noncomputable def afterBridgeRepresentation (R : PetalRecord M)
    (P : CurrentBridgeRepresentation M cut R.invariant) :
    CurrentBridgeRepresentation M cut R.after_invariant where
  weighted := R.afterWeightedMatching P.weighted P.phase P.drop
  phase _ := rfl
  drop he := R.afterWeightedMatching_drop P.weighted P.phase P.drop he
  high v k hv := R.after_roots_high P v k hv
  tops u v hb ht hu hv := R.after_bridge_arms P u v hb ht hu hv

end PetalRecord
end MaximumMatching.Search

end CurrentBridgeRepresentation

section CurrentBridgePath

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

end CurrentBridgePath

section CurrentBridgeSupport

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

end CurrentBridgeSupport

section PetalMax

/-! Concrete MAX processing of the roots selected by an actual petal record.
Only selected non-bottleneck roots receive current-tenacity assignments; old
descendants in their fibers are not mistaken for new current-tenacity roots.
The executable fold includes the source's incident bridge refresh. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

section
variable [DecidableRel G.Adj]

theorem maxProcessVertices_minLabel (M : Matching G) (i : Nat) (vs : List (Fin n))
    (s : State (Fin n)) (v : Fin n) :
    (maxProcessVertices M i vs s).minLabel v = s.minLabel v := by
  induction vs generalizing s with
  | nil => rfl
  | cons u us ih => exact (ih (maxProcessVertex M i u s)).trans (maxProcessVertex_labels M i u v s).1

theorem maxProcessVertices_outside_maxLabel (M : Matching G) (i : Nat) (vs : List (Fin n))
    (s : State (Fin n)) (v : Fin n) (hv : v ∉ vs) :
    (maxProcessVertices M i vs s).maxLabel v = s.maxLabel v := by
  induction vs generalizing s with
  | nil => rfl
  | cons u us ih =>
    have hne : v ≠ u := fun he => hv (List.mem_cons.mpr (Or.inl he))
    have htail : v ∉ us := fun hm => hv (List.mem_cons_of_mem u hm)
    have ha : (assignMax s (2 * i + 1) u).maxLabel v = s.maxLabel v := by
      unfold assignMax
      split
      · rfl
      · exact ite_eq_right hne
    exact (ih (maxProcessVertex M i u s) htail).trans ((maxProcessVertex_labels M i u v s).2.trans ha)

end

namespace PetalRecord

/-- The actual computed root list used by MAX, excluding the bottleneck. -/
def newRoots (R : PetalRecord M) : List (Fin n) :=
  R.trees.vertices.filter fun v => decide (v ≠ R.bottleneck)

theorem mem_newRoots (R : PetalRecord M) (v : Fin n) :
    v ∈ R.newRoots ↔ R.selected v ∧ v ≠ R.bottleneck := by
  simp only [newRoots, List.mem_filter, decide_eq_true_eq, R.trees.mem_vertices]

theorem newRoots_fixed (R : PetalRecord M) (v : Fin n) (hv : v ∈ R.newRoots) :
    R.forest.parent v = v := R.selected_fixed v ((R.mem_newRoots v).1 hv).1

/-- Current tenacity and actual trigger support are derived for each listed
root from the computed trees and lower-blossom input representation. -/
theorem newRoots_support (R : PetalRecord M) (cut : Nat) (hc : cut % 2 = 1)
    (htop : AtMostShortestAugmenting M (cut + 2))
    (hhalf : 2 * R.cap ≤ cut + 3)
    (hrep : LowerBlossomRepresentation M cut R.prior R.forest)
    (hten : R.tenacity = cut + 2) (v : Fin n) (hv : v ∈ R.newRoots) :
    MaximumMatching.tenacity M v = some R.tenacity ∧ InSupport M R.left R.right v := by
  obtain ⟨hsel, hne⟩ := (R.mem_newRoots v).1 hv
  have hh := R.invariant.colored_region_support hc htop hhalf hrep R.left R.right
    R.trigger.1 (by rw [← hten]; exact R.trigger.2) R.starts_assigned.1 R.starts_assigned.2
    R.bottleneck R.selected R.trees R.region v hsel hne
  exact ⟨by simpa only [hten] using hh.1, hh.2⟩

section
variable [DecidableRel G.Adj]

/-- Process the computed root list using the actual assignment and incident
refresh operation, and retain the actual contracted forest. -/
def maxEvent (R : PetalRecord M) (i : Nat) : State (Fin n) × BudForest (Fin n) :=
  (maxProcessVertices M i R.newRoots R.prior, R.after)

theorem maxEvent_minLabel (R : PetalRecord M) (i : Nat) (v : Fin n) :
    (R.maxEvent i).1.minLabel v = R.prior.minLabel v :=
  maxProcessVertices_minLabel M i R.newRoots R.prior v

theorem maxEvent_outside (R : PetalRecord M) (i : Nat) (v : Fin n) (hv : v ∉ R.newRoots) :
    (R.maxEvent i).1.maxLabel v = R.prior.maxLabel v :=
  maxProcessVertices_outside_maxLabel M i R.newRoots R.prior v hv

/-- A concrete petal event preserves the complete local MIN/MAX stage state
and the matching-derived bud graph, sets every newly selected root's correct
maximum level, and preserves every prior maximum-level assignment. The only
path-representation premise is at the preceding blossom cutoff. -/
theorem maxEvent_correct (R : PetalRecord M) (i cut cutoff : Nat)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hrep : LowerBlossomRepresentation M cut R.prior R.forest)
    (hten : R.tenacity = cut + 2) (hstageTen : cut + 2 = 2 * i + 1)
    (hcap : R.cap = i + 1) (hstage : StageState M (i + 1) cutoff R.prior) :
    StageState M (i + 1) cutoff (R.maxEvent i).1 ∧
      BudGraphInvariant M (i + 1) (R.maxEvent i).1 (R.maxEvent i).2 ∧
      (∀ v, v ∈ R.newRoots → (R.maxEvent i).1.maxLabel v = maxlevel M v) ∧
      (∀ v k, R.prior.maxLabel v = some k → (R.maxEvent i).1.maxLabel v = some k) := by
  have hhalf : 2 * R.cap ≤ cut + 3 := by omega
  have hroots : ∀ v, v ∈ R.newRoots → MaximumMatching.tenacity M v = some (2 * i + 1) := by
    intro v hv
    have hh := (R.newRoots_support cut hc htop hhalf hrep hten v hv).1
    simpa only [hten, hstageTen] using hh
  have hs := maxProcessVertices_stageState M i cutoff R.newRoots R.prior hstage hroots
  refine ⟨hs, ?_, ?_, ?_⟩
  · refine ⟨hs.min, hs.minBound, ?_, ?_⟩
    · intro v k hv
      have hold : R.prior.minLabel v = some k := (R.maxEvent_minLabel i v).symm.trans hv
      obtain ⟨j, hj⟩ := R.after_invariant.rootAssigned v k hold
      exact ⟨j, (R.maxEvent_minLabel i (R.after.root v)).trans hj⟩
    · intro v
      exact (R.after_invariant.rankLabel v).trans (congrArg (fun x : Option Nat => x.getD 0)
        (R.maxEvent_minLabel i v).symm)
  · intro v hv
    exact maxProcessVertices_member_correct M i cutoff R.newRoots R.prior hstage hroots v hv
  · intro v k hv
    exact maxProcessVertices_preserves_known_maxLabel M i cutoff R.newRoots R.prior hstage hroots v k hv

end

end PetalRecord
end MaximumMatching.Search

end PetalMax

section PetalCurrentMax

/-! Concrete MAX events throughout one search level. The path representation
is preserved across the actual assignment/incident-refresh fold and the actual
recorded bud contraction, permitting the next event to reuse proved witnesses. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

/-- The predecessor graph depends only on minimum labels and predecessor
lists; MAX's other state fields and proof witnesses do not affect it. -/
theorem predecessorGraph_eq_of_fields {cap cap' : Nat} {s s' : State V} {F : BudForest V}
    (h : BudGraphInvariant M cap s F) (h' : BudGraphInvariant M cap' s' F)
    (hmin : s'.minLabel = s.minLabel) (hpred : s'.predecessors = s.predecessors) :
    predecessorGraph s' F h' = predecessorGraph s F h := by
  unfold predecessorGraph
  congr 1
  · unfold budEdge
    rw [hmin, hpred]
  · rw [hmin]

/-- Transport actual edge/arm witnesses across state updates that preserve
MIN's data. The new stage invariant is proved separately by the state update. -/
noncomputable def CurrentBridgeRepresentation.of_same_min_data {cap cap' cut : Nat}
    {s s' : State V} {F : BudForest V} {h : BudGraphInvariant M cap s F}
    (P : CurrentBridgeRepresentation M cut h) (h' : BudGraphInvariant M cap' s' F)
    (hmin : s'.minLabel = s.minLabel) (hpred : s'.predecessors = s.predecessors) :
    CurrentBridgeRepresentation M cut h' := by
  let lift : ∀ {u v}, (DDFS.fixedRootGraph (predecessorGraph s' F h') F).Edge u v →
      (DDFS.fixedRootGraph (predecessorGraph s F h) F).Edge u v := by
    intro u v he
    simpa only [predecessorGraph_eq_of_fields h h' hmin hpred] using he
  refine {
    weighted := {
      phase := P.weighted.phase
      segment := fun he => P.weighted.segment (lift he)
      first := fun he => P.weighted.first (lift he)
      last := fun he => P.weighted.last (lift he)
      start_phase := fun he => P.weighted.start_phase (lift he)
      end_phase := fun he => P.weighted.end_phase (lift he)
      interior := fun he => P.weighted.interior (lift he) }
    phase := ?_
    drop := ?_
    high := ?_
    tops := ?_ }
  · intro v
    simpa only [hmin] using P.phase v
  · intro u v he
    simpa only [hmin] using P.drop (lift he)
  · intro v k hv
    apply P.high v k
    simpa only [hmin] using hv
  · intro u v hb ht hu hv
    have hu' : ∃ k, s.minLabel u = some k := by simpa only [hmin] using hu
    have hv' : ∃ k, s.minLabel v = some k := by simpa only [hmin] using hv
    simpa only [BridgeEndpointArms, hmin] using P.tops u v hb ht hu' hv'

private theorem refreshKnownEdge_predecessors [DecidableRel G.Adj]
    (s : State V) (u v : V) :
    (refreshKnownEdge M u v s).predecessors = s.predecessors := by
  unfold refreshKnownEdge
  split
  · split <;> rfl
  · rfl

private theorem refreshKnownEdges_predecessors [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) :
    (refreshKnownEdges M xs s).predecessors = s.predecessors := by
  induction xs generalizing s with
  | nil => rfl
  | cons e es ih =>
    exact (ih (refreshKnownEdge M e.1 e.2 s)).trans (refreshKnownEdge_predecessors s e.1 e.2)

section Finite
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G} [DecidableRel G.Adj]

theorem maxProcessVertex_predecessors (M : Matching G) (i : Nat) (v : Fin n)
    (s : State (Fin n)) : (maxProcessVertex M i v s).predecessors = s.predecessors := by
  have ha : (assignMax s (2 * i + 1) v).predecessors = s.predecessors := by
    unfold assignMax
    split <;> rfl
  unfold maxProcessVertex
  dsimp only
  split
  · exact ha
  · split
    · exact (refreshKnownEdges_predecessors _ _).trans ha
    · exact ha

theorem maxProcessVertices_predecessors (M : Matching G) (i : Nat) (vs : List (Fin n))
    (s : State (Fin n)) : (maxProcessVertices M i vs s).predecessors = s.predecessors := by
  induction vs generalizing s with
  | nil => rfl
  | cons v vs ih =>
    exact (ih (maxProcessVertex M i v s)).trans (maxProcessVertex_predecessors M i v s)

namespace PetalRecord
variable {cut : Nat}

omit [DecidableRel G.Adj] in
/-- The preserved current-level representation proves each computed new root
belongs to the actual trigger support, after any preceding same-level events. -/
theorem newRoots_support_of_current (R : PetalRecord M)
    (P : CurrentBridgeRepresentation M cut R.invariant)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hten : R.tenacity = cut + 2) (v : Fin n) (hv : v ∈ R.newRoots) :
    MaximumMatching.tenacity M v = some R.tenacity ∧ InSupport M R.left R.right v := by
  obtain ⟨hsel, hne⟩ := (R.mem_newRoots v).1 hv
  have hh := P.colored_region_support hc htop R.left R.right R.trigger.1
    (by rw [← hten]; exact R.trigger.2) R.starts_assigned.1 R.starts_assigned.2
    R.bottleneck R.selected R.trees R.region v hsel hne
  exact ⟨by simpa only [hten] using hh.1, hh.2⟩

/-- Actual assignment and incident refresh preserve the full stage and graph
invariants, and correctly label exactly the supplied computed root list. -/
theorem maxEvent_correct_of_current (R : PetalRecord M)
    (P : CurrentBridgeRepresentation M cut R.invariant) (i cutoff : Nat)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hten : R.tenacity = cut + 2) (hstageTen : cut + 2 = 2 * i + 1)
    (_hcap : R.cap = i + 1) (hstage : StageState M (i + 1) cutoff R.prior) :
    StageState M (i + 1) cutoff (R.maxEvent i).1 ∧
      BudGraphInvariant M (i + 1) (R.maxEvent i).1 (R.maxEvent i).2 ∧
      (∀ v, v ∈ R.newRoots → (R.maxEvent i).1.maxLabel v = maxlevel M v) ∧
      (∀ v k, R.prior.maxLabel v = some k → (R.maxEvent i).1.maxLabel v = some k) := by
  have hroots : ∀ v, v ∈ R.newRoots → MaximumMatching.tenacity M v = some (2 * i + 1) := by
    intro v hv
    have hh := (R.newRoots_support_of_current P hc htop hten v hv).1
    simpa only [hten, hstageTen] using hh
  have hs := maxProcessVertices_stageState M i cutoff R.newRoots R.prior hstage hroots
  refine ⟨hs, ?_, ?_, ?_⟩
  · refine ⟨hs.min, hs.minBound, ?_, ?_⟩
    · intro v k hv
      have hold : R.prior.minLabel v = some k := (R.maxEvent_minLabel i v).symm.trans hv
      obtain ⟨j, hj⟩ := R.after_invariant.rootAssigned v k hold
      exact ⟨j, (R.maxEvent_minLabel i (R.after.root v)).trans hj⟩
    · intro v
      exact (R.after_invariant.rankLabel v).trans (congrArg (fun x : Option Nat => x.getD 0)
        (R.maxEvent_minLabel i v).symm)
  · intro v hv
    exact maxProcessVertices_member_correct M i cutoff R.newRoots R.prior hstage hroots v hv
  · intro v k hv
    exact maxProcessVertices_preserves_known_maxLabel M i cutoff R.newRoots R.prior hstage hroots v k hv

/-- The actual updated state and forest carry the constructed representation
for subsequent current-level bridges. Only the independently proved graph
invariant is supplied; the path data are preserved from the preceding event. -/
noncomputable def maxEvent_representation (R : PetalRecord M)
    (P : CurrentBridgeRepresentation M cut R.invariant) (i : Nat) {cap' : Nat}
    (h' : BudGraphInvariant M cap' (R.maxEvent i).1 R.after) :
    CurrentBridgeRepresentation M cut h' :=
  (R.afterBridgeRepresentation P).of_same_min_data h'
    (funext (R.maxEvent_minLabel i)) (maxProcessVertices_predecessors M i R.newRoots R.prior)

end PetalRecord
end Finite
end MaximumMatching.Search

end PetalCurrentMax
