import MaximumMatching.PetalRootExpansion
import MaximumMatching.BridgeTopSegments

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
