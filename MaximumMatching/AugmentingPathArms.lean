import MaximumMatching.CurrentBucketAugmenting
import MaximumMatching.RecursiveRemovalTransport

/-! Vertex-contained bottom arms for shortest augmentations. The containment
predicate is retained explicitly so deletion can preserve a disjoint path. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

def BottomBridgeArms (H : DDFS.LayeredGraph V) (F : BudForest V)
    (u v : V) (Q : V → Prop) : Prop :=
  ∃ a b : DDFS.Path H, a.ToBottom (F.root u) ∧ b.ToBottom (F.root v) ∧
    a.Disjoint b ∧ (∀ w, a.Contains w → Q w) ∧ (∀ w, b.Contains w → Q w)

namespace BottomBridgeArms

theorem symm {H : DDFS.LayeredGraph V} {F : BudForest V} {u v : V} {Q : V → Prop}
    (h : BottomBridgeArms H F u v Q) : BottomBridgeArms H F v u Q := by
  obtain ⟨a, b, ha, hb, hd, hqa, hqb⟩ := h
  exact ⟨b, a, hb, ha, (fun w hb ha => hd w ha hb), hqb, hqa⟩

theorem of_same_min_data {cap cap' : Nat} {s s' : State V} {F : BudForest V}
    {h : BudGraphInvariant M cap s F} {u v : V} {Q : V → Prop}
    (ha : BottomBridgeArms (predecessorGraph s F h) F u v Q)
    (h' : BudGraphInvariant M cap' s' F)
    (hmin : s'.minLabel = s.minLabel) (hpred : s'.predecessors = s.predecessors) :
    BottomBridgeArms (predecessorGraph s' F h') F u v Q := by
  rw [predecessorGraph_eq_of_fields h h' hmin hpred]
  exact ha

end BottomBridgeArms

namespace BudGraphInvariant
variable {cap cut : Nat} {s : State V} {F : BudForest V}

/-- Compress a shortest augmentation without losing the original-vertex
containment of either arm. Both terminal vertices are free. -/
theorem augmenting_bridge_arms (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1) (ht : AtMostShortestAugmenting M (cut + 2))
    (hrep : LowerBlossomRepresentation M cut s F) (hcap : cut + 2 ≤ 2 * cap + 1)
    (p : AltPath M) (hp : p.Augmenting) (hlen : p.length = cut + 2)
    (I : Fin p.length)
    (hIb : Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩))
    (hIt : MaximumMatching.edgeTenacity M (p.vertex ⟨I.val, by omega⟩)
      (p.vertex ⟨I.val + 1, by omega⟩) = some (cut + 2))
    (hu : ∃ k, s.minLabel (p.vertex ⟨I.val, by omega⟩) = some k)
    (hv : ∃ k, s.minLabel (p.vertex ⟨I.val + 1, by omega⟩) = some k) :
    BottomBridgeArms (predecessorGraph s F h) F
      (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩)
      (fun w => ∃ j, p.vertex j = w) := by
  obtain ⟨hpt, hmax⟩ := p.shortest_augmenting_last_levels hp (hlen ▸ ht)
  rw [hlen] at hpt
  obtain ⟨A, hAI, hA, hAh⟩ := h.current_bridge_left_root hrep p ht hpt hmax I hIb hIt hu
  obtain ⟨J, hIJ, hJ, hJt⟩ := h.current_bridge_right_root hrep p ht hpt hmax I hIb hIt hv
  have hJh : levelLT (some cut) (tenacity M (p.vertex J)) := by
    rw [hJt]; change cut < cut + 2; omega
  obtain ⟨a, haf, hal, _, hav⟩ := h.compress_early_core hc ht hrep hcap p hpt hmax I hIb hIt A hAI hAh
  obtain ⟨b, hbf, hbl, _, hbv⟩ := h.compress_late_core hc ht hrep hcap p hpt hmax I hIb hIt J hIJ hJh
  refine ⟨a, b, ⟨haf.trans hA, ?_⟩, ⟨hbf.trans hJ, ?_⟩, ?_, ?_, ?_⟩
  · have hl := h.minInvariant.2.1 p.first 0 ((minlevel_zero_iff_free p.first).2 p.start_free)
      (Nat.zero_le cap)
    change (s.minLabel a.last).getD 0 = 0
    rw [hal, hl]; rfl
  · have hl := h.minInvariant.2.1 p.last 0 ((minlevel_zero_iff_free p.last).2 hp.2)
      (Nat.zero_le cap)
    change (s.minLabel b.last).getD 0 = 0
    rw [hbl, hl]; rfl
  · intro w haw hbw
    obtain ⟨K, hKA, _, hKw⟩ := (hav w).1 haw
    obtain ⟨L, hJL, _, hLw⟩ := (hbv w).1 hbw
    have he := congrArg Fin.val (p.injective K L (hKw.trans hLw.symm))
    omega
  · intro w hw
    obtain ⟨K, _, _, hKw⟩ := (hav w).1 hw
    exact ⟨K, hKw⟩
  · intro w hw
    obtain ⟨K, _, _, hKw⟩ := (hbv w).1 hw
    exact ⟨K, hKw⟩

end BudGraphInvariant

section Finite
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

theorem CurrentBucketState.augmenting_bridge_arms {i cut : Nat}
    (B : CurrentBucketState M i cut) (hc : cut % 2 = 1)
    (ht : AtMostShortestAugmenting M (cut + 2)) (hstageTen : cut + 2 = 2 * i + 1)
    (hrep : LowerBlossomRepresentation M cut B.state B.forest)
    (p : AltPath M) (hp : p.Augmenting) (hlen : p.length = 2 * i + 1) :
    ∃ u v, Bridge M u v ∧ MaximumMatching.edgeTenacity M u v = some (2 * i + 1) ∧
      BottomBridgeArms (predecessorGraph B.state B.forest B.bud) B.forest u v
        (fun w => ∃ j, p.vertex j = w) := by
  have hl : p.length = cut + 2 := hlen.trans hstageTen.symm
  obtain ⟨hpt, hmax⟩ := p.shortest_augmenting_last_levels hp (hl ▸ ht)
  obtain ⟨I, hIb, hIt, _⟩ := p.general_maxlevel_path_unique_bridge (cut + 2) ht
    (by rwa [hl] at hpt) hmax
  have hk := B.stage.current_bridge_known _ _ hIb (by rwa [← hstageTen])
  obtain ⟨hu, hv⟩ := edgeTenacity_has_minLabels B.state _ _ (2 * i + 1) hk
  exact ⟨_, _, hIb, by rwa [← hstageTen],
    B.bud.augmenting_bridge_arms hc ht hrep (by omega) p hp hl I hIb hIt hu hv⟩

namespace PetalRecord

theorem transport_bottom_bridge_arms (R : PetalRecord M) {u v : Fin n} {Q : Fin n → Prop}
    (ha : BottomBridgeArms (predecessorGraph R.prior R.forest R.invariant) R.forest u v Q) :
    BottomBridgeArms (predecessorGraph R.prior R.after R.after_invariant) R.after u v Q := by
  obtain ⟨p, q, hp, hq, hd, hpQ, hqQ⟩ := ha
  have hpf : R.forest.parent p.first = p.first := by rw [hp.1]; exact R.forest.root_fixed u
  have hqf : R.forest.parent q.first = q.first := by rw [hq.1]; exact R.forest.root_fixed v
  have hpfix : ∀ x, p.Contains x → R.forest.root x = x := by
    rintro x ⟨j, rfl⟩
    exact R.forest.root_of_fixed _ (R.invariant.path_fixed p hpf j)
  have hqfix : ∀ x, q.Contains x → R.forest.root x = x := by
    rintro x ⟨j, rfl⟩
    exact R.forest.root_of_fixed _ (R.invariant.path_fixed q hqf j)
  obtain ⟨a, b, haf, hal, hbf, hbl, hab, hav, hbv⟩ :=
    R.transport_disjoint_bottom_paths p q hpfix hqfix hd hp.2 hq.2
  refine ⟨a, b, ⟨?_, ?_⟩, ⟨?_, ?_⟩, hab, fun w hw => hpQ w (hav w hw),
    fun w hw => hqQ w (hbv w hw)⟩
  · exact haf.trans ((congrArg R.after.root hp.1).trans (R.after_root_old_root u))
  · change (R.prior.minLabel a.last).getD 0 = 0
    rw [hal]; exact hp.2
  · exact hbf.trans ((congrArg R.after.root hq.1).trans (R.after_root_old_root v))
  · change (R.prior.minLabel b.last).getD 0 = 0
    rw [hbl]; exact hq.2

end PetalRecord
end Finite
end MaximumMatching.Search
