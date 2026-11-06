import MaximumMatching.ActiveSearchGraph
import MaximumMatching.AugmentingPathArms

/-! Initialize the deletion-aware graph from all current bud roots. No
vertices have been removed at this boundary. -/
namespace MaximumMatching.Search.ActiveSearchState
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G} {i cut : Nat}

def initialLive (B : CurrentBucketState M i cut) : List (Fin n) :=
  (List.finRange n).filter (fun v => decide (B.forest.root v = v))

theorem mem_initialLive (B : CurrentBucketState M i cut) (v : Fin n) :
    v ∈ initialLive B ↔ B.forest.root v = v := by
  simp [initialLive]

theorem initial_path_live (B : CurrentBucketState M i cut)
    (p : DDFS.Path (predecessorGraph B.state B.forest B.bud))
    (hf : B.forest.root p.first = p.first) : ∀ j, p.vertex j ∈ initialLive B := by
  intro j
  apply (mem_initialLive B _).2
  have hpf : B.forest.parent p.first = p.first := by
    rw [← hf]
    exact B.forest.root_fixed p.first
  exact B.forest.root_of_fixed _ (B.bud.path_fixed p hpf j)

theorem initial_reach (B : CurrentBucketState M i cut) :
    DDFS.ReachBottom (DDFS.RecursiveRemoval.restricted
      (predecessorGraph B.state B.forest B.bud) (initialLive B)) := by
  intro v
  by_cases hv : v ∈ initialLive B
  · obtain ⟨p, hp, hb⟩ := B.bud.reachBottom v
    have hl := initial_path_live B p (by rw [hp]; exact (mem_initialLive B v).1 hv)
    refine ⟨DDFS.RecursiveRemoval.restrictPath _ _ p hl, hp, ?_⟩
    change (if p.last ∈ initialLive B then (B.state.minLabel p.last).getD 0 else 0) = 0
    rw [ite_eq_left (show p.last ∈ initialLive B from hl ⟨p.length, by omega⟩)]
    exact hb
  · refine ⟨DDFS.Path.trivial _ v, rfl, ?_⟩
    change (if v ∈ initialLive B then _ else 0) = 0
    exact ite_eq_right hv

def initial (B : CurrentBucketState M i cut) (A : OperationalArms M B.state B.forest) :
    ActiveSearchState M i cut where
  B := B
  A := A
  live := initialLive B
  live_fixed := fun v hv => (mem_initialLive B v).1 hv
  reach := initial_reach B

theorem initial_root_live (B : CurrentBucketState M i cut)
    (A : OperationalArms M B.state B.forest) (v : Fin n) :
    B.forest.root v ∈ (initial B A).live :=
  (mem_initialLive B _).2 (B.forest.root_idempotent v)

theorem initial_arms (B : CurrentBucketState M i cut)
    (A : OperationalArms M B.state B.forest) {u v : Fin n} {Q : Fin n → Prop}
    (h : BottomBridgeArms (predecessorGraph B.state B.forest B.bud) B.forest u v Q) :
    BottomBridgeArms (initial B A).graph B.forest u v Q := by
  obtain ⟨p, q, hp, hq, hd, hpQ, hqQ⟩ := h
  have hpl := initial_path_live B p (by rw [hp.1]; exact B.forest.root_idempotent u)
  have hql := initial_path_live B q (by rw [hq.1]; exact B.forest.root_idempotent v)
  refine ⟨DDFS.RecursiveRemoval.restrictPath _ _ p hpl,
    DDFS.RecursiveRemoval.restrictPath _ _ q hql, ⟨hp.1, ?_⟩, ⟨hq.1, ?_⟩, hd, hpQ, hqQ⟩
  · change (if p.last ∈ initialLive B then (B.state.minLabel p.last).getD 0 else 0) = 0
    rw [ite_eq_left (show p.last ∈ initialLive B from hpl ⟨p.length, by omega⟩)]; exact hp.2
  · change (if q.last ∈ initialLive B then (B.state.minLabel q.last).getD 0 else 0) = 0
    rw [ite_eq_left (show q.last ∈ initialLive B from hql ⟨q.length, by omega⟩)]; exact hq.2

end MaximumMatching.Search.ActiveSearchState
