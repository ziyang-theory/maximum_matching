import MaximumMatching.BlockingBucketAccounting
import MaximumMatching.AugmentingPathArms
import MaximumMatching.FreeEdgePhase

/-! Deleting a recovered path's bud fibers and recursively removing live
vertices with no remaining predecessor. Vertex-contained bottom arms of a
disjoint shortest path survive this exact operation. -/
namespace MaximumMatching.Search.ActiveSearchState
variable {n i cut : Nat} {G : Graph (Fin n)} {M : Matching G}

/-- Bottom arms whose trigger roots are genuinely live. The explicit root
membership excludes isolated inactive vertices assigned layer zero. -/
def LiveBridgeArms (S : ActiveSearchState M i cut) (u v : Fin n) (Q : Fin n → Prop) : Prop :=
  S.B.forest.root u ∈ S.live ∧ S.B.forest.root v ∈ S.live ∧
    BottomBridgeArms S.graph S.B.forest u v Q

/-- Delete the specified root names and perform predecessor cleanup. Labels,
original predecessor lists, and computed fiber routes retain their meaning. -/
def remove (S : ActiveSearchState M i cut) (forbidden : List (Fin n)) :
    ActiveSearchState M i cut where
  B := S.B
  A := S.A
  live := DDFS.RecursiveRemoval.remove
    (predecessorGraph S.B.state S.B.forest S.B.bud) S.live forbidden
  live_fixed v hv := S.live_fixed v
    (DDFS.RecursiveRemoval.remove_avoids _ S.live forbidden v hv).1
  reach := DDFS.RecursiveRemoval.remove_reachBottom _ S.live forbidden

theorem remove_live (S : ActiveSearchState M i cut) (forbidden : List (Fin n))
    (v : Fin n) (hv : v ∈ (S.remove forbidden).live) :
    v ∈ S.live ∧ v ∉ forbidden :=
  DDFS.RecursiveRemoval.remove_avoids _ S.live forbidden v hv

theorem remove_monotone (S : ActiveSearchState M i cut) (forbidden : List (Fin n)) :
    S.Monotone (S.remove forbidden) :=
  Monotone.of_live_subset (fun _ => rfl) (fun v hv => (S.remove_live forbidden v hv).1)

/-- Surviving disjoint arms retain exactly their previous original-vertex
containment predicate after deletion and recursive pruning. -/
theorem LiveBridgeArms.remove {S : ActiveSearchState M i cut} {u v : Fin n}
    {Q : Fin n → Prop} (h : S.LiveBridgeArms u v Q) (forbidden : List (Fin n))
    (havoid : ∀ w, Q w → w ∉ forbidden) :
    (S.remove forbidden).LiveBridgeArms u v Q := by
  obtain ⟨hu, hv, p, q, hp, hq, hd, hpQ, hqQ⟩ := h
  have hpLive : ∀ j, p.vertex j ∈ S.live := fun j =>
    S.path_live p (hp.1.symm ▸ hu) _ ⟨j, rfl⟩
  have hqLive : ∀ j, q.vertex j ∈ S.live := fun j =>
    S.path_live q (hq.1.symm ▸ hv) _ ⟨j, rfl⟩
  have hpBottom := S.liftPath_bottom p (hp.1.symm ▸ hu) hp.2
  have hqBottom := S.liftPath_bottom q (hq.1.symm ▸ hv) hq.2
  have hpNew := DDFS.RecursiveRemoval.remove_preserves_bottom_path
    (predecessorGraph S.B.state S.B.forest S.B.bud) S.live forbidden
    (S.liftPath p) hpBottom hpLive (fun j => havoid _ (hpQ _ ⟨j, rfl⟩))
  have hqNew := DDFS.RecursiveRemoval.remove_preserves_bottom_path
    (predecessorGraph S.B.state S.B.forest S.B.bud) S.live forbidden
    (S.liftPath q) hqBottom hqLive (fun j => havoid _ (hqQ _ ⟨j, rfl⟩))
  let a := DDFS.RecursiveRemoval.restrictPath _ (S.remove forbidden).live (S.liftPath p) hpNew
  let b := DDFS.RecursiveRemoval.restrictPath _ (S.remove forbidden).live (S.liftPath q) hqNew
  refine ⟨?_, ?_, a, b, ⟨hp.1, ?_⟩, ⟨hq.1, ?_⟩, hd, hpQ, hqQ⟩
  · exact hp.1 ▸ hpNew ⟨0, by omega⟩
  · exact hq.1 ▸ hqNew ⟨0, by omega⟩
  · change (if p.last ∈ (S.remove forbidden).live then (S.B.state.minLabel p.last).getD 0 else 0) = 0
    have hv : p.last ∈ (S.remove forbidden).live := hpNew ⟨p.length, by change p.length < p.length + 1; omega⟩
    rw [ite_eq_left hv]
    exact hpBottom
  · change (if q.last ∈ (S.remove forbidden).live then (S.B.state.minLabel q.last).getD 0 else 0) = 0
    have hv : q.last ∈ (S.remove forbidden).live := hqNew ⟨q.length, by change q.length < q.length + 1; omega⟩
    rw [ite_eq_left hv]
    exact hqBottom

/-- Bud roots of every original vertex on a recovered augmentation. -/
def pathRoots (S : ActiveSearchState M i cut) (p : AltPath M) : List (Fin n) :=
  (List.finRange (p.length + 1)).map (fun j => S.B.forest.root (p.vertex j))

theorem mem_pathRoots (S : ActiveSearchState M i cut) (p : AltPath M) (v : Fin n) :
    v ∈ S.pathRoots p ↔ ∃ j, S.B.forest.root (p.vertex j) = v := by
  simp only [pathRoots, List.mem_map, List.mem_finRange, true_and]

/-- Every vertex of a removed path has an inactive root afterwards. -/
theorem pathRoots_inactive (S : ActiveSearchState M i cut) (p : AltPath M)
    (j : Fin (p.length + 1)) :
    (S.remove (S.pathRoots p)).B.forest.root (p.vertex j) ∉
      (S.remove (S.pathRoots p)).live := by
  intro hv
  exact (S.remove_live _ _ hv).2 ((S.mem_pathRoots p _).2 ⟨j, rfl⟩)

/-- If expansion includes the root of each path vertex, forbidding its root
classes removes no vertex of a disjoint path. -/
theorem pathRoots_avoids_disjoint (S : ActiveSearchState M i cut) (p q : AltPath M)
    (hclosed : ∀ j, ∃ k, p.vertex k = S.B.forest.root (p.vertex j))
    (hd : p.Disjoint q) (w : Fin n) (hw : ∃ j, q.vertex j = w) :
    w ∉ S.pathRoots p := by
  intro hm
  obtain ⟨j, hj⟩ := (S.mem_pathRoots p w).1 hm
  obtain ⟨k, hk⟩ := hclosed j
  obtain ⟨l, hl⟩ := hw
  exact hd k l (hk.trans (hj.trans hl.symm))

theorem LiveBridgeArms.remove_path {S : ActiveSearchState M i cut} {u v : Fin n}
    {p q : AltPath M} (h : S.LiveBridgeArms u v (fun w => ∃ j, q.vertex j = w))
    (hclosed : ∀ j, ∃ k, p.vertex k = S.B.forest.root (p.vertex j))
    (hd : p.Disjoint q) :
    (S.remove (S.pathRoots p)).LiveBridgeArms u v (fun w => ∃ j, q.vertex j = w) :=
  h.remove _ (S.pathRoots_avoids_disjoint p q hclosed hd)

end MaximumMatching.Search.ActiveSearchState
