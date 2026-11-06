import MaximumMatching.OperationalArms
import MaximumMatching.RecoverableBucket
import MaximumMatching.RecursiveRemoval
import MaximumMatching.ShortestAugmentingSearch

section ActiveSearchGraph

/-! The live predecessor graph used after paths have been removed during a
blocking phase. Labels and original predecessor lists retain their full-graph
meaning; live DDFS searches use the explicitly restricted root graph. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

/-- A current-level state with computed routes and an explicit list of live
bud roots. Original vertices are live through membership of their bud root. -/
structure ActiveSearchState (M : Matching G) (i cut : Nat) where
  B : CurrentBucketState M i cut
  A : OperationalArms M B.state B.forest
  live : List (Fin n)
  live_fixed : ∀ v, v ∈ live → B.forest.root v = v
  reach : DDFS.ReachBottom (DDFS.RecursiveRemoval.restricted
    (predecessorGraph B.state B.forest B.bud) live)

namespace ActiveSearchState
variable {i cut : Nat}

abbrev graph (S : ActiveSearchState M i cut) :=
  DDFS.RecursiveRemoval.restricted (predecessorGraph S.B.state S.B.forest S.B.bud) S.live

instance (S : ActiveSearchState M i cut) : DecidableRel S.graph.Edge :=
  inferInstanceAs (DecidableRel (DDFS.RecursiveRemoval.restricted _ _).Edge)

/-- Lift a live graph path by retaining its actual vertex sequence. -/
def liftPath (S : ActiveSearchState M i cut) (p : DDFS.Path S.graph) :
    DDFS.Path (predecessorGraph S.B.state S.B.forest S.B.bud) where
  length := p.length
  vertex := p.vertex
  adjacent j := (p.adjacent j).2.2

theorem path_live (S : ActiveSearchState M i cut) (p : DDFS.Path S.graph)
    (hf : p.first ∈ S.live) (v : Fin n) (hv : p.Contains v) : v ∈ S.live := by
  obtain ⟨j, rfl⟩ := hv
  exact DDFS.RecursiveRemoval.restricted_path_live _ _ p hf j

theorem level_live (S : ActiveSearchState M i cut) (v : Fin n) (hv : v ∈ S.live) :
    S.graph.level v = (S.B.state.minLabel v).getD 0 := by
  change (if v ∈ S.live then _ else 0) = _
  exact ite_eq_left hv

theorem liftPath_bottom (S : ActiveSearchState M i cut) (p : DDFS.Path S.graph)
    (hf : p.first ∈ S.live) (hb : S.graph.level p.last = 0) :
    (predecessorGraph S.B.state S.B.forest S.B.bud).level (S.liftPath p).last = 0 := by
  have hv := S.path_live p hf p.last p.contains_last
  exact (S.level_live p.last hv).symm.trans hb

end ActiveSearchState
end MaximumMatching.Search

end ActiveSearchGraph

section ActiveSearchInitial

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

end ActiveSearchInitial

section ActivePathRecovery

/-! Recover a shortest augmentation from the actual live DDFS arms. Expansion
uses stored parity routes, remains in live fibers, and contains both trigger
roots. The latter facts justify the next path deletion. -/
namespace MaximumMatching.Search.ActiveSearchState
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G} {i cut : Nat}

def recoverLivePath (S : ActiveSearchState M i cut)
    (htop : AtMostShortestAugmenting M (cut + 2)) (hstageTen : cut + 2 = 2 * i + 1)
    (u v : Fin n) (he : (u, v) ∈ S.B.state.bucket (2 * i + 1))
    (hu : S.B.forest.root u ∈ S.live) (hv : S.B.forest.root v ∈ S.live)
    (p q : DDFS.Path S.graph) (hp : p.ToBottom (S.B.forest.root u))
    (hq : q.ToBottom (S.B.forest.root v)) (hd : p.Disjoint q) :
    { z : AltPath M // z.Augmenting ∧ z.length = 2 * i + 1 ∧
      (∀ w, (∃ j, z.vertex j = w) → S.B.forest.root w ∈ S.live) ∧
      RootClosed S.B.forest z ∧
      (∃ j, z.vertex j = S.B.forest.root u) ∧ (∃ j, z.vertex j = S.B.forest.root v) } := by
  have hb := S.B.stage.classification.2.2 (2 * i + 1) u v he
  have hk := S.B.stage.current_bridge_known u v hb.1 hb.2
  have hpLive : p.first ∈ S.live := hp.1.symm ▸ hu
  have hqLive : q.first ∈ S.live := hq.1.symm ▸ hv
  let z := S.A.recoverShortestAugmentingWithCore S.B.stage.min.1 (S.A.weighted S.B.stage S.B.bud)
    (fun _ => rfl) (fun e => S.A.weighted_drop S.B.stage S.B.bud e)
    u v (2 * i + 1) hb.1.1 hk (by omega) (hstageTen ▸ htop)
    (S.liftPath p) (S.liftPath q)
    ⟨hp.1, S.liftPath_bottom p hpLive hp.2⟩
    ⟨hq.1, S.liftPath_bottom q hqLive hq.2⟩ hd
  have hfibers := z.property.2.2.2.2.2.2.1
  have hcore := z.property.2.2.2.2.2.2.2
  refine ⟨z.val, z.property.1, z.property.2.2.2.1, ?_,
    rootClosed_of_core_coverage S.B.forest z.val _ hfibers hcore, ?_, ?_⟩
  · intro w hw
    rcases hfibers w hw with hr | hg
    · exact S.path_live p hpLive _ hr
    · exact S.path_live q hqLive _ hg
  · exact hcore _ (Or.inl (hp.1 ▸ p.contains_first))
  · exact hcore _ (Or.inr (hq.1 ▸ q.contains_first))

end MaximumMatching.Search.ActiveSearchState

end ActivePathRecovery

section BlockingBucketAccounting

/-! Trigger accounting for a deletion-aware blocking bucket. A processed
trigger either has one current bud or has lost an endpoint's live bud. Both
conditions persist through later live-only contractions and removals. -/
namespace MaximumMatching.Search.ActiveSearchState
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G} {i cut : Nat}

/-- A trigger no longer needs a distinct-live-root DDFS call. -/
def Accounted (S : ActiveSearchState M i cut) (u v : Fin n) : Prop :=
  S.B.forest.root u = S.B.forest.root v ∨
    S.B.forest.root u ∉ S.live ∨ S.B.forest.root v ∉ S.live

/-- Later operations do not split old classes or revive an inactive class.
The relation concerns original vertices, so a live contraction may change
which fixed root names a surviving class. -/
structure Monotone (S T : ActiveSearchState M i cut) : Prop where
  roots : ∀ u v, S.B.forest.root u = S.B.forest.root v →
    T.B.forest.root u = T.B.forest.root v
  inactive : ∀ v, S.B.forest.root v ∉ S.live → T.B.forest.root v ∉ T.live

namespace Monotone

theorem refl (S : ActiveSearchState M i cut) : Monotone S S :=
  ⟨fun _ _ h => h, fun _ h => h⟩

theorem trans {S T U : ActiveSearchState M i cut} (hST : Monotone S T)
    (hTU : Monotone T U) : Monotone S U :=
  ⟨fun u v h => hTU.roots u v (hST.roots u v h),
    fun v h => hTU.inactive v (hST.inactive v h)⟩

/-- Removing vertices while retaining the forest is monotone. -/
theorem of_live_subset {S T : ActiveSearchState M i cut}
    (hroot : ∀ v, T.B.forest.root v = S.B.forest.root v)
    (hsub : ∀ v, v ∈ T.live → v ∈ S.live) : Monotone S T := by
  constructor
  · intro u v h
    rw [hroot, hroot]
    exact h
  · intro v h hv
    apply h
    rw [hroot] at hv
    exact hsub _ hv

end Monotone

namespace Accounted

theorem symm {S : ActiveSearchState M i cut} {u v : Fin n}
    (h : S.Accounted u v) : S.Accounted v u := by
  rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem mono {S T : ActiveSearchState M i cut} (hST : Monotone S T)
    {u v : Fin n} (h : S.Accounted u v) : T.Accounted u v := by
  rcases h with h | h | h
  · exact Or.inl (hST.roots u v h)
  · exact Or.inr (Or.inl (hST.inactive u h))
  · exact Or.inr (Or.inr (hST.inactive v h))

/-- A surviving pair of disjoint live-root arms witnesses an unaccounted
trigger. This is the final contradiction used for maximality. -/
theorem excludes_disjoint_arms {S : ActiveSearchState M i cut} {u v : Fin n}
    (h : S.Accounted u v) (hu : S.B.forest.root u ∈ S.live)
    (hv : S.B.forest.root v ∈ S.live)
    (p q : DDFS.Path S.graph) (hp : p.first = S.B.forest.root u)
    (hq : q.first = S.B.forest.root v) (hd : p.Disjoint q) : False := by
  rcases h with he | he | he
  · have hh : p.first = q.first := hp.trans (he.trans hq.symm)
    exact hd p.first p.contains_first (hh ▸ q.contains_first)
  · exact he hu
  · exact he hv

end Accounted
end MaximumMatching.Search.ActiveSearchState

end BlockingBucketAccounting

section BlockingBucketRemoval

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

/-- If expansion includes the root of each path vertex, no forbidden root name
occurs on a disjoint path. This preserves its vertex-contained bottom arms;
whole-fiber deletion can still deactivate other original vertices. -/
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

end BlockingBucketRemoval

section BlockingBucketResult

/-! The invariant returned by a continued blocking-bucket scan. All returned
paths have the original matching and level. Surviving bottom arms transport
through the same contractions and recursive removals used by the execution. -/
namespace MaximumMatching.Search
variable {n i cut : Nat} {G : Graph (Fin n)} {M : Matching G}

structure BlockingBucketResult (S : ActiveSearchState M i cut)
    (es : List (Fin n × Fin n)) where
  state : ActiveSearchState M i cut
  family : AugmentingFamily M
  monotone : S.Monotone state
  queued : ∀ u v t, (u, v) ∈ S.B.state.bucket t → (u, v) ∈ state.B.state.bucket t
  accounted : ∀ e, e ∈ es → state.Accounted e.1 e.2
  lengths : ∀ j, (family.path j).length = 2 * i + 1
  live : ∀ j k, S.B.forest.root ((family.path j).vertex k) ∈ S.live
  inactive : ∀ j k, state.B.forest.root ((family.path j).vertex k) ∉ state.live
  survives : ∀ q : AltPath M, (∀ j, (family.path j).Disjoint q) →
    ∀ u v, S.LiveBridgeArms u v (fun w => ∃ k, q.vertex k = w) →
      state.LiveBridgeArms u v (fun w => ∃ k, q.vertex k = w)

namespace BlockingBucketResult

/-- The completed scan has no remaining trigger and adds no path. -/
def done (S : ActiveSearchState M i cut) : BlockingBucketResult S [] where
  state := S
  family := .empty
  monotone := .refl S
  queued _ _ _ h := h
  accounted _ h := False.elim (List.not_mem_nil h)
  lengths j := nomatch j
  live j := nomatch j
  inactive j := nomatch j
  survives _ _ _ _ h := h

/-- Record a discharged head trigger after the remaining scan has finished. -/
def account {S : ActiveSearchState M i cut} {e : Fin n × Fin n}
    {es : List (Fin n × Fin n)} (R : BlockingBucketResult S es)
    (ha : R.state.Accounted e.1 e.2) : BlockingBucketResult S (e :: es) where
  state := R.state
  family := R.family
  monotone := R.monotone
  queued := R.queued
  accounted f hf := by
    rcases List.mem_cons.mp hf with he | hf
    · cases he
      exact ha
    · exact R.accounted f hf
  lengths := R.lengths
  live := R.live
  inactive := R.inactive
  survives := R.survives

/-- A trigger already accounted in the input needs no DDFS operation. -/
def skip {S : ActiveSearchState M i cut} {e : Fin n × Fin n}
    {es : List (Fin n × Fin n)} (ha : S.Accounted e.1 e.2)
    (R : BlockingBucketResult S es) : BlockingBucketResult S (e :: es) :=
  R.account (ha.mono R.monotone)

/-- Compose a live contraction with the rest of the actual scan. -/
def advance {S T : ActiveSearchState M i cut} {es : List (Fin n × Fin n)}
    (hmono : S.Monotone T)
    (hqueue : ∀ u v t, (u, v) ∈ S.B.state.bucket t → (u, v) ∈ T.B.state.bucket t)
    (htransport : ∀ q : AltPath M, ∀ u v,
      S.LiveBridgeArms u v (fun w => ∃ k, q.vertex k = w) →
      T.LiveBridgeArms u v (fun w => ∃ k, q.vertex k = w))
    (R : BlockingBucketResult T es) : BlockingBucketResult S es where
  state := R.state
  family := R.family
  monotone := hmono.trans R.monotone
  queued u v t h := R.queued u v t (hqueue u v t h)
  accounted := R.accounted
  lengths := R.lengths
  live j k := by
    by_cases hh : S.B.forest.root ((R.family.path j).vertex k) ∈ S.live
    · exact hh
    · exact False.elim (hmono.inactive _ hh (R.live j k))
  inactive := R.inactive
  survives q hd u v h := R.survives q hd u v (htransport q u v h)

/-- Add a recovered augmentation, remove its root classes, and continue on
that exact pruned state. Future paths are disjoint because their initial roots
remain live after this removal. -/
def prependRemoved (S : ActiveSearchState M i cut) (p : AltPath M)
    (hp : p.Augmenting) (hlen : p.length = 2 * i + 1)
    (hlive : ∀ j, S.B.forest.root (p.vertex j) ∈ S.live)
    (hclosed : ∀ j, ∃ k, p.vertex k = S.B.forest.root (p.vertex j))
    {es : List (Fin n × Fin n)} (R : BlockingBucketResult (S.remove (S.pathRoots p)) es) :
    BlockingBucketResult S es := by
  have hd : ∀ j, p.Disjoint (R.family.path j) := by
    intro j a b he
    have hh := (S.remove_live _ _ (R.live j b)).2
    apply hh
    exact (S.mem_pathRoots p _).2 ⟨a, congrArg S.B.forest.root he⟩
  let F := R.family.prepend p hp hd
  refine {
    state := R.state
    family := F
    monotone := (S.remove_monotone _).trans R.monotone
    queued := R.queued
    accounted := R.accounted
    lengths := ?_
    live := ?_
    inactive := ?_
    survives := ?_ }
  · intro j
    change (if h : j.val = 0 then p else R.family.path ⟨j.val - 1, _⟩).length = _
    split
    · exact hlen
    · exact R.lengths _
  · intro j
    by_cases hz : j.val = 0
    · have he : F.path j = p := dite_eq_left hz
      rw [he]
      exact hlive
    · have he : F.path j = R.family.path ⟨j.val - 1, by have := j.isLt; change j.val < R.family.count + 1 at this; omega⟩ := dite_eq_right hz
      rw [he]
      intro k
      exact (S.remove_live _ _ (R.live _ k)).1
  · intro j
    by_cases hz : j.val = 0
    · have he : F.path j = p := dite_eq_left hz
      rw [he]
      intro k
      exact R.monotone.inactive _ (S.pathRoots_inactive p k)
    · have he : F.path j = R.family.path ⟨j.val - 1, by have := j.isLt; change j.val < R.family.count + 1 at this; omega⟩ := dite_eq_right hz
      rw [he]
      exact R.inactive _
  · intro q hdis u v h
    have hpq : p.Disjoint q := hdis ⟨0, by change 0 < R.family.count + 1; omega⟩
    have hRq : ∀ j, (R.family.path j).Disjoint q := by
      intro j
      have hh := hdis ⟨j.val + 1, by change j.val + 1 < R.family.count + 1; omega⟩
      simpa only [F, AugmentingFamily.prepend, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, dite_false, Nat.add_sub_cancel, Fin.eta] using hh
    exact R.survives q hRq u v (h.remove_path hclosed hpq)

/-- Exhausting a complete trigger list yields a maximal family of shortest
augmentations: a disjoint shortest path would retain live disjoint arms at an
accounted trigger. -/
theorem maximalShortest {S : ActiveSearchState M i cut} {es : List (Fin n × Fin n)}
    (R : BlockingBucketResult S es) (htop : AtMostShortestAugmenting M (2 * i + 1))
    (hcover : ∀ p : AltPath M, p.Augmenting → p.length = 2 * i + 1 →
      ∃ u v, (u, v) ∈ es ∧ S.LiveBridgeArms u v (fun w => ∃ j, p.vertex j = w)) :
    R.family.MaximalShortest (2 * i + 1) := by
  refine ⟨htop, R.lengths, ?_⟩
  intro p hp hlen hd
  obtain ⟨u, v, he, ha⟩ := hcover p hp hlen
  obtain ⟨hu, hv, a, b, haf, hbf, hab, _⟩ := R.survives p hd u v ha
  exact (R.accounted (u, v) he).excludes_disjoint_arms hu hv a b haf.1 hbf.1 hab

end BlockingBucketResult
end MaximumMatching.Search

end BlockingBucketResult
