import MaximumMatching.MatchingSearchGraph
import MaximumMatching.DDFSRootTargets

/-! A concrete matching-state DDFS event. Its graph comes from recorded MIN
predecessors and current bud roots. The event retains the computed outcome,
contracts its actual bottleneck region, and preserves the graph invariant.
Identifying the region with matching bridge support remains separate. -/
namespace MaximumMatching.BudForest
variable {V : Type} [DecidableEq V]

theorem mergeInto_root_predicate (F : BudForest V) (A : V → Prop)
    (hA : ∀ v, A v → A (F.root v)) (x b : V) (hb : A b) :
    ∀ v, A v → A ((F.mergeInto x b).root v) := by
  intro v hv
  rw [F.mergeInto_root]
  split
  · exact hA b hb
  · exact hA v hv

theorem mergeManyInto_root_predicate (F : BudForest V) (A : V → Prop)
    (hA : ∀ v, A v → A (F.root v)) (xs : List V) (b : V) (hb : A b) :
    ∀ v, A v → A ((F.mergeManyInto xs b).root v) := by
  induction xs generalizing F with
  | nil => exact hA
  | cons x xs ih => exact ih (F.mergeInto x b) (F.mergeInto_root_predicate A hA x b hb)

end MaximumMatching.BudForest

namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}
variable {i : Nat} {s : State (Fin n)} {F : BudForest (Fin n)}

/-- Execute the finite search graph computed from actual MIN lists, starting
at the current buds of the supplied matching vertices, then contract its
actual bottleneck region. The full certified DDFS output is retained. -/
def executeBudSearch (h : BudGraphInvariant M i s F) (r g : Fin n) :
    DDFS.Machine.FullOutput (predecessorGraph s F h) (F.root r) (F.root g) × BudForest (Fin n) :=
  DDFS.Machine.executeAndContract h.reachBottom (F.root r) (F.root g) F

theorem executeBudSearch_rank (h : BudGraphInvariant M i s F) (r g v : Fin n) :
    (executeBudSearch h r g).2.rank v = F.rank v :=
  DDFS.Machine.executeAndContract_rank h.reachBottom (F.root r) (F.root g) F v

/-- Active matching starts ensure that all returned search vertices are
assigned fixed bud roots. In the disjoint case both bottom vertices are
genuinely free in the original matching. -/
theorem executeBudSearch_vertices (h : BudGraphInvariant M i s F) (r g : Fin n)
    (hr : ∃ k, s.minLabel r = some k) (hg : ∃ k, s.minLabel g = some k) :
    match (executeBudSearch h r g).1 with
    | .disjoint p q _ _ _ => M.Free p.last ∧ M.Free q.last ∧
        (∀ j, (∃ k, s.minLabel (p.vertex j) = some k) ∧ F.parent (p.vertex j) = p.vertex j) ∧
        (∀ j, (∃ k, s.minLabel (q.vertex j) = some k) ∧ F.parent (q.vertex j) = q.vertex j)
    | .bottleneck b S _ _ _ => (∃ k, s.minLabel b = some k) ∧
        ∀ v, S v → (∃ k, s.minLabel v = some k) ∧ F.parent v = v := by
  have hrootr : ∃ k, s.minLabel (F.root r) = some k := by
    obtain ⟨k, hk⟩ := hr
    exact h.rootAssigned r k hk
  have hrootg : ∃ k, s.minLabel (F.root g) = some k := by
    obtain ⟨k, hk⟩ := hg
    exact h.rootAssigned g k hk
  have paths (p : DDFS.Path (predecessorGraph s F h))
      (hp : p.first = F.root r ∨ p.first = F.root g) :
      ∀ j, (∃ k, s.minLabel (p.vertex j) = some k) ∧ F.parent (p.vertex j) = p.vertex j := by
    have ha : ∃ k, s.minLabel p.first = some k := by
      rcases hp with hp | hp
      · rw [hp]; exact hrootr
      · rw [hp]; exact hrootg
    have hf : F.parent p.first = p.first := by
      rcases hp with hp | hp
      · rw [hp]; exact F.root_fixed r
      · rw [hp]; exact F.root_fixed g
    intro j
    exact ⟨h.path_assigned p ha j, h.path_fixed p hf j⟩
  change match DDFS.Machine.executeFull h.reachBottom (F.root r) (F.root g) with
    | .disjoint p q _ _ _ => _
    | .bottleneck b S _ _ _ => _
  cases hout : DDFS.Machine.executeFull h.reachBottom (F.root r) (F.root g) with
  | disjoint p q hp hq hd =>
    exact ⟨h.path_bottom_free p (by rw [hp.1]; exact hrootr) hp.2,
      h.path_bottom_free q (by rw [hq.1]; exact hrootg) hq.2,
      paths p (Or.inl hp.1), paths q (Or.inr hq.1)⟩
  | bottleneck b S trees highest region =>
    have hvertices : ∀ v, S v → (∃ k, s.minLabel v = some k) ∧ F.parent v = v := by
      intro v hv
      obtain ⟨p, hp, _, j, hj⟩ := (region v).1 hv
      simpa only [hj] using paths p hp j
    exact ⟨(hvertices b trees.bottleneck_mem).1, hvertices⟩

/-- The actual finite contraction preserves every field needed to run the
next matching-derived DDFS graph. Its target is assigned by the actual
searched paths, rather than an assumed support invariant. -/
theorem executeBudSearch_preserves (h : BudGraphInvariant M i s F) (r g : Fin n)
    (hr : ∃ k, s.minLabel r = some k) (hg : ∃ k, s.minLabel g = some k) :
    BudGraphInvariant M i s (executeBudSearch h r g).2 := by
  have hvertices := executeBudSearch_vertices h r g hr hg
  change BudGraphInvariant M i s
    ((DDFS.Machine.executeFull h.reachBottom (F.root r) (F.root g)).contract F)
  change (match DDFS.Machine.executeFull h.reachBottom (F.root r) (F.root g) with
    | .disjoint p q _ _ _ => _
    | .bottleneck b S _ _ _ => _) at hvertices
  cases hout : DDFS.Machine.executeFull h.reachBottom (F.root r) (F.root g) with
  | disjoint p q hp hq hd => exact h
  | bottleneck b S trees highest region =>
    rw [hout] at hvertices
    refine ⟨h.minInvariant, h.labelsBounded, ?_, ?_⟩
    · intro v k hv
      apply F.mergeManyInto_root_predicate (fun w => ∃ j, s.minLabel w = some j) ?_
        trees.vertices b hvertices.1 v ⟨k, hv⟩
      intro w hw
      obtain ⟨j, hj⟩ := hw
      exact h.rootAssigned w j hj
    · intro v
      exact (F.mergeManyInto_rank trees.vertices b v).trans (h.rankLabel v)

/-- Every selected old bud class collapses to the actual reported
bottleneck. Root representation is derived from the matching graph itself. -/
theorem executeBudSearch_contracts (h : BudGraphInvariant M i s F) (r g b : Fin n)
    (S : Fin n → Prop) (trees : DDFS.ColoredTrees (predecessorGraph s F h) S (F.root r) (F.root g) b)
    (highest : DDFS.HighestBottleneck (predecessorGraph s F h) (F.root r) (F.root g) b)
    (region : ∀ v, S v ↔ DDFS.OnRootTo (H := predecessorGraph s F h) (F.root r) (F.root g) b v)
    (hout : DDFS.Machine.executeFull h.reachBottom (F.root r) (F.root g) =
      .bottleneck b S trees highest region)
    (v : Fin n) (hv : S (F.root v)) : (executeBudSearch h r g).2.root v = b := by
  exact DDFS.Machine.executeAndContract_root_targets h.reachBottom (F.root r) (F.root g) F
    b S trees highest region hout h.rankLabel (fun _ _ he => h.edge_target_fixed he)
    (F.root_fixed r) (F.root_fixed g) v hv

end MaximumMatching.Search
