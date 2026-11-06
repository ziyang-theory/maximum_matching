import MaximumMatching.PetalMax

/-! Operational facts for processing a fixed complete current-tenacity bucket.
All queued current bridges have computable tenacity, and actual MAX refreshes
retain every previously queued edge. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

theorem current_bridge_tenacity_available (s : State V) (i : Nat)
    (hc : MinCompleteBelow M i s) (hx : MaxCompleteBelowTenacity M (2 * i + 1) s)
    (u v : V) (hb : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (2 * i + 1)) :
    edgeTenacity M s u v = some (2 * i + 1) := by
  by_cases hm : M.mate u = some v
  · obtain ⟨j, huj, _, hum, hvm, _, _, hsum⟩ := matched_bridge_levels hb hm (2 * i + 1) ht
    have hji : j = i := by omega
    have hjodd := level_parity M 1 u j huj
    have hu := hc u j hum (by omega)
    have hv := hc v j hvm (by omega)
    simp [edgeTenacity, hm, parityLabel, hu, hv, hjodd,
      show j + j + 1 = 2 * i + 1 by omega]
  · exact unmatched_bridge_tenacity_available s i u v hc hx hb hm ht

theorem StageState.current_bridge_known {i : Nat} {s : State V}
    (h : StageState M (i + 1) (2 * i + 1) s) (u v : V)
    (hb : Bridge M u v) (ht : MaximumMatching.edgeTenacity M u v = some (2 * i + 1)) :
    edgeTenacity M s u v = some (2 * i + 1) :=
  current_bridge_tenacity_available s i
    (fun w k hw hk => h.min.2.1 w k hw (by omega)) h.maxComplete u v hb ht

theorem assignMax_bucket (s : State V) (t : Nat) (x : V) :
    (assignMax s t x).bucket = s.bucket := by
  unfold assignMax
  split <;> rfl

section Finite
variable {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]

theorem maxProcessVertices_bucket_mono (M : Matching G) (i : Nat) (s : State (Fin n))
    (xs : List (Fin n)) (u v : Fin n) (t : Nat) (h : (u, v) ∈ s.bucket t) :
    (u, v) ∈ (maxProcessVertices M i xs s).bucket t := by
  induction xs generalizing s with
  | nil => exact h
  | cons x xs ih => exact ih _ (maxProcessVertex_bucket_mono M i x u v s t h)

theorem PetalRecord.maxEvent_bucket_mono {M : Matching G} (R : PetalRecord M) (i : Nat)
    (u v : Fin n) (t : Nat) (h : (u, v) ∈ R.prior.bucket t) :
    (u, v) ∈ (R.maxEvent i).1.bucket t :=
  maxProcessVertices_bucket_mono M i R.prior R.newRoots u v t h

end Finite
end MaximumMatching.Search
