import MaximumMatching.SupportPathEdges
import MaximumMatching.SupportBridgeGeometry
import MaximumMatching.SupportBridgePrefix
import MaximumMatching.DDFSPathCompression

/-! Compress original maximum-level path intervals into the actual executable
predecessor/bud graph. Every graph edge is derived from a real predecessor and
lower-blossom membership, and the returned paths retain exactly the original
high vertices. Both results include the shortest augmentation threshold. -/
namespace MaximumMatching.Search.BudGraphInvariant
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}
variable {cap cut : Nat} {s : State V} {F : BudForest V}

omit [DecidableEq V] in
private theorem high_cut_lift (v : V) (hc : cut % 2 = 1)
    (hv : levelLT (some cut) (tenacity M v)) : levelLE (some (cut + 2)) (tenacity M v) := by
  cases ht : tenacity M v with
  | none => trivial
  | some t =>
    have htodd := tenacity_odd M v t ht
    rw [ht] at hv
    change cut < t at hv
    change cut + 2 ≤ t
    omega

omit [DecidableEq V] in
private theorem low_of_not_high (v : V)
    (hv : ¬levelLT (some cut) (tenacity M v)) : levelLE (tenacity M v) (some cut) := by
  cases ht : tenacity M v with
  | none => exact False.elim (hv (by rw [ht]; trivial))
  | some t =>
    have hh : ¬cut < t := by simpa only [ht, levelLT] using hv
    change t ≤ cut
    omega

/-- Reverse-compress the increasing half, from a named high vertex before
the current bridge all the way to the original free start. -/
theorem compress_early_core (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1) (ht : AtMostShortestAugmenting M (cut + 2))
    (hrep : LowerBlossomRepresentation M cut s F) (hcap : cut + 2 ≤ 2 * cap + 1)
    (p : AltPath M) (hpt : tenacity M p.last = some (cut + 2))
    (hmax : maxlevel M p.last = some p.length) (I : Fin p.length)
    (hIb : Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩))
    (hIt : MaximumMatching.edgeTenacity M (p.vertex ⟨I.val, by omega⟩)
      (p.vertex ⟨I.val + 1, by omega⟩) = some (cut + 2))
    (A : Fin (p.length + 1)) (hAI : A.val ≤ I.val)
    (hA : levelLT (some cut) (tenacity M (p.vertex A))) :
    ∃ q : DDFS.Path (predecessorGraph s F h), q.first = p.vertex A ∧ q.last = p.first ∧
      q.length ≤ A.val ∧ ∀ v, q.Contains v ↔
        ∃ K : Fin (p.length + 1), K.val ≤ A.val ∧
          levelLT (some cut) (tenacity M (p.vertex K)) ∧ p.vertex K = v := by
  have hp := p.shortest_of_maxlevel hmax
  have hnoaug : ∀ q : AltPath M, q.Augmenting → cut < q.length := by
    intro q hq; have := ht q hq; omega
  let high := fun K : Fin (p.length + 1) => levelLT (some cut) (tenacity M (p.vertex K))
  have hroot : high ⟨0, by omega⟩ := free_tenacity_above M cut p.first p.start_free hnoaug
  obtain ⟨q, hqf, hql, hqn, hqv⟩ := DDFS.path_of_reverse_consecutive_indices
    (H := predecessorGraph s F h) p.vertex high ⟨0, by omega⟩ A (by simp) hroot hA (by
      intro J K _ hJK hKA hJ hK hgap
      have hKhigh := high_cut_lift (p.vertex K) hc hK
      have hKmin := p.current_bridge_before_minlevel (cut + 2) ht hpt hmax I hIb hIt K
        (by omega) hKhigh
      obtain ⟨k, hk, hks⟩ := p.maxlevel_high_vertex_minlevel_lt_half hp (cut + 2) hpt hmax K hKhigh
      have he : k = K.val := Option.some.inj (hk.symm.trans hKmin)
      have hKcap : K.val ≤ cap := by omega
      exact h.early_stretch_edge hc hnoaug hrep p J K hJK hKcap hKmin hJ
        (fun L hJL hLK => low_of_not_high (p.vertex L) (hgap L hJL hLK)))
  refine ⟨q, hqf, hql, by simpa only [Nat.sub_zero] using hqn, ?_⟩
  intro v
  simpa only [Nat.zero_le, true_and, high] using hqv v

/-- Compress the descending half from a named high vertex after the bridge
to the maximum-level endpoint. Complementary levels and jump parities are
derived internally, not passed as a graph invariant. -/
theorem compress_late_core (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1) (ht : AtMostShortestAugmenting M (cut + 2))
    (hrep : LowerBlossomRepresentation M cut s F) (hcap : cut + 2 ≤ 2 * cap + 1)
    (p : AltPath M) (hpt : tenacity M p.last = some (cut + 2))
    (hmax : maxlevel M p.last = some p.length) (I : Fin p.length)
    (hIb : Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩))
    (hIt : MaximumMatching.edgeTenacity M (p.vertex ⟨I.val, by omega⟩)
      (p.vertex ⟨I.val + 1, by omega⟩) = some (cut + 2))
    (A : Fin (p.length + 1)) (hIA : I.val < A.val)
    (hA : levelLT (some cut) (tenacity M (p.vertex A))) :
    ∃ q : DDFS.Path (predecessorGraph s F h), q.first = p.vertex A ∧ q.last = p.last ∧
      q.length ≤ p.length - A.val ∧ ∀ v, q.Contains v ↔
        ∃ K : Fin (p.length + 1), A.val ≤ K.val ∧
          levelLT (some cut) (tenacity M (p.vertex K)) ∧ p.vertex K = v := by
  have hnoaug : ∀ q : AltPath M, q.Augmenting → cut < q.length := by
    intro q hq; have := ht q hq; omega
  let high := fun K : Fin (p.length + 1) => levelLT (some cut) (tenacity M (p.vertex K))
  have hend : high ⟨p.length, by omega⟩ := by
    change levelLT (some cut) (tenacity M p.last)
    rw [hpt]; change cut < cut + 2; omega
  obtain ⟨q, hqf, hql, hqn, hqv⟩ := DDFS.path_of_consecutive_indices
    (H := predecessorGraph s F h) p.vertex high A ⟨p.length, by omega⟩ (by change A.val ≤ p.length; omega) hA hend (by
      intro J K hAJ hJK _ hJ hK hgap
      obtain ⟨hJt, hJmin, _, hJh⟩ := p.current_bridge_after_geometry (cut + 2) ht hpt hmax
        I hIb hIt J (by omega) (high_cut_lift (p.vertex J) hc hJ)
      obtain ⟨hKt, hKmin, hKb, _⟩ := p.current_bridge_after_geometry (cut + 2) ht hpt hmax
        I hIb hIt K (by omega) (high_cut_lift (p.vertex K) hc hK)
      have hJcap : cut + 2 - J.val ≤ cap := by omega
      exact h.late_consecutive_high_edge hc hnoaug hrep p J K hJK hKb hJh hJcap hJmin hKmin
        hJ hKt (fun L hJL hLK => low_of_not_high (p.vertex L) (hgap L hJL hLK)))
  refine ⟨q, hqf, hql, hqn, ?_⟩
  intro v
  constructor
  · intro hv
    obtain ⟨K, hAK, _, hK, hKv⟩ := (hqv v).1 hv
    exact ⟨K, hAK, hK, hKv⟩
  · rintro ⟨K, hAK, hK, hKv⟩
    exact (hqv v).2 ⟨K, hAK, by change K.val ≤ p.length; have := K.isLt; omega, hK, hKv⟩

end MaximumMatching.Search.BudGraphInvariant
