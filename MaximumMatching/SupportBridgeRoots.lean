import MaximumMatching.SupportPathCompression
import MaximumMatching.SupportBridgeRight

/-! The actual two bridge buds occur on opposite sides of a maximum-level
support witness. Combining their original high-index intervals yields two
disjoint paths in the executable predecessor graph. -/
namespace MaximumMatching.Search.BudGraphInvariant
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}
variable {cap cut : Nat} {s : State V} {F : BudForest V}

theorem current_bridge_left_root (_h : BudGraphInvariant M cap s F)
    (hrep : LowerBlossomRepresentation M cut s F)
    (p : AltPath M) (ht : AtMostShortestAugmenting M (cut + 2))
    (hpt : tenacity M p.last = some (cut + 2)) (hmax : maxlevel M p.last = some p.length)
    (I : Fin p.length)
    (hIb : Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩))
    (hIt : MaximumMatching.edgeTenacity M (p.vertex ⟨I.val, by omega⟩)
      (p.vertex ⟨I.val + 1, by omega⟩) = some (cut + 2))
    (hu : ∃ k, s.minLabel (p.vertex ⟨I.val, by omega⟩) = some k) :
    ∃ A : Fin (p.length + 1), A.val ≤ I.val ∧
      p.vertex A = F.root (p.vertex ⟨I.val, by omega⟩) ∧
      levelLT (some cut) (tenacity M (p.vertex A)) := by
  obtain ⟨k, hk⟩ := hu
  obtain ⟨hh, hfiber⟩ := hrep _ k hk
  rcases hfiber with he | hbl
  · exact ⟨⟨I.val, by omega⟩, Nat.le_refl _, he, by rw [he]; exact hh⟩
  · let q := p.take I.val (by omega)
    have hq := p.current_bridge_prefix_honest (cut + 2) ht hpt hmax I hIb hIt
    obtain ⟨A, hA, _, _, _, _⟩ := blossom_on_shortest cut
      (F.root (p.vertex ⟨I.val, by omega⟩)) q.last hbl q rfl hq
    have hAb : A.val ≤ I.val := by have := A.isLt; change A.val < I.val + 1 at this; omega
    refine ⟨⟨A.val, by omega⟩, hAb, hA, ?_⟩
    change levelLT (some cut) (tenacity M (q.vertex A))
    rw [hA]
    exact hh

theorem current_bridge_right_root (h : BudGraphInvariant M cap s F)
    (hrep : LowerBlossomRepresentation M cut s F)
    (p : AltPath M) (ht : AtMostShortestAugmenting M (cut + 2))
    (hpt : tenacity M p.last = some (cut + 2)) (hmax : maxlevel M p.last = some p.length)
    (I : Fin p.length)
    (hIb : Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩))
    (hIt : MaximumMatching.edgeTenacity M (p.vertex ⟨I.val, by omega⟩)
      (p.vertex ⟨I.val + 1, by omega⟩) = some (cut + 2))
    (hv : ∃ k, s.minLabel (p.vertex ⟨I.val + 1, by omega⟩) = some k) :
    ∃ J : Fin (p.length + 1), I.val < J.val ∧
      p.vertex J = F.root (p.vertex ⟨I.val + 1, by omega⟩) ∧
      tenacity M (p.vertex J) = some (cut + 2) := by
  obtain ⟨k, hk⟩ := hv
  obtain ⟨J, hIJ, hJt, hlow⟩ := p.current_bridge_right_blossom (cut + 2) ht hpt hmax I hIb hIt
  have hJhigh : levelLT (some cut) (tenacity M (p.vertex J)) := by
    rw [hJt]; change cut < cut + 2; omega
  refine ⟨J, hIJ, ?_, hJt⟩
  by_cases he : I.val + 1 = J.val
  · have heFin : (⟨I.val + 1, by omega⟩ : Fin (p.length + 1)) = J := Fin.ext he
    rw [heFin] at hk ⊢
    exact (h.root_eq_of_high hrep _ k hk hJhigh).symm
  · have hbl := hlow ⟨I.val + 1, by omega⟩
      (by change I.val < I.val + 1; omega) (by change I.val + 1 < J.val; omega)
    exact (h.root_eq_of_lower_member hrep _ _ k hk hJhigh
      (by simpa only [Nat.add_sub_cancel] using hbl)).symm

/-- A semantic maximum-level support witness produces the two actual graph
arms: one bud reaches the original free start, and the other reaches the
supported vertex. Their original index intervals certify disjointness. -/
theorem current_bridge_graph_arms (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1) (ht : AtMostShortestAugmenting M (cut + 2))
    (hrep : LowerBlossomRepresentation M cut s F) (hcap : cut + 2 ≤ 2 * cap + 1)
    (p : AltPath M) (hpt : tenacity M p.last = some (cut + 2))
    (hmax : maxlevel M p.last = some p.length) (I : Fin p.length)
    (hIb : Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩))
    (hIt : MaximumMatching.edgeTenacity M (p.vertex ⟨I.val, by omega⟩)
      (p.vertex ⟨I.val + 1, by omega⟩) = some (cut + 2))
    (hu : ∃ k, s.minLabel (p.vertex ⟨I.val, by omega⟩) = some k)
    (hv : ∃ k, s.minLabel (p.vertex ⟨I.val + 1, by omega⟩) = some k) :
    ∃ a b : DDFS.Path (predecessorGraph s F h),
      a.first = F.root (p.vertex ⟨I.val, by omega⟩) ∧ a.last = p.first ∧
      b.first = F.root (p.vertex ⟨I.val + 1, by omega⟩) ∧ b.last = p.last ∧
      a.Disjoint b ∧ (predecessorGraph s F h).level a.last = 0 := by
  obtain ⟨A, hAI, hA, hAh⟩ := h.current_bridge_left_root hrep p ht hpt hmax I hIb hIt hu
  obtain ⟨J, hIJ, hJ, hJt⟩ := h.current_bridge_right_root hrep p ht hpt hmax I hIb hIt hv
  have hJh : levelLT (some cut) (tenacity M (p.vertex J)) := by
    rw [hJt]; change cut < cut + 2; omega
  obtain ⟨a, haf, hal, _, hav⟩ := h.compress_early_core hc ht hrep hcap p hpt hmax I hIb hIt A hAI hAh
  obtain ⟨b, hbf, hbl, _, hbv⟩ := h.compress_late_core hc ht hrep hcap p hpt hmax I hIb hIt J hIJ hJh
  refine ⟨a, b, haf.trans hA, hal, hbf.trans hJ, hbl, ?_, ?_⟩
  · intro v hav' hbv'
    obtain ⟨K, hKA, _, hKv⟩ := (hav v).1 hav'
    obtain ⟨L, hJL, _, hLv⟩ := (hbv v).1 hbv'
    have he := congrArg Fin.val (p.injective K L (hKv.trans hLv.symm))
    omega
  · have hf : minlevel M p.first = some 0 := (minlevel_zero_iff_free p.first).2 p.start_free
    have hl := h.minInvariant.2.1 p.first 0 hf (Nat.zero_le cap)
    change (s.minLabel a.last).getD 0 = 0
    rw [hal, hl]
    rfl

end MaximumMatching.Search.BudGraphInvariant
