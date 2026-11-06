import MaximumMatching.FiberWeightedExpansion
import MaximumMatching.MatchingGraphExpansion

/-! Initialize actual fiber-based path expansion from lower-blossom
representation. MIN coverage forces every lower-blossom member into the
unique represented fiber, so segment containment is derived for all original
vertices, not merely assumed for those already named by a DDFS path. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}
namespace BudGraphInvariant
variable {cap cut : Nat} {s : State V} {F : BudForest V}

/-- At the actual search-stage range, all vertices in a lower blossom are
assigned by MIN and belong to its represented root's exact fiber. -/
theorem lower_blossom_fiber (h : BudGraphInvariant M cap s F)
    (hcap : cut ≤ 2 * cap + 1) (hrep : LowerBlossomRepresentation M cut s F)
    (b v : V) (hb : levelLT (some cut) (tenacity M b)) (hbl : Blossom M cut b v) :
    F.root v = b := by
  obtain ⟨t, hvt, htc⟩ := blossom_tenacity_bound cut b v hbl
  obtain ⟨e, o, he, ho, hep, hop, hsum⟩ := finite_levels_of_tenacity v t hvt
  have hmin : minlevel M v = some (min e o) := by simp only [minlevel, he, ho, levelMin]
  have hbound : min e o ≤ cap := by omega
  have hv : s.minLabel v = some (min e o) := h.minInvariant.2.1 v (min e o) hmin hbound
  obtain ⟨hrhigh, hvfiber⟩ := hrep v (min e o) hv
  rcases hvfiber with hvr | hvbl
  · rw [← hvr, hvt] at hrhigh
    change cut < t at hrhigh
    omega
  · by_cases heq : F.root v = b
    · exact heq
    · exact False.elim (blossoms_disjoint_same_tenacity cut (F.root v) b
        hrhigh hb heq v ⟨hvbl, hbl⟩)

/-- Instantiate the fiber interface from constructed predecessor segments.
This establishes the starting representation before same-level petal updates. -/
noncomputable def fiberWeightedMatching (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut < p.length)
    (hhalf : 2 * cap ≤ cut + 3) (hcap : cut ≤ 2 * cap + 1)
    (hrep : LowerBlossomRepresentation M cut s F) :
    DDFS.FiberWeightedMatching M (predecessorGraph s F h) F where
  phase := (h.weightedMatching hc hnoaug hhalf hrep).phase
  segment := (h.weightedMatching hc hnoaug hhalf hrep).segment
  first := (h.weightedMatching hc hnoaug hhalf hrep).first
  last := (h.weightedMatching hc hnoaug hhalf hrep).last
  start_phase := (h.weightedMatching hc hnoaug hhalf hrep).start_phase
  end_phase := (h.weightedMatching hc hnoaug hhalf hrep).end_phase
  interior := by
    intro u v he i hi hil
    obtain ⟨k, hk⟩ := h.edge_target_assigned he
    have hv : levelLT (some cut) (tenacity M v) := by
      have hh := (hrep v k hk).1
      rwa [F.root_of_fixed v (h.edge_target_fixed he)] at hh
    exact h.lower_blossom_fiber hcap hrep v _ hv
      ((h.weightedMatching hc hnoaug hhalf hrep).interior he i hi hil)

theorem fiberWeightedMatching_drop (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut < p.length)
    (hhalf : 2 * cap ≤ cut + 3) (hcap : cut ≤ 2 * cap + 1)
    (hrep : LowerBlossomRepresentation M cut s F)
    {u v : V} (he : (predecessorGraph s F h).Edge u v) :
    ((h.fiberWeightedMatching hc hnoaug hhalf hcap hrep).segment he).length +
      (s.minLabel v).getD 0 = (s.minLabel u).getD 0 :=
  h.weightedMatching_drop hc hnoaug hhalf hrep he

end BudGraphInvariant
end MaximumMatching.Search
