import MaximumMatching.MatchingGraphExpansion
import MaximumMatching.SupportPathReverse

/-! Identify edges of the actual predecessor/bud graph along original path
stretches. Lower-blossom membership determines the operational root by
disjointness, rather than assuming a jump edge or contraction equality. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Matching edges cannot cross a tenacity cutoff, so a nonempty low stretch
starts after an even index and ends before an odd one. -/
theorem low_stretch_boundary_parities (p : AltPath M) (cut : Nat)
    (A J : Fin (p.length + 1)) (hAJ : A.val + 1 < J.val)
    (hA : levelLT (some cut) (tenacity M (p.vertex A)))
    (hJ : levelLT (some cut) (tenacity M (p.vertex J)))
    (hlow : ∀ K : Fin (p.length + 1), A.val < K.val → K.val < J.val →
      levelLE (tenacity M (p.vertex K)) (some cut)) :
    A.val % 2 = 0 ∧ J.val % 2 = 1 := by
  have incompatible (u v : V) (hh : levelLT (some cut) (tenacity M u))
      (hl : levelLE (tenacity M v) (some cut)) (hm : M.mate u = some v) : False := by
    have he := (matched_tenacity M hm).1
    rw [he] at hh
    cases hv : tenacity M v with
    | none => simp only [hv, levelLE] at hl
    | some k =>
      rw [hv] at hh hl
      change cut < k at hh
      change k ≤ cut at hl
      omega
  constructor
  · by_cases he : A.val % 2 = 0
    · exact he
    · have hm := p.mate_next A.val (by have := J.isLt; omega) (by omega)
      exact False.elim (incompatible _ _ hA
        (hlow ⟨A.val + 1, by have := J.isLt; omega⟩
          (by change A.val < A.val + 1; omega) (by change A.val + 1 < J.val; exact hAJ)) hm)
  · by_cases ho : J.val % 2 = 1
    · exact ho
    · have hm := p.mate_previous J.val (by omega) (by omega) (by omega)
      exact False.elim (incompatible _ _ hJ
        (hlow ⟨J.val - 1, by omega⟩ (by change A.val < J.val - 1; omega)
          (by change J.val - 1 < J.val; omega)) hm)

end MaximumMatching.AltPath

namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

namespace BudGraphInvariant
variable {cap cut : Nat} {s : State V} {F : BudForest V}

theorem root_eq_of_high (_h : BudGraphInvariant M cap s F)
    (hrep : LowerBlossomRepresentation M cut s F) (v : V) (k : Nat)
    (hv : s.minLabel v = some k) (hhigh : levelLT (some cut) (tenacity M v)) :
    F.root v = v := by
  rcases (hrep v k hv).2 with he | hbl
  · exact he.symm
  · obtain ⟨t, ht, htc⟩ := blossom_tenacity_bound cut (F.root v) v hbl
    rw [ht] at hhigh
    change cut < t at hhigh
    omega

theorem root_eq_of_lower_member (_h : BudGraphInvariant M cap s F)
    (hrep : LowerBlossomRepresentation M cut s F) (v b : V) (k : Nat)
    (hv : s.minLabel v = some k) (hb : levelLT (some cut) (tenacity M b))
    (hbl : Blossom M cut b v) : F.root v = b := by
  obtain ⟨hrhigh, hfiber⟩ := hrep v k hv
  rcases hfiber with he | hrbl
  · obtain ⟨t, ht, htc⟩ := blossom_tenacity_bound cut b v hbl
    rw [← he, ht] at hrhigh
    change cut < t at hrhigh
    omega
  · apply Classical.byContradiction
    intro hne
    exact blossoms_disjoint_same_tenacity cut (F.root v) b hrhigh hb hne v ⟨hrbl, hbl⟩

theorem edge_of_predecessor (h : BudGraphInvariant M cap s F) (u v : V) (k : Nat)
    (hv : s.minLabel v = some k) (hp : Predecessor M u v) :
    (predecessorGraph s F h).Edge v (F.root u) := by
  refine ⟨by simp only [hv, Option.isSome_some], ?_⟩
  exact List.mem_map.mpr ⟨u, (h.listed_iff u v k hv).2 hp, rfl⟩

omit [DecidableEq V] in
private theorem bases_below_cut (cut : Nat)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut < p.length) :
    ∀ (v : V) (t : Nat), tenacity M v = some t → t ≤ cut → ∃ b, IsBase M v b := by
  intro v t ht htc
  have helig : EligibleTenacity M t := by
    refine ⟨tenacity_odd M v t ht, ⟨v, ?_⟩, ?_⟩
    · rw [ht]; exact Nat.le_refl _
    · intro p hp; have := hnoaug p hp; omega
  obtain ⟨b, hb, _⟩ := general_unique_base M t helig v ht
  exact ⟨b, t, ht, hb⟩

/-- Consecutive high vertices on the increasing half give the actual reverse
predecessor/bud edge. The intervening original low stretch is contracted to
its proved boundary, and the adjacent case uses the original predecessor. -/
theorem early_stretch_edge (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut < p.length)
    (hrep : LowerBlossomRepresentation M cut s F)
    (p : AltPath M) (A J : Fin (p.length + 1)) (hAJ : A.val < J.val)
    (hJcap : J.val ≤ cap) (hJmin : minlevel M (p.vertex J) = some J.val)
    (hAhigh : levelLT (some cut) (tenacity M (p.vertex A)))
    (hlow : ∀ K : Fin (p.length + 1), A.val < K.val → K.val < J.val →
      levelLE (tenacity M (p.vertex K)) (some cut)) :
    (predecessorGraph s F h).Edge (p.vertex J) (p.vertex A) := by
  have hJlabel := h.minInvariant.2.1 (p.vertex J) J.val hJmin hJcap
  let U : Fin (p.length + 1) := ⟨J.val - 1, by omega⟩
  have hpred : Predecessor M (p.vertex U) (p.vertex J) := by
    refine ⟨p.take J.val (by omega), rfl, hJmin, ?_, rfl⟩
    change 0 < J.val
    omega
  obtain ⟨k, hk, _⟩ := h.predecessor_assigned _ _ J.val hJlabel hpred
  have he := h.edge_of_predecessor _ _ J.val hJlabel hpred
  have hroot : F.root (p.vertex U) = p.vertex A := by
    by_cases hadj : A.val + 1 = J.val
    · have hUA : U = A := Fin.ext (by change J.val - 1 = A.val; omega)
      rw [hUA] at hk ⊢
      exact h.root_eq_of_high hrep _ k hk hAhigh
    · have hbl := (p.low_stretch_boundary cut hc (bases_below_cut cut hnoaug) A J
        (by omega) hJmin hAhigh hlow).1
      exact h.root_eq_of_lower_member hrep _ _ k hk hAhigh hbl
  simpa only [hroot] using he

/-- Adjacent descending high vertices also give a genuine reverse
predecessor, using their complementary minimum levels and the actual edge's
matching parity. -/
theorem late_adjacent_edge (h : BudGraphInvariant M cap s F)
    (hrep : LowerBlossomRepresentation M cut s F)
    (p : AltPath M) (t : Nat) (ht : t % 2 = 1)
    (A J : Fin (p.length + 1)) (hAJ : A.val + 1 = J.val) (hJt : J.val ≤ t)
    (hAcap : t - A.val ≤ cap)
    (hAmin : minlevel M (p.vertex A) = some (t - A.val))
    (hJmin : minlevel M (p.vertex J) = some (t - J.val))
    (hJhigh : levelLT (some cut) (tenacity M (p.vertex J))) :
    (predecessorGraph s F h).Edge (p.vertex A) (p.vertex J) := by
  have hAlabel := h.minInvariant.2.1 _ _ hAmin hAcap
  have hJlabel := h.minInvariant.2.1 _ _ hJmin (by omega)
  have hpred : Predecessor M (p.vertex J) (p.vertex A) := by
    apply predecessor_of_consecutive_minlevels M _ _ (t - J.val) hJmin
      (by simpa only [show t - J.val + 1 = t - A.val by omega] using hAmin)
    · have he := G.symm (p.adjacent ⟨A.val, by have := J.isLt; omega⟩)
      simpa only [hAJ, Fin.eta] using he
    · have he := p.alternating ⟨A.val, by have := J.isLt; omega⟩
      have hm : M.mate (p.vertex A) = some (p.vertex J) ↔ A.val % 2 = 1 := by
        simpa only [hAJ, Fin.eta] using he
      have hpar : (t - J.val) % 2 = A.val % 2 := by omega
      rw [hpar]
      exact ⟨fun hx => hm.1 (M.symm hx), fun hx => M.symm (hm.2 hx)⟩
  have he := h.edge_of_predecessor _ _ _ hAlabel hpred
  simpa only [h.root_eq_of_high hrep _ _ hJlabel hJhigh] using he

/-- A nonempty descending low stretch gives a genuine graph jump to its
right high boundary. The reverse predecessor and the original low-vertex
membership are both derived from actual path constructions. -/
theorem late_stretch_edge (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut < p.length)
    (hrep : LowerBlossomRepresentation M cut s F)
    (p : AltPath M) (A J : Fin (p.length + 1)) (hAJ : A.val + 1 < J.val)
    (hAe : A.val % 2 = 0) (hJo : J.val % 2 = 1)
    (hJt : J.val ≤ cut + 2) (hhalf : cut + 2 < 2 * A.val)
    (hAcap : cut + 2 - A.val ≤ cap)
    (hAmin : minlevel M (p.vertex A) = some (cut + 2 - A.val))
    (hJmin : minlevel M (p.vertex J) = some (cut + 2 - J.val))
    (hJten : tenacity M (p.vertex J) = some (cut + 2))
    (hlow : ∀ K : Fin (p.length + 1), A.val < K.val → K.val < J.val →
      levelLE (tenacity M (p.vertex K)) (some cut)) :
    (predecessorGraph s F h).Edge (p.vertex A) (p.vertex J) := by
  have ht : (cut + 2) % 2 = 1 := by omega
  have hAlabel := h.minInvariant.2.1 _ _ hAmin hAcap
  have hpred := p.late_reverse_predecessor (cut + 2) ht A J (by omega)
    hAe hJo hJt hhalf hAmin hJmin hJten
  obtain ⟨k, hk, _⟩ := h.predecessor_assigned _ _ _ hAlabel hpred
  have hconf : ∀ (b v : V), Blossom M cut b v → levelLT (some cut) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M cut b w := by
    intro b v hv hb q hq hqb hqv
    obtain ⟨t, ht, htc⟩ := blossom_tenacity_bound cut b v hv
    have helig : EligibleTenacity M cut := ⟨hc, ⟨v, by rw [ht]; exact htc⟩, hnoaug⟩
    exact general_blossom_relative_confined M cut helig b v hv hb q hq hqb hqv
  have hbl := p.late_low_stretch_mem (cut + 2) ht
    (by simpa only [Nat.add_sub_cancel] using bases_below_cut cut hnoaug)
    (by simpa only [Nat.add_sub_cancel] using hconf)
    A ⟨A.val + 1, by have := J.isLt; omega⟩ J
    (by change A.val < A.val + 1; omega) (by change A.val + 1 < J.val; exact hAJ)
    hAe hJo hJt hhalf hAmin hJmin hJten (by simpa only [Nat.add_sub_cancel] using hlow)
  have hJhigh : levelLT (some cut) (tenacity M (p.vertex J)) := by
    rw [hJten]; change cut < cut + 2; omega
  have hr := h.root_eq_of_lower_member hrep _ _ k hk hJhigh
    (by simpa only [Nat.add_sub_cancel] using hbl)
  have he := h.edge_of_predecessor _ _ _ hAlabel hpred
  simpa only [hr] using he

/-- The complete descending high-to-high jump, including adjacent vertices.
No parity of the selected high boundaries is supplied by the caller. -/
theorem late_consecutive_high_edge (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut < p.length)
    (hrep : LowerBlossomRepresentation M cut s F)
    (p : AltPath M) (A J : Fin (p.length + 1)) (hAJ : A.val < J.val)
    (hJt : J.val ≤ cut + 2) (hhalf : cut + 2 < 2 * A.val)
    (hAcap : cut + 2 - A.val ≤ cap)
    (hAmin : minlevel M (p.vertex A) = some (cut + 2 - A.val))
    (hJmin : minlevel M (p.vertex J) = some (cut + 2 - J.val))
    (hAhigh : levelLT (some cut) (tenacity M (p.vertex A)))
    (hJten : tenacity M (p.vertex J) = some (cut + 2))
    (hlow : ∀ K : Fin (p.length + 1), A.val < K.val → K.val < J.val →
      levelLE (tenacity M (p.vertex K)) (some cut)) :
    (predecessorGraph s F h).Edge (p.vertex A) (p.vertex J) := by
  have hJhigh : levelLT (some cut) (tenacity M (p.vertex J)) := by
    rw [hJten]; change cut < cut + 2; omega
  by_cases ha : A.val + 1 = J.val
  · exact h.late_adjacent_edge hrep p (cut + 2) (by omega) A J ha hJt hAcap hAmin hJmin hJhigh
  · obtain ⟨hAe, hJo⟩ := p.low_stretch_boundary_parities cut A J (by omega) hAhigh hJhigh hlow
    exact h.late_stretch_edge hc hnoaug hrep p A J (by omega) hAe hJo hJt hhalf hAcap
      hAmin hJmin hJten hlow

end BudGraphInvariant
end MaximumMatching.Search
