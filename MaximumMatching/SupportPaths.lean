import MaximumMatching.DDFSGeometry
import MaximumMatching.GeneralConfinementSteps
import MaximumMatching.MatchingBridgePath
import MaximumMatching.MatchingGraphExpansion
import MaximumMatching.SupportGeometry

section SupportPathReverse

/-! Actual reverse predecessor witnesses on the descending half of a
maximum-level path. The path segment is preserved vertex by vertex; its
fresh minimum-level prefix is constructed using the established avoidance
theorem. No graph-compression or support conclusion is assumed. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Reverse the actual odd-length stretch between two after-midpoint high
vertices and prepend a minimum-level path to its right endpoint. The result
attains the left endpoint's minimum level and retains every original vertex
at the complementary index `t - K`. -/
theorem reverse_stretch_minlevel_witness (p : AltPath M) (t : Nat) (ht : t % 2 = 1)
    (A J : Fin (p.length + 1)) (hAJ : A.val < J.val)
    (hAe : A.val % 2 = 0) (hJo : J.val % 2 = 1)
    (hJt : J.val ≤ t) (hhalf : t < 2 * A.val)
    (hAmin : minlevel M (p.vertex A) = some (t - A.val))
    (hJmin : minlevel M (p.vertex J) = some (t - J.val))
    (hJten : tenacity M (p.vertex J) = some t) :
    ∃ z : AltPath M, z.length = t - A.val ∧ z.last = p.vertex A ∧
      minlevel M z.last = some z.length ∧
      ∀ K : Fin (p.length + 1), A.val ≤ K.val → K.val ≤ J.val →
        ∃ L : Fin (z.length + 1), L.val = t - K.val ∧ z.vertex L = p.vertex K := by
  have hJlevel : evenlevel M (p.vertex J) = some (t - J.val) := by
    have hh := level_of_minlevel (p.vertex J) (t - J.val) hJmin
    simpa only [show (t - J.val) % 2 = 0 by omega] using hh
  obtain ⟨q, hqJ, hqlen, _⟩ := ((level_eq_some_iff M 0 (p.vertex J) (t - J.val)).1 hJlevel).1
  let a := (p.take J.val (by omega)).segment A.val (by change A.val ≤ J.val; omega) hAe
  have hao : a.length % 2 = 1 := by change (J.val - A.val) % 2 = 1; omega
  let s := a.reverse hao
  have hsn : s.length = J.val - A.val := rfl
  have hsf : s.first = p.vertex J :=
    (a.reverse_first hao).trans ((p.take J.val (by omega)).segment_last A.val (by change A.val ≤ J.val; omega) hAe)
  have hsl : s.last = p.vertex A := a.reverse_last hao
  have hlen : q.length + s.length = t - A.val := by omega
  have htarget : IsShortest M (s.length % 2) s.last (q.length + s.length) := by
    have hh := (level_eq_some_iff M ((t - A.val) % 2) (p.vertex A) (t - A.val)).1
      (level_of_minlevel (p.vertex A) (t - A.val) hAmin)
    simpa only [hsl, hlen, show s.length % 2 = (t - A.val) % 2 by omega] using hh
  have hjoin : q.last = s.first := hqJ.trans hsf.symm
  have hqlevel : evenlevel M q.last = some q.length := by rw [hqJ, hqlen]; exact hJlevel
  have hqhigh : levelLT (some (t - 1)) (tenacity M q.last) := by
    rw [hqJ, hJten]
    change t - 1 < t
    omega
  have hdis := q.segment_avoids_prefix s hjoin htarget (t - 1) hqlevel hqhigh (by omega)
  have hqe : q.length % 2 = 0 := by omega
  let z := q.appendSegment s hqe hjoin hdis
  have hzn : z.length = t - A.val := hlen
  have hzl : z.last = p.vertex A := (q.appendSegment_last s hqe hjoin hdis).trans hsl
  refine ⟨z, hzn, hzl, by rw [hzl, hzn]; exact hAmin, ?_⟩
  intro K hAK hKJ
  let L : Fin (z.length + 1) := ⟨t - K.val, by rw [hzn]; omega⟩
  refine ⟨L, rfl, ?_⟩
  by_cases hKJe : K.val = J.val
  · have hKJ' : K = J := Fin.ext hKJe
    change (if h : t - K.val ≤ q.length then q.vertex ⟨t - K.val, _⟩
      else s.vertex ⟨t - K.val - q.length, _⟩) = p.vertex K
    rw [dite_eq_left (by omega : t - K.val ≤ q.length)]
    have hL : (⟨t - K.val, by omega⟩ : Fin (q.length + 1)) = ⟨q.length, by omega⟩ :=
      Fin.ext (by change t - K.val = q.length; omega)
    rw [hL, hKJ']
    exact hqJ
  · have hKJlt : K.val < J.val := by omega
    change (if h : t - K.val ≤ q.length then q.vertex ⟨t - K.val, _⟩
      else s.vertex ⟨t - K.val - q.length, _⟩) = p.vertex K
    rw [dite_eq_right (by omega : ¬t - K.val ≤ q.length)]
    change p.vertex ⟨A.val + (J.val - A.val - (t - K.val - q.length)), _⟩ = p.vertex K
    congr 1
    apply Fin.ext
    change A.val + (J.val - A.val - (t - K.val - q.length)) = K.val
    omega

/-- The first edge of the original stretch is a genuine predecessor when
traversed backward. Its witness is the constructed minimum-level path. -/
theorem late_reverse_predecessor (p : AltPath M) (t : Nat) (ht : t % 2 = 1)
    (A J : Fin (p.length + 1)) (hAJ : A.val < J.val)
    (hAe : A.val % 2 = 0) (hJo : J.val % 2 = 1)
    (hJt : J.val ≤ t) (hhalf : t < 2 * A.val)
    (hAmin : minlevel M (p.vertex A) = some (t - A.val))
    (hJmin : minlevel M (p.vertex J) = some (t - J.val))
    (hJten : tenacity M (p.vertex J) = some t) :
    Predecessor M (p.vertex ⟨A.val + 1, by have := J.isLt; omega⟩) (p.vertex A) := by
  obtain ⟨z, hzn, hzl, hzm, hvertices⟩ := p.reverse_stretch_minlevel_witness t ht A J hAJ
    hAe hJo hJt hhalf hAmin hJmin hJten
  have hzpos : 0 < z.length := by omega
  obtain ⟨L, hL, hLv⟩ := hvertices ⟨A.val + 1, by have := J.isLt; omega⟩
    (by change A.val ≤ A.val + 1; omega) (by change A.val + 1 ≤ J.val; omega)
  refine ⟨z, hzl, by rw [← hzl]; exact hzm, hzpos, ?_⟩
  have he : (⟨z.length - 1, by omega⟩ : Fin (z.length + 1)) = L := by
    apply Fin.ext
    change z.length - 1 = L.val
    dsimp only at hL
    omega
  rw [he]
  exact hLv

end MaximumMatching.AltPath

end SupportPathReverse

section SupportPathEdges

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

end SupportPathEdges

section SupportPathCompression

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

end SupportPathCompression

section SupportBridgeRoots

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

end SupportBridgeRoots

section MatchingSupportComplete

/-! Converse support discovery from actual maximum-level matching paths.
Before same-level petals are formed, every semantic support member has
disjoint arms in the actual predecessor/bud graph. Therefore any returned
bottleneck region contains exactly the trigger's support, excluding its bud.
Preservation of the converse through later same-stage contractions is separate. -/
namespace MaximumMatching.DDFS
variable {V : Type} {H : LayeredGraph V}

/-- A graph path to `w` disjoint from another root-to-bottom path places `w`
strictly above every common bottleneck. Extend the first path to the bottom
and cut its actual continuation at the forced bottleneck occurrence. -/
theorem onRootTo_of_disjoint_bottom_path (hreach : ReachBottom H) {r g b w : V}
    (hb : Bottleneck H r g b) (p q : Path H)
    (hpfirst : p.first = r ∨ p.first = g) (hplast : p.last = w)
    (hqfirst : q.first = r ∨ q.first = g) (hqbottom : H.level q.last = 0)
    (hdis : p.Disjoint q) : OnRootTo (H := H) r g b w ∧ w ≠ b := by
  have hqb : q.Contains b := hb q (hqfirst.elim
    (fun h => Or.inl ⟨h, hqbottom⟩) (fun h => Or.inr ⟨h, hqbottom⟩))
  have hnp : ¬p.Contains b := fun hp => hdis b hp hqb
  have hwb : w ≠ b := by
    intro he
    apply hnp
    rw [← he, ← hplast]
    exact p.contains_last
  obtain ⟨d, hdf, hdb⟩ := hreach w
  have hj : p.last = d.first := hplast.trans hdf.symm
  let z := p.append d hj
  have hzfirst : z.first = r ∨ z.first = g := by simpa only [z, Path.append_first] using hpfirst
  have hzbottom : H.level z.last = 0 := by simpa only [z, Path.append_last] using hdb
  have hzb := hb z (hzfirst.elim
    (fun h => Or.inl ⟨h, hzbottom⟩) (fun h => Or.inr ⟨h, hzbottom⟩))
  have hdb' : d.Contains b := ((p.contains_append_iff d hj b).1 hzb).resolve_left hnp
  obtain ⟨K, hKb⟩ := hdb'
  let a := d.take K.val (by omega)
  have hja : p.last = a.first := hj
  let y := p.append a hja
  refine ⟨⟨y, ?_, ?_, ?_⟩, hwb⟩
  · simpa only [y, Path.append_first] using hpfirst
  · exact (p.append_last a hja).trans hKb
  · apply (p.contains_append_iff a hja w).2
    exact Or.inl (hplast ▸ p.contains_last)

end MaximumMatching.DDFS

namespace MaximumMatching.Search.BudGraphInvariant
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}
variable {cap cut : Nat} {s : State V} {F : BudForest V}

/-- Every actual support witness yields a disjoint pair of graph arms.
The arm ending at the supported vertex may start at either bridge bud. -/
theorem support_graph_arms (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1) (hrep : LowerBlossomRepresentation M cut s F)
    (hcap : cut + 2 ≤ 2 * cap + 1) (u v w : V)
    (he : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, s.minLabel u = some k) (hv : ∃ k, s.minLabel v = some k)
    (hsupport : InSupport M u v w) :
    ∃ p q : DDFS.Path (predecessorGraph s F h), p.last = w ∧
      (predecessorGraph s F h).level q.last = 0 ∧ p.Disjoint q ∧
      ((p.first = F.root u ∧ q.first = F.root v) ∨
        (p.first = F.root v ∧ q.first = F.root u)) := by
  obtain ⟨hb, t, ht, het, hwt, z, hzw, hzmax, I, hI⟩ := hsupport
  have hte : t = cut + 2 := Option.some.inj (het.symm.trans he)
  subst t
  have hzt : tenacity M z.last = some (cut + 2) := by rw [hzw]; exact hwt
  have hzm : maxlevel M z.last = some z.length := by rw [hzw]; exact hzmax
  rcases hI with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · have hIb : Bridge M (z.vertex ⟨I.val, by omega⟩) (z.vertex ⟨I.val + 1, by omega⟩) :=
      by rw [hleft, hright]; exact hb
    have hIt : MaximumMatching.edgeTenacity M (z.vertex ⟨I.val, by omega⟩)
        (z.vertex ⟨I.val + 1, by omega⟩) = some (cut + 2) := by rw [hleft, hright]; exact he
    obtain ⟨a, b, haf, _, hbf, hbl, hdis, hbottom⟩ := h.current_bridge_graph_arms hc ht hrep hcap z
      hzt hzm I hIb hIt (by rw [hleft]; exact hu) (by rw [hright]; exact hv)
    exact ⟨b, a, hbl.trans hzw, hbottom, DDFS.Path.disjoint_symm hdis,
      Or.inr ⟨by simpa only [hright] using hbf, by simpa only [hleft] using haf⟩⟩
  · have hIb : Bridge M (z.vertex ⟨I.val, by omega⟩) (z.vertex ⟨I.val + 1, by omega⟩) :=
      by rw [hleft, hright]; exact bridge_symm hb
    have hIt : MaximumMatching.edgeTenacity M (z.vertex ⟨I.val, by omega⟩)
        (z.vertex ⟨I.val + 1, by omega⟩) = some (cut + 2) := by
      rw [hleft, hright, edgeTenacity_symmetric v u]; exact he
    obtain ⟨a, b, haf, _, hbf, hbl, hdis, hbottom⟩ := h.current_bridge_graph_arms hc ht hrep hcap z
      hzt hzm I hIb hIt (by rw [hleft]; exact hv) (by rw [hright]; exact hu)
    exact ⟨b, a, hbl.trans hzw, hbottom, DDFS.Path.disjoint_symm hdis,
      Or.inl ⟨by simpa only [hright] using hbf, by simpa only [hleft] using haf⟩⟩

theorem support_in_bottleneck_region (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1) (hrep : LowerBlossomRepresentation M cut s F)
    (hcap : cut + 2 ≤ 2 * cap + 1) (u v w b : V)
    (he : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, s.minLabel u = some k) (hv : ∃ k, s.minLabel v = some k)
    (hb : DDFS.Bottleneck (predecessorGraph s F h) (F.root u) (F.root v) b)
    (hsupport : InSupport M u v w) :
    DDFS.OnRootTo (H := predecessorGraph s F h) (F.root u) (F.root v) b w ∧ w ≠ b := by
  obtain ⟨p, q, hpw, hqb, hdis, hstarts⟩ := h.support_graph_arms hc hrep hcap u v w he hu hv hsupport
  apply DDFS.onRootTo_of_disjoint_bottom_path h.reachBottom hb p q ?_ hpw ?_ hqb hdis
  · exact hstarts.elim (fun hh => Or.inl hh.1) (fun hh => Or.inr hh.1)
  · exact hstarts.elim (fun hh => Or.inr hh.2) (fun hh => Or.inl hh.2)

end MaximumMatching.Search.BudGraphInvariant

end MatchingSupportComplete
