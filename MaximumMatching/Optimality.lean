import MaximumMatching.DifferenceUniqueness

/-! Maximum-cardinality specification and both directions of Berge's criterion.
The converse is proved by finite alternating components of two matchings. -/
namespace MaximumMatching
namespace Matching
variable {n : Nat} {G : Graph (Fin n)}

/-- Maximum cardinality among all matchings of this same graph. -/
def IsMaximum (M : Matching G) : Prop := ∀ N : Matching G, N.cardinality ≤ M.cardinality

/-- There is no simple alternating path with distinct free endpoints. -/
def NoAugmentingPath (M : Matching G) : Prop := ∀ p : AltPath M, ¬ p.Augmenting

theorem cardinality_le (M : Matching G) : M.cardinality ≤ n / 2 := by
  have hc : M.matchedCount ≤ n := by
    simpa only [List.length_finRange, matchedCount] using
      (List.countP_le_length (p := fun v => (M.mate v).isSome) (l := List.finRange n))
  unfold cardinality
  omega

theorem isMaximum_noAugmentingPath (M : Matching G) (hM : M.IsMaximum) :
    M.NoAugmentingPath := by
  intro p hp
  have hle := hM (p.augment hp)
  have hgain := p.augment_cardinality hp
  omega

theorem augmenting_not_isMaximum (M : Matching G) (p : AltPath M) (hp : p.Augmenting) :
    ¬ M.IsMaximum := by
  intro hM
  exact M.isMaximum_noAugmentingPath hM p hp

/-- A larger matching supplies a start vertex for a symmetric-difference argument.
This alone does not certify that the resulting path ends at another M-free vertex. -/
theorem larger_has_free_matched (M N : Matching G) (h : M.cardinality < N.cardinality) :
    ∃ v, M.Free v ∧ (N.mate v).isSome = true := by
  classical
  apply Classical.byContradiction
  intro hex
  have hpoint : ∀ v, (N.mate v).isSome = true → (M.mate v).isSome = true := by
    intro v hv
    apply Classical.byContradiction
    intro hM
    have hnone : M.mate v = none := by
      cases he : M.mate v with
      | none => rfl
      | some w => exact False.elim (hM (by simp [he]))
    exact hex ⟨v, hnone, hv⟩
  have hcount : N.matchedCount ≤ M.matchedCount :=
    List.countP_mono_left (fun v _ => hpoint v)
  unfold cardinality at h
  omega

end Matching

namespace DifferencePath
variable {n : Nat} {G : Graph (Fin n)} {M N : Matching G}

/-- Without M-augmenting paths, following the two matchings terminates at an
N-free vertex. The simple-path length is the termination measure. -/
theorem extend_to_other_free (hno : M.NoAugmentingPath) (p : DifferencePath M N)
    (heven : p.path.length % 2 = 0) :
    ∃ q : DifferencePath M N, q.path.first = p.path.first ∧
      p.path.length ≤ q.path.length ∧ q.path.length % 2 = 0 ∧ N.Free q.path.last := by
  cases hv : N.mate p.path.last with
  | none => exact ⟨p, rfl, Nat.le_refl _, heven, hv⟩
  | some v =>
    let r := p.appendOther heven hv
    have hrodd : r.path.length % 2 = 1 := by
      change (p.path.length + 1) % 2 = 1
      omega
    cases hw : M.mate r.path.last with
    | none => exact False.elim (hno r.path ⟨hrodd, hw⟩)
    | some w =>
      let s := r.appendMatched hrodd hw
      have hseven : s.path.length % 2 = 0 := by
        change (p.path.length + 1 + 1) % 2 = 0
        omega
      obtain ⟨q, hqfirst, hqlen, hqeven, hqfree⟩ := extend_to_other_free hno s hseven
      refine ⟨q, ?_, ?_, hqeven, hqfree⟩
      · exact hqfirst.trans ((r.appendMatched_first hrodd hw).trans
          (p.appendOther_first heven hv))
      · have hs : s.path.length = p.path.length + 2 := by rfl
        omega
termination_by n - p.path.length
decreasing_by
  change n - s.path.length < n - p.path.length
  have hpbound := p.path.length_lt_vertices
  have hs : s.path.length = p.path.length + 2 := by rfl
  omega

/-- Every M-free/N-matched vertex has an alternating path to an N-free/M-matched
vertex, assuming that M admits no augmenting path. -/
theorem free_matched_to_matched_free (hno : M.NoAugmentingPath) {u : Fin n}
    (hu : M.Free u) (hNu : (N.mate u).isSome = true) :
    ∃ q : DifferencePath M N, q.path.first = u ∧ q.path.length % 2 = 0 ∧
      N.Free q.path.last ∧ (M.mate q.path.last).isSome = true := by
  let p := trivial M N u hu
  have heven : p.path.length % 2 = 0 := rfl
  obtain ⟨q, hqfirst, _, hqeven, hqfree⟩ := extend_to_other_free hno p heven
  have hfirst : q.path.first = u := hqfirst
  have hpos : 0 < q.path.length := by
    by_cases hz : q.path.length = 0
    · have hl : q.path.last = q.path.first :=
        congrArg q.path.vertex (Fin.ext hz)
      have hfree : N.mate u = none := by
        simpa only [Matching.Free, hl, hfirst] using hqfree
      rw [hfree] at hNu
      contradiction
    · omega
  have hmate := q.path.mate_previous q.path.length (by omega) hpos hqeven
  have hmatched : (M.mate q.path.last).isSome = true := by
    change (M.mate (q.path.vertex ⟨q.path.length, by omega⟩)).isSome = true
    rw [hmate]
    rfl
  exact ⟨q, hfirst, hqeven, hqfree, hmatched⟩

end DifferencePath

namespace Matching
variable {n : Nat} {G : Graph (Fin n)}

/-- Vertices free for M but saturated by N. -/
def excessVertices (M N : Matching G) : List (Fin n) :=
  (List.finRange n).filter (fun v => (M.mate v).isNone && (N.mate v).isSome)

theorem mem_excessVertices (M N : Matching G) (v : Fin n) :
    v ∈ M.excessVertices N ↔ M.Free v ∧ (N.mate v).isSome = true := by
  simp only [excessVertices, List.mem_filter, List.mem_finRange, true_and,
    Bool.and_eq_true, Option.isNone_iff_eq_none, Free]

/-- The difference in saturated-vertex counts is the difference in excess counts. -/
theorem excess_balance (M N : Matching G) :
    N.matchedCount + (N.excessVertices M).length =
      M.matchedCount + (M.excessVertices N).length := by
  have hlist (vs : List (Fin n)) :
      vs.countP (fun v => (N.mate v).isSome) +
        vs.countP (fun v => (N.mate v).isNone && (M.mate v).isSome) =
      vs.countP (fun v => (M.mate v).isSome) +
        vs.countP (fun v => (M.mate v).isNone && (N.mate v).isSome) := by
    induction vs with
    | nil => rfl
    | cons v vs ih =>
      simp only [List.countP_cons]
      cases hM : M.mate v <;> cases hN : N.mate v <;>
        simp only [Option.isSome_some, Option.isSome_none, Option.isNone_some,
          Option.isNone_none, Bool.true_and, Bool.false_and, Bool.false_eq_true,
          ↓reduceIte] <;> omega
  simpa only [matchedCount, excessVertices, List.countP_eq_length_filter] using
    hlist (List.finRange n)

/-- Endpoint injection for the alternating components: if there is no augmenting
path, every excess N endpoint is paired with a distinct excess M endpoint. -/
theorem excess_le_of_noAugmentingPath (M N : Matching G) (hno : M.NoAugmentingPath) :
    (M.excessVertices N).length ≤ (N.excessVertices M).length := by
  classical
  let source := M.excessVertices N
  let target := N.excessVertices M
  have hpaths (u : Fin n) (hu : u ∈ source) :
      ∃ q : DifferencePath M N, q.path.first = u ∧ q.path.length % 2 = 0 ∧
        N.Free q.path.last ∧ (M.mate q.path.last).isSome = true := by
    have hu' := (M.mem_excessVertices N u).mp hu
    exact DifferencePath.free_matched_to_matched_free hno hu'.1 hu'.2
  let f (u : Fin n) : Fin n :=
    if hu : u ∈ source then (hpaths u hu).choose.path.last else u
  have hmem (u : Fin n) (hu : u ∈ source) : f u ∈ target := by
    have hq := (hpaths u hu).choose_spec
    change (if h : u ∈ source then (hpaths u h).choose.path.last else u) ∈ target
    rw [dite_eq_left hu]
    exact (N.mem_excessVertices M _).mpr ⟨hq.2.2.1, hq.2.2.2⟩
  have hinj (u : Fin n) (hu : u ∈ source) (v : Fin n) (hv : v ∈ source)
      (he : f u = f v) : u = v := by
    have hpu := (hpaths u hu).choose_spec
    have hpv := (hpaths v hv).choose_spec
    have hend : (hpaths u hu).choose.path.last = (hpaths v hv).choose.path.last := by
      simpa only [f, dite_eq_left hu, dite_eq_left hv] using he
    have hf := DifferencePath.same_last_same_first
      (hpaths u hu).choose (hpaths v hv).choose hpu.2.1 hpv.2.1 hend
    exact hpu.1.symm.trans (hf.trans hpv.1)
  have hnd : source.Nodup :=
    (List.nodup_finRange n).filter (fun v => (M.mate v).isNone && (N.mate v).isSome)
  have hndmap : (source.map f).Nodup := by
    apply List.pairwise_map.mpr
    exact hnd.imp_of_mem (fun hu hv hne he => hne (hinj _ hu _ hv he))
  have hsub : source.map f ⊆ target := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    exact hmem u hu
  have hlen := hndmap.length_le_of_subset hsub
  simpa only [List.length_map] using hlen

/-- Berge's criterion, converse direction, proved by the alternating-component
endpoint injection above. No algorithm-completeness hypothesis is assumed. -/
theorem noAugmentingPath_isMaximum (M : Matching G) (hno : M.NoAugmentingPath) :
    M.IsMaximum := by
  intro N
  have hbalance := M.excess_balance N
  have hle := M.excess_le_of_noAugmentingPath N hno
  unfold cardinality
  omega

/-- Berge's augmenting-path characterization for finite simple undirected graphs. -/
theorem isMaximum_iff_noAugmentingPath (M : Matching G) :
    M.IsMaximum ↔ M.NoAugmentingPath :=
  ⟨M.isMaximum_noAugmentingPath, M.noAugmentingPath_isMaximum⟩

/-- Any larger matching witnesses the existence of an augmenting path. -/
theorem larger_has_augmentingPath (M N : Matching G) (h : M.cardinality < N.cardinality) :
    ∃ p : AltPath M, p.Augmenting := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hno : M.NoAugmentingPath := by
    intro p hp
    exact hnone ⟨p, hp⟩
  have hmax := M.noAugmentingPath_isMaximum hno N
  omega

end Matching
end MaximumMatching
