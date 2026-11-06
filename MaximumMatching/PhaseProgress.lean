import MaximumMatching.DifferencePacking

/-! A maximal family of shortest augmenting paths strictly increases the
shortest augmenting-path length. The proof uses the proved difference packing
and the finite vertex support of the actual matching flips. -/
namespace MaximumMatching

namespace DifferencePath
variable {V : Type} {G : Graph V} {M N : Matching G}

/-- Every vertex of an augmenting difference component has different mates in
the two matchings, including the free endpoints. -/
theorem mates_ne (p : DifferencePath M N) (hp : p.path.Augmenting)
    (i : Fin (p.path.length + 1)) : M.mate (p.path.vertex i) ≠ N.mate (p.path.vertex i) := by
  intro heq
  by_cases he : i.val % 2 = 0
  · have hi : i.val < p.path.length := by have := hp.1; omega
    have hn := p.other ⟨i.val, hi⟩ he
    have hm : M.mate (p.path.vertex i) = some (p.path.vertex ⟨i.val + 1, by omega⟩) := by
      rw [heq]; exact hn
    have hodd := (p.path.alternating ⟨i.val, hi⟩).mp hm
    change i.val % 2 = 1 at hodd
    omega
  · have hi : 0 < i.val := by omega
    have hprev : i.val - 1 < p.path.length := by omega
    have hn := p.other ⟨i.val - 1, hprev⟩ (by change (i.val - 1) % 2 = 0; omega)
    have hstep := N.symm hn
    have hidx : i.val - 1 + 1 = i.val := by omega
    dsimp only at hstep
    simp only [hidx] at hstep
    have hm : M.mate (p.path.vertex i) = some (p.path.vertex ⟨i.val - 1, by omega⟩) := by
      rw [heq]; exact hstep
    have hrev : M.mate (p.path.vertex ⟨i.val - 1, by omega⟩) =
        some (p.path.vertex ⟨i.val - 1 + 1, by omega⟩) := by
      simpa only [hidx] using M.symm hm
    have hodd := (p.path.alternating ⟨i.val - 1, hprev⟩).mp hrev
    change (i.val - 1) % 2 = 1 at hodd
    omega

end DifferencePath

namespace AugmentingFamily
variable {V : Type} [DecidableEq V] {G : Graph V}

/-- All flips leave every vertex outside the supplied family unchanged. -/
theorem run_mate_off {M : Matching G} (f : AugmentingFamily M) (v : V)
    (hoff : ∀ i j, (f.path i).vertex j ≠ v) : f.run.mate v = M.mate v := by
  rw [run]
  split
  · rfl
  · rename_i h
    rw [run_mate_off]
    · exact AltPath.augment_off_path _ _ (by rintro ⟨j, hj⟩; exact hoff _ j hj)
    · intro i j
      exact hoff ⟨i.val + 1, by change i.val + 1 < f.count; have := i.isLt; change i.val < f.count - 1 at this; omega⟩ j
termination_by f.count
decreasing_by dsimp [tailAfterFirst]; omega

/-- Transport a path back through a disjoint family of actual flips. -/
def pullback {M : Matching G} (f : AugmentingFamily M) (q : AltPath f.run)
    (hoff : ∀ i j k, (f.path i).vertex j ≠ q.vertex k) : AltPath M where
  length := q.length
  vertex := q.vertex
  injective := q.injective
  adjacent := q.adjacent
  start_free := by
    change M.mate (q.vertex ⟨0, by omega⟩) = none
    rw [← f.run_mate_off _ (fun i j => hoff i j _)]
    exact q.start_free
  alternating := by
    intro k
    rw [← f.run_mate_off _ (fun i j => hoff i j _)]
    exact q.alternating k

theorem pullback_augmenting {M : Matching G} (f : AugmentingFamily M) (q : AltPath f.run)
    (hq : q.Augmenting) (hoff : ∀ i j k, (f.path i).vertex j ≠ q.vertex k) :
    (f.pullback q hoff).Augmenting := by
  refine ⟨hq.1, ?_⟩
  change M.mate (q.vertex ⟨q.length, by omega⟩) = none
  rw [← f.run_mate_off _ (fun i j => hoff i j _)]
  exact hq.2

end AugmentingFamily

namespace AugmentingFamily
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

theorem mem_vertices (f : AugmentingFamily M) (v : Fin n) :
    v ∈ f.vertices ↔ ∃ i j, (f.path i).vertex j = v := by
  simp only [vertices, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]

theorem vertices_length_eq (f : AugmentingFamily M) (l : Nat)
    (h : ∀ i, (f.path i).length = l) : f.vertices.length = f.count * (l + 1) := by
  have calcLength (is : List (Fin f.count)) :
      (is.flatMap fun i => (List.finRange ((f.path i).length + 1)).map (f.path i).vertex).length =
      is.length * (l + 1) := by
    induction is with
    | nil => simp
    | cons i is ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_finRange,
        h i, ih, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  simpa only [vertices, List.length_finRange] using calcLength (List.finRange f.count)

/-- The semantic input guaranteed by a completed shortest-path blocking phase. -/
structure MaximalShortest (f : AugmentingFamily M) (l : Nat) : Prop where
  shortest : ∀ p : AltPath M, p.Augmenting → l ≤ p.length
  length_eq : ∀ i, (f.path i).length = l
  maximal : ∀ p : AltPath M, p.Augmenting → p.length = l →
    ¬ (∀ i, (f.path i).Disjoint p)

/-- A maximal vertex-disjoint family of shortest augmenting paths is a blocking
phase: every augmenting path after executing its flips is strictly longer. -/
theorem shortest_length_increases (f : AugmentingFamily M) (l : Nat)
    (hf : f.MaximalShortest l) (q : AltPath f.run) (hq : q.Augmenting) :
    l < q.length := by
  classical
  apply Nat.lt_of_not_ge
  intro hshort
  let N := q.augment hq
  obtain ⟨d, hd⟩ := exists_differenceFamily n G M N
  have hN : N.cardinality = M.cardinality + f.count + 1 := by
    change (q.augment hq).cardinality = _
    rw [AltPath.augment_cardinality, f.run_cardinality]
  have hdc : d.count = f.count + 1 := by omega
  let qvs := (List.finRange (q.length + 1)).map q.vertex
  have qmem (v : Fin n) : v ∈ qvs ↔ ∃ k, q.vertex k = v := by
    simp only [qvs, List.mem_map, List.mem_finRange, true_and]
  have qlen : qvs.length = q.length + 1 := by simp only [qvs, List.length_map, List.length_finRange]
  have flen := f.vertices_length_eq l hf.length_eq
  have dlower := d.toAugmentingFamily.vertices_length_lower l
    (fun i => hf.shortest _ (d.augmenting i))
  change d.count * (l + 1) ≤ d.toAugmentingFamily.vertices.length at dlower
  rw [hdc, Nat.add_mul, Nat.one_mul] at dlower
  have support : d.toAugmentingFamily.vertices ⊆ f.vertices ++ qvs := by
    intro v hv
    obtain ⟨i, j, rfl⟩ := (d.toAugmentingFamily.mem_vertices v).mp hv
    apply List.mem_append.mpr
    by_cases hfmem : (d.path i).path.vertex j ∈ f.vertices
    · exact Or.inl hfmem
    · right
      apply Classical.byContradiction
      intro hqmem
      have old := f.run_mate_off ((d.path i).path.vertex j) (by
        intro a b hab
        exact hfmem ((f.mem_vertices _).mpr ⟨a, b, hab⟩))
      have new := q.augment_off_path hq (by
        intro hmem
        exact hqmem ((qmem _).mpr hmem))
      exact (d.path i).mates_ne (d.augmenting i) j (by
        change M.mate _ = (q.augment hq).mate _
        exact (new.trans old).symm)
  have hoff : ∀ i j k, (f.path i).vertex j ≠ q.vertex k := by
    intro i j k heq
    let v := (f.path i).vertex j
    have hvf : v ∈ f.vertices := (f.mem_vertices _).mpr ⟨i, j, rfl⟩
    have hvq : v ∈ qvs := (qmem _).mpr ⟨k, heq.symm⟩
    have support' : d.toAugmentingFamily.vertices ⊆ f.vertices ++ qvs.erase v := by
      intro x hx
      rcases List.mem_append.mp (support hx) with hxf | hxq
      · exact List.mem_append.mpr (Or.inl hxf)
      · by_cases hxv : x = v
        · subst x; exact List.mem_append.mpr (Or.inl hvf)
        · exact List.mem_append.mpr (Or.inr ((List.mem_erase_of_ne hxv).mpr hxq))
    have upper := d.toAugmentingFamily.vertices_nodup.length_le_of_subset support'
    rw [List.length_append, List.length_erase_of_mem hvq, flen, qlen] at upper
    omega
  let oldq := f.pullback q hoff
  have holdq : oldq.Augmenting := f.pullback_augmenting q hq hoff
  have hge : l ≤ q.length := hf.shortest oldq holdq
  have hlen : oldq.length = l := by change q.length = l; omega
  exact hf.maximal oldq holdq hlen (fun i j k => hoff i j k)

end AugmentingFamily

end MaximumMatching
