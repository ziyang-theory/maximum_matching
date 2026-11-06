import MaximumMatching.FirstBridge
import MaximumMatching.PhaseProgress
import MaximumMatching.MinComplete

/-! The tenacity-one case of a phase: greedily select disjoint free-free
edges from the actual finite edge enumeration. The resulting family is a
maximal family of shortest augmenting paths whenever such an edge exists. -/
namespace MaximumMatching

namespace AugmentingFamily
variable {V : Type} {G : Graph V} {M : Matching G}

def empty : AugmentingFamily M where
  count := 0
  path i := nomatch i
  augmenting i := nomatch i
  disjoint i := nomatch i

/-- Prepend a real augmenting path disjoint from every existing path. -/
def prepend (f : AugmentingFamily M) (p : AltPath M) (hp : p.Augmenting)
    (hd : ∀ i, p.Disjoint (f.path i)) : AugmentingFamily M where
  count := f.count + 1
  path i := if h : i.val = 0 then p else f.path ⟨i.val - 1, by omega⟩
  augmenting i := by
    split
    · exact hp
    · exact f.augmenting _
  disjoint i j hij := by
    split <;> split
    · exact False.elim (hij (Fin.ext (by omega)))
    · exact hd _
    · exact AltPath.disjoint_symm (hd _)
    · apply f.disjoint
      intro he
      exact hij (Fin.ext (by have hh := congrArg Fin.val he; dsimp only at hh; omega))

section Finite
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

theorem mem_vertices_prepend (f : AugmentingFamily M) (p : AltPath M)
    (hp : p.Augmenting) (hd : ∀ i, p.Disjoint (f.path i)) (v : Fin n) :
    v ∈ (f.prepend p hp hd).vertices ↔ (∃ j, p.vertex j = v) ∨ v ∈ f.vertices := by
  rw [mem_vertices]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hz : i.val = 0
    · have he : (f.prepend p hp hd).path i = p := by
        exact dite_eq_left hz
      rw [he] at hi
      exact Or.inl hi
    · let j : Fin f.count := ⟨i.val - 1, by
        have := i.isLt; change i.val < f.count + 1 at this; omega⟩
      have he : (f.prepend p hp hd).path i = f.path j := dite_eq_right hz
      rw [he] at hi
      exact Or.inr ((f.mem_vertices v).2 ⟨j, hi⟩)
  · rintro (hpv | hv)
    · exact ⟨⟨0, by dsimp only [prepend]; omega⟩, hpv⟩
    · obtain ⟨i, hi⟩ := (f.mem_vertices v).1 hv
      refine ⟨⟨i.val + 1, by dsimp only [prepend]; omega⟩, ?_⟩
      simpa [prepend] using hi

end Finite
end AugmentingFamily

namespace Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
private theorem freeEdge_disjoint_of_not_mem (f : AugmentingFamily M)
    (u v : Fin n) (hu : M.Free u) (ha : G.Adj u v)
    (huf : u ∉ f.vertices) (hvf : v ∉ f.vertices) :
    ∀ i, (AltPath.freeEdge u v hu ha).Disjoint (f.path i) := by
  intro i j k he
  have hjlt : j.val < 2 := j.isLt
  by_cases hj : j.val = 0
  · apply huf
    apply (f.mem_vertices u).2
    refine ⟨i, k, ?_⟩
    have hjeq : j = ⟨0, by change 0 < 1 + 1; omega⟩ := Fin.ext hj
    simpa [hjeq, AltPath.freeEdge, AltPath.append, AltPath.trivial] using he.symm
  · apply hvf
    apply (f.mem_vertices v).2
    refine ⟨i, k, ?_⟩
    have hjeq : j = ⟨1, by change 1 < 1 + 1; omega⟩ := Fin.ext (show j.val = 1 by omega)
    simpa [hjeq, AltPath.freeEdge, AltPath.append, AltPath.trivial] using he.symm

/-- Greedy free-edge selection in reverse candidate order. Every decision
uses the current matching and the explicitly selected family vertices. -/
def freeEdgeScan (M : Matching G) : List (Fin n × Fin n) → AugmentingFamily M
  | [] => .empty
  | (u, v) :: es =>
    let f := freeEdgeScan M es
    if h : G.Adj u v ∧ M.mate u = none ∧ M.mate v = none ∧ u ∉ f.vertices ∧ v ∉ f.vertices then
      f.prepend (AltPath.freeEdge u v h.2.1 h.1)
        (AltPath.freeEdge_augmenting u v h.2.1 h.2.2.1 h.1)
        (freeEdge_disjoint_of_not_mem f u v h.2.1 h.1 h.2.2.2.1 h.2.2.2.2)
    else f

theorem freeEdgeScan_length (es : List (Fin n × Fin n)) :
    ∀ j, ((freeEdgeScan M es).path j).length = 1 := by
  induction es with
  | nil => intro j; exact Fin.elim0 j
  | cons e es ih =>
    rcases e with ⟨u, v⟩
    rw [freeEdgeScan]
    by_cases h : G.Adj u v ∧ M.mate u = none ∧ M.mate v = none ∧
        u ∉ (freeEdgeScan M es).vertices ∧ v ∉ (freeEdgeScan M es).vertices
    · rw [dite_eq_left h]
      intro j
      simp only [AugmentingFamily.prepend]
      split
      · rfl
      · exact ih _
    · rw [dite_eq_right h]
      exact ih

/-- Every candidate free-free edge meets the returned family. This is the
maximality invariant of the greedy scan, including rejected and repeated edges. -/
theorem freeEdgeScan_covers (es : List (Fin n × Fin n))
    (u v : Fin n) (he : (u, v) ∈ es) (ha : G.Adj u v)
    (hu : M.Free u) (hv : M.Free v) :
    u ∈ (freeEdgeScan M es).vertices ∨ v ∈ (freeEdgeScan M es).vertices := by
  induction es with
  | nil => exact False.elim (List.not_mem_nil he)
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    rw [freeEdgeScan]
    split
    next h =>
      rcases List.mem_cons.mp he with he | he
      · cases he
        left
        apply (AugmentingFamily.mem_vertices_prepend _ _ _ _ u).2
        exact Or.inl ⟨⟨0, by change 0 < 2; omega⟩, rfl⟩
      · rcases ih he with hu | hv
        · exact Or.inl ((AugmentingFamily.mem_vertices_prepend _ _ _ _ u).2 (Or.inr hu))
        · exact Or.inr ((AugmentingFamily.mem_vertices_prepend _ _ _ _ v).2 (Or.inr hv))
    next h =>
      rcases List.mem_cons.mp he with he | he
      · cases he
        by_cases huf : u ∈ (freeEdgeScan M es).vertices
        · exact Or.inl huf
        · by_cases hvf : v ∈ (freeEdgeScan M es).vertices
          · exact Or.inr hvf
          · exact False.elim (h ⟨ha, hu, hv, huf, hvf⟩)
      · exact ih he

/-- The actual finite tenacity-one phase. Enumeration cost is separate from
the correctness and maximal-shortest-family theorem below. -/
def freeEdgePhase (M : Matching G) : AugmentingFamily M :=
  freeEdgeScan M (allCandidates n)

theorem freeEdgePhase_maximalShortest (M : Matching G) :
    (freeEdgePhase M).MaximalShortest 1 := by
  refine ⟨fun p hp => p.augmenting_pos hp, freeEdgeScan_length _, ?_⟩
  intro p hp hlen hd
  have hadj : G.Adj p.first p.last := by
    have hh := p.adjacent ⟨0, by omega⟩
    have hi : (⟨0 + 1, by omega⟩ : Fin (p.length + 1)) = ⟨p.length, by omega⟩ := Fin.ext (show 1 = p.length by omega)
    simpa only [AltPath.first, AltPath.last, hi] using hh
  have he : (p.first, p.last) ∈ allCandidates n := by
    simp [allCandidates]
  have hcover := freeEdgeScan_covers (M := M) (allCandidates n) p.first p.last he
    hadj p.start_free hp.2
  rcases hcover with hf | hl
  · obtain ⟨i, j, hj⟩ := ((freeEdgePhase M).mem_vertices p.first).1 hf
    exact hd i j ⟨0, by omega⟩ hj
  · obtain ⟨i, j, hj⟩ := ((freeEdgePhase M).mem_vertices p.last).1 hl
    exact hd i j ⟨p.length, by omega⟩ hj

theorem freeEdgePhase_empty_no_short (M : Matching G)
    (hz : (freeEdgePhase M).count = 0) :
    ∀ p : AltPath M, p.Augmenting → 1 < p.length := by
  intro p hp
  have hpos := p.augmenting_pos hp
  by_cases he : p.length = 1
  · exact False.elim ((freeEdgePhase_maximalShortest M).maximal p hp he (by
      intro i
      have hh := i.isLt
      omega))
  · omega

/-- After executing this phase, no augmenting path of length one remains. -/
theorem freeEdgePhase_no_short (M : Matching G)
    (p : AltPath (freeEdgePhase M).run) (hp : p.Augmenting) : 1 < p.length :=
  (freeEdgePhase M).shortest_length_increases 1 (freeEdgePhase_maximalShortest M) p hp

end Search
end MaximumMatching
