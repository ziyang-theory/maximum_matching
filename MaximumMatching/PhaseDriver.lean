import MaximumMatching.Foundations
import MaximumMatching.Optimality

section DifferencePacking

/-! Disjoint augmenting components of the union of two matchings.
These components establish strict shortest-path progress after a blocking phase. -/
namespace MaximumMatching

namespace Matching
variable {V : Type} {G : Graph V}

def unionGraph (M N : Matching G) : Graph V where
  Adj u v := M.mate u = some v ∨ N.mate u = some v
  symm := fun h => h.elim (fun h => Or.inl (M.symm h)) (fun h => Or.inr (N.symm h))
  loopless := by
    intro v h
    exact h.elim (M.mate_ne_self) (N.mate_ne_self)

def unionLeft (M N : Matching G) : Matching (M.unionGraph N) where
  mate := M.mate
  symm := M.symm
  edge := fun h => Or.inl h

def unionRight (M N : Matching G) : Matching (M.unionGraph N) where
  mate := N.mate
  symm := N.symm
  edge := fun h => Or.inr h

end Matching

namespace DifferencePath
variable {V : Type} {G : Graph V} {M N : Matching G}

/-- A union-graph alternating path is a genuine difference path in the original graph. -/
def ofUnionPath (p : AltPath (M.unionLeft N)) : DifferencePath M N where
  path := {
    length := p.length
    vertex := p.vertex
    injective := p.injective
    adjacent := by
      intro i
      exact (p.adjacent i).elim M.edge N.edge
    start_free := p.start_free
    alternating := p.alternating }
  other := by
    intro i hi
    have hib : i.val < p.length := i.isLt
    have hn : ¬(M.unionLeft N).mate (p.vertex ⟨i.val, by omega⟩) =
        some (p.vertex ⟨i.val + 1, by omega⟩) := by
      intro hm
      have := (p.alternating i).1 hm
      omega
    exact (p.adjacent i).elim (fun hm => False.elim (hn hm)) id

end DifferencePath

/-- The larger matching yields an augmenting component using only edges of the two
matchings. This is derived from the already-proved Berge criterion on their union. -/
theorem larger_has_differenceAugmenting {n : Nat} {G : Graph (Fin n)}
    (M N : Matching G) (h : M.cardinality < N.cardinality) :
    ∃ p : DifferencePath M N, p.path.Augmenting := by
  have hu : (M.unionLeft N).cardinality < (M.unionRight N).cardinality := h
  obtain ⟨p, hp⟩ := (M.unionLeft N).larger_has_augmentingPath (M.unionRight N) hu
  exact ⟨DifferencePath.ofUnionPath p, hp⟩

namespace DifferencePath
variable {V : Type} {G : Graph V} {M N : Matching G}

/-- Every vertex of an odd difference path is paired by N inside the path. -/
theorem other_mate_on_path (p : DifferencePath M N) (hp : p.path.Augmenting)
    (i : Fin (p.path.length + 1)) :
    ∃ j, N.mate (p.path.vertex i) = some (p.path.vertex j) := by
  by_cases he : i.val % 2 = 0
  · have hi : i.val < p.path.length := by have := hp.1; omega
    exact ⟨⟨i.val + 1, by omega⟩, p.other ⟨i.val, hi⟩ he⟩
  · have hi : 0 < i.val := by omega
    have hm := N.symm (p.other ⟨i.val - 1, by omega⟩ (by change (i.val - 1) % 2 = 0; omega))
    have heq : i.val - 1 + 1 = i.val := by omega
    dsimp only at hm
    simp only [heq] at hm
    exact ⟨⟨i.val - 1, by omega⟩, hm⟩

end DifferencePath

namespace DifferencePath
variable {V : Type} [DecidableEq V] {G : Graph V} {M N : Matching G}

def Outside (p : DifferencePath M N) (v : V) : Prop := ∀ i, p.path.vertex i ≠ v
instance (p : DifferencePath M N) (v : V) : Decidable (p.Outside v) :=
  inferInstanceAs (Decidable (∀ i, p.path.vertex i ≠ v))

def removedGraph (p : DifferencePath M N) : Graph V where
  Adj u v := G.Adj u v ∧ p.Outside u ∧ p.Outside v
  symm := fun h => ⟨G.symm h.1, h.2.2, h.2.1⟩
  loopless := fun v h => G.loopless v h.1

omit [DecidableEq V] in
theorem mate_outside (p : DifferencePath M N) (K : Matching G)
    (hclosed : ∀ i v, K.mate (p.path.vertex i) = some v → ∃ j, p.path.vertex j = v)
    {u v : V} (hu : p.Outside u) (he : K.mate u = some v) : p.Outside v := by
  intro i hi
  have hrev : K.mate (p.path.vertex i) = some u := by rw [hi]; exact K.symm he
  obtain ⟨j, hj⟩ := hclosed i u hrev
  exact hu j hj

/-- Delete a component's vertices. Closure is proved separately for each matching. -/
def removeMatching (p : DifferencePath M N) (K : Matching G)
    (hclosed : ∀ i v, K.mate (p.path.vertex i) = some v → ∃ j, p.path.vertex j = v) :
    Matching p.removedGraph where
  mate v := if p.Outside v then K.mate v else none
  symm := by
    intro u v he
    split at he
    next hu =>
      have hv := p.mate_outside K hclosed hu he
      simp only [ite_eq_left hv]
      exact K.symm he
    next hu => contradiction
  edge := by
    intro u v he
    split at he
    next hu => exact ⟨K.edge he, hu, p.mate_outside K hclosed hu he⟩
    next hu => contradiction

def withoutLeft (p : DifferencePath M N) (hp : p.path.Augmenting) : Matching p.removedGraph :=
  p.removeMatching M (fun i _ h => p.path.old_mate_on_path hp i h)

def withoutRight (p : DifferencePath M N) (hp : p.path.Augmenting) : Matching p.removedGraph :=
  p.removeMatching N (by
    intro i v he
    obtain ⟨j, hj⟩ := p.other_mate_on_path hp i
    exact ⟨j, N.mate_unique hj he⟩)

theorem withoutLeft_mate (p : DifferencePath M N) (hp : p.path.Augmenting) (v : V) :
    (p.withoutLeft hp).mate v = if p.Outside v then M.mate v else none := rfl

theorem withoutRight_mate (p : DifferencePath M N) (hp : p.path.Augmenting) (v : V) :
    (p.withoutRight hp).mate v = if p.Outside v then N.mate v else none := rfl

omit [DecidableEq V] in
theorem not_outside_vertex (p : DifferencePath M N) (i : Fin (p.path.length + 1)) :
    ¬p.Outside (p.path.vertex i) := fun h => h i rfl

omit [DecidableEq V] in
theorem outside_ne_endpoints (p : DifferencePath M N) {v : V} (hv : p.Outside v) :
    v ≠ p.path.first ∧ v ≠ p.path.last :=
  ⟨fun h => hv ⟨0, by omega⟩ h.symm, fun h => hv ⟨p.path.length, by omega⟩ h.symm⟩

/-- Pointwise count balance after deleting a whole alternating augmenting component. -/
theorem removal_count_list (p : DifferencePath M N) (hp : p.path.Augmenting) (vs : List V) :
    vs.countP (fun v => ((p.withoutRight hp).mate v).isSome) +
      vs.countP (fun v => (M.mate v).isSome) + vs.count p.path.first + vs.count p.path.last =
    vs.countP (fun v => ((p.withoutLeft hp).mate v).isSome) +
      vs.countP (fun v => (N.mate v).isSome) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [List.countP_cons, List.countP_cons, List.count_cons, List.count_cons,
      List.countP_cons, List.countP_cons]
    rw [p.withoutLeft_mate hp, p.withoutRight_mate hp]
    by_cases hout : p.Outside v
    · have he := p.outside_ne_endpoints hout
      simp only [ite_eq_left hout, beq_iff_eq, he.1, he.2, ↓reduceIte]
      omega
    · have hmem : ∃ i, p.path.vertex i = v := by
        apply Classical.byContradiction
        intro hno
        exact hout (fun i hi => hno ⟨i, hi⟩)
      obtain ⟨i, rfl⟩ := hmem
      have hn := p.not_outside_vertex i
      obtain ⟨j, hj⟩ := p.other_mate_on_path hp i
      simp only [ite_eq_right (fun h => False.elim (hn h)), hj, Option.isSome_some,
        Option.isSome_none, ↓reduceIte]
      by_cases hi0 : i.val = 0
      · have hvf : p.path.vertex i = p.path.first :=
          congrArg p.path.vertex (Fin.ext hi0)
        have hf := p.path.start_free
        change M.mate p.path.first = none at hf
        have hd := p.path.augmenting_distinct hp
        rw [hvf]
        simp only [hf, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          beq_self_eq_true, beq_iff_eq, hd]
        omega
      · by_cases hil : i.val = p.path.length
        · have hvl : p.path.vertex i = p.path.last :=
            congrArg p.path.vertex (Fin.ext hil)
          have hf := hp.2
          change M.mate p.path.last = none at hf
          have hd := (p.path.augmenting_distinct hp).symm
          rw [hvl]
          simp only [hf, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
            beq_iff_eq, hd, beq_self_eq_true]
          omega
        · obtain ⟨w, hw⟩ := p.path.internal_matched i hi0 hil
          have hf : p.path.vertex i ≠ p.path.first := by
            intro he
            have := congrArg Fin.val (p.path.injective _ _ he)
            exact hi0 this
          have hl : p.path.vertex i ≠ p.path.last := by
            intro he
            have := congrArg Fin.val (p.path.injective _ _ he)
            exact hil this
          simp only [hw, Option.isSome_some, Bool.false_eq_true, ↓reduceIte, beq_iff_eq, hf, hl]
          omega


/-- Every vertex of a nonempty path in the deleted graph is outside the removed component. -/
theorem removed_path_outside (p : DifferencePath M N) (hp : p.path.Augmenting)
    (q : AltPath (p.withoutLeft hp)) (hq : q.Augmenting)
    (i : Fin (q.length + 1)) : p.Outside (q.vertex i) := by
  by_cases hi : i.val < q.length
  · exact (q.adjacent ⟨i.val, hi⟩).2.1
  · have hiend : i.val = q.length := by omega
    have hpos := q.augmenting_pos hq
    have hadj := (q.adjacent ⟨q.length - 1, by omega⟩).2.2
    have he : q.length - 1 + 1 = i.val := by omega
    simpa only [he] using hadj

/-- Lift an augmenting path from the deleted graph back to the original matching. -/
def liftPath (p : DifferencePath M N) (hp : p.path.Augmenting)
    (q : AltPath (p.withoutLeft hp)) (hq : q.Augmenting) : AltPath M where
  length := q.length
  vertex := q.vertex
  injective := q.injective
  adjacent := fun i => (q.adjacent i).1
  start_free := by
    have hfree := q.start_free
    change (if p.Outside (q.vertex ⟨0, by omega⟩) then M.mate _ else none) = none at hfree
    simpa only [Matching.Free, ite_eq_left (p.removed_path_outside hp q hq _)] using hfree
  alternating := by
    intro i
    have h := q.alternating i
    change ((if p.Outside (q.vertex ⟨i.val, by omega⟩) then M.mate _ else none) = _) ↔ _ at h
    simpa only [ite_eq_left (p.removed_path_outside hp q hq _)] using h

theorem liftPath_augmenting (p : DifferencePath M N) (hp : p.path.Augmenting)
    (q : AltPath (p.withoutLeft hp)) (hq : q.Augmenting) : (p.liftPath hp q hq).Augmenting := by
  refine ⟨hq.1, ?_⟩
  have hfree := hq.2
  change (if p.Outside q.last then M.mate q.last else none) = none at hfree
  have hout : p.Outside q.last := p.removed_path_outside hp q hq ⟨q.length, by omega⟩
  rw [ite_eq_left hout] at hfree
  exact hfree

def liftDifference (p : DifferencePath M N) (hp : p.path.Augmenting)
    (q : DifferencePath (p.withoutLeft hp) (p.withoutRight hp))
    (hq : q.path.Augmenting) : DifferencePath M N where
  path := p.liftPath hp q.path hq
  other := by
    intro i hi
    have hib : i.val < q.path.length := i.isLt
    change N.mate (q.path.vertex ⟨i.val, by omega⟩) = some (q.path.vertex ⟨i.val + 1, by omega⟩)
    have h := q.other i hi
    change (if p.Outside (q.path.vertex ⟨i.val, by omega⟩) then N.mate _ else none) = _ at h
    simpa only [ite_eq_left (p.removed_path_outside hp q.path hq _)] using h

theorem liftDifference_augmenting (p : DifferencePath M N) (hp : p.path.Augmenting)
    (q : DifferencePath (p.withoutLeft hp) (p.withoutRight hp)) (hq : q.path.Augmenting) :
    (p.liftDifference hp q hq).path.Augmenting := p.liftPath_augmenting hp q.path hq

theorem liftDifference_disjoint (p : DifferencePath M N) (hp : p.path.Augmenting)
    (q : DifferencePath (p.withoutLeft hp) (p.withoutRight hp)) (hq : q.path.Augmenting) :
    p.path.Disjoint (p.liftDifference hp q hq).path := by
  intro i j
  exact p.removed_path_outside hp q.path hq j i

end DifferencePath

namespace DifferencePath
variable {n : Nat} {G : Graph (Fin n)} {M N : Matching G}

theorem removal_cardinality_balance (p : DifferencePath M N) (hp : p.path.Augmenting) :
    (p.withoutRight hp).cardinality + M.cardinality + 1 =
      (p.withoutLeft hp).cardinality + N.cardinality := by
  have h := p.removal_count_list hp (List.finRange n)
  have hf := (List.nodup_finRange n).count_of_mem (List.mem_finRange p.path.first)
  have hl := (List.nodup_finRange n).count_of_mem (List.mem_finRange p.path.last)
  change (p.withoutRight hp).matchedCount + M.matchedCount + _ + _ =
      (p.withoutLeft hp).matchedCount + N.matchedCount at h
  rw [hf, hl, ← (p.withoutRight hp).twice_cardinality, ← M.twice_cardinality,
    ← (p.withoutLeft hp).twice_cardinality, ← N.twice_cardinality] at h
  omega

theorem withoutLeft_cardinality_le (p : DifferencePath M N) (hp : p.path.Augmenting) :
    (p.withoutLeft hp).cardinality ≤ M.cardinality := by
  have h : (p.withoutLeft hp).matchedCount ≤ M.matchedCount := by
    apply List.countP_mono_left
    intro v _ hv
    rw [p.withoutLeft_mate hp] at hv
    split at hv
    · exact hv
    · contradiction
  unfold Matching.cardinality
  omega

theorem withoutRight_cardinality_lt (p : DifferencePath M N) (hp : p.path.Augmenting) :
    (p.withoutRight hp).cardinality < N.cardinality := by
  have hb := p.removal_cardinality_balance hp
  have hle := p.withoutLeft_cardinality_le hp
  omega

end DifferencePath

/-- A family of disjoint augmenting components relative to two fixed matchings. -/
structure DifferenceFamily {V : Type} {G : Graph V} (M N : Matching G) where
  count : Nat
  path : Fin count → DifferencePath M N
  augmenting : ∀ i, (path i).path.Augmenting
  disjoint : ∀ i j, i ≠ j → (path i).path.Disjoint (path j).path

namespace DifferenceFamily
variable {V : Type} {G : Graph V} {M N : Matching G}

def empty (M N : Matching G) : DifferenceFamily M N where
  count := 0
  path := Fin.elim0
  augmenting := by intro i; exact Fin.elim0 i
  disjoint := fun i => Fin.elim0 i

def toAugmentingFamily (f : DifferenceFamily M N) : AugmentingFamily M where
  count := f.count
  path i := (f.path i).path
  augmenting := f.augmenting
  disjoint := f.disjoint


variable [DecidableEq V]

/-- Put back a removed augmenting component and lift the disjoint residual family. -/
def prepend (p : DifferencePath M N) (hp : p.path.Augmenting)
    (f : DifferenceFamily (p.withoutLeft hp) (p.withoutRight hp)) : DifferenceFamily M N where
  count := f.count + 1
  path i := if h : i.val = 0 then p else
    p.liftDifference hp (f.path ⟨i.val - 1, by omega⟩) (f.augmenting _)
  augmenting := by
    intro i
    split
    · exact hp
    · exact p.liftDifference_augmenting hp _ _
  disjoint := by
    intro i j hij
    split <;> split
    · rename_i hi hj
      exact False.elim (hij (Fin.ext (by omega)))
    · exact p.liftDifference_disjoint hp _ _
    · exact AltPath.disjoint_symm (p.liftDifference_disjoint hp _ _)
    · rename_i hi hj
      apply f.disjoint
      intro he
      apply hij
      apply Fin.ext
      have hv : i.val - 1 = j.val - 1 := congrArg Fin.val he
      omega

end DifferenceFamily

/-- Symmetric-difference packing: there are exactly `|N|-|M|` vertex-disjoint
M-augmenting components using only N/M edges. The whole decomposition is proved
by deleting each component, not assumed as a black-box theorem. -/
theorem exists_differenceFamily (n : Nat) (G : Graph (Fin n)) (M N : Matching G) :
    ∃ f : DifferenceFamily M N, f.count = N.cardinality - M.cardinality := by
  classical
  by_cases hle : N.cardinality ≤ M.cardinality
  · exact ⟨DifferenceFamily.empty M N, by change 0 = _; omega⟩
  · have hlt : M.cardinality < N.cardinality := by omega
    obtain ⟨p, hp⟩ := larger_has_differenceAugmenting M N hlt
    obtain ⟨f, hf⟩ := exists_differenceFamily n p.removedGraph (p.withoutLeft hp) (p.withoutRight hp)
    refine ⟨DifferenceFamily.prepend p hp f, ?_⟩
    change f.count + 1 = N.cardinality - M.cardinality
    have hbalance := p.removal_cardinality_balance hp
    omega
termination_by N.cardinality
decreasing_by exact p.withoutRight_cardinality_lt hp

namespace AugmentingFamily
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

/-- Enumerate all vertices in a disjoint augmenting family. -/
def vertices (f : AugmentingFamily M) : List (Fin n) :=
  (List.finRange f.count).flatMap fun i =>
    (List.finRange ((f.path i).length + 1)).map (f.path i).vertex

theorem vertices_nodup (f : AugmentingFamily M) : f.vertices.Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro i _
    exact (List.nodup_finRange _).map _ (fun a b h he => h ((f.path i).injective a b he))
  · apply (List.nodup_finRange f.count).imp
    intro i j hij x hx y hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hy
    exact f.disjoint i j hij a b

/-- Every disjoint augmenting path of length at least `l` consumes `l+1` distinct
vertices, giving a packing bound independently of any algorithmic phase. -/
theorem vertices_length_lower (f : AugmentingFamily M) (l : Nat)
    (h : ∀ i, l ≤ (f.path i).length) : f.count * (l + 1) ≤ f.vertices.length := by
  have lower (is : List (Fin f.count)) : is.length * (l + 1) ≤
      (is.flatMap fun i => (List.finRange ((f.path i).length + 1)).map (f.path i).vertex).length := by
    induction is with
    | nil => simp
    | cons i is ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append,
        List.length_map, List.length_finRange, Nat.add_mul, Nat.one_mul]
      have hi := h i
      omega
  have hl := lower (List.finRange f.count)
  simp only [List.length_finRange] at hl
  exact hl

end AugmentingFamily

end MaximumMatching

end DifferencePacking

section PhaseProgress

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

end PhaseProgress

section PhaseDriver

/-! The executable outer augmentation loop, separated from the phase search.

Every supplied phase returns actual disjoint augmenting paths and `run` flips
them. Termination and cardinality gain require no completeness premise. Maximum
cardinality additionally requires proving that this particular phase search
returns an empty family only when there is no augmenting path. The concrete
deletion-aware MIN/MAX/DDFS search instantiates this interface in `BlockingPhase`.
-/
namespace MaximumMatching
namespace PhaseDriver

variable {n : Nat} {G : Graph (Fin n)}

/-- The data computed by a phase. No shortestness or completeness is asserted. -/
abbrev Search (G : Graph (Fin n)) := (M : Matching G) → AugmentingFamily M

structure Result (G : Graph (Fin n)) where
  matching : Matching G
  positivePhases : Nat
  augmentations : Nat

/-- Run genuine flips until the supplied search returns no paths. The natural
cardinality deficit proves termination, without an arbitrary fuel limit. -/
def run (search : Search G) (M : Matching G) : Result G :=
  let f := search M
  if _h : f.count = 0 then
    ⟨M, 0, 0⟩
  else
    let rest := run search f.run
    ⟨rest.matching, rest.positivePhases + 1, rest.augmentations + f.count⟩
termination_by n / 2 - M.cardinality
decreasing_by
  change n / 2 - (search M).run.cardinality < n / 2 - M.cardinality
  change (search M).count ≠ 0 at _h
  have hgain := (search M).run_cardinality
  have hbound := (search M).run.cardinality_le
  omega

/-- Exact cumulative cardinality gain, for every search implementation. -/
theorem run_cardinality (search : Search G) (M : Matching G) :
    (run search M).matching.cardinality = M.cardinality + (run search M).augmentations := by
  rw [run]
  split
  · simp
  · dsimp only
    have ih := run_cardinality search (search M).run
    have hg := (search M).run_cardinality
    omega
termination_by n / 2 - M.cardinality
decreasing_by
  have hg := (search M).run_cardinality
  have hb := (search M).run.cardinality_le
  omega

/-- Independent specification of the search's stopping condition. This is an
obligation for the actual MV phase, not a field assumed of its implementation. -/
def Complete (search : Search G) : Prop :=
  ∀ M, (search M).count = 0 → M.NoAugmentingPath

/-- Every positive search result is a maximal family of shortest augmenting
paths. A concrete blocking-phase implementation proves this specification. -/
def ShortestBlocking (search : Search G) : Prop :=
  ∀ M, (search M).count ≠ 0 → ∃ l, (search M).MaximalShortest l

/-- Conditional assembly theorem: any complete augmenting-family search makes
this executable outer loop return a maximum matching. It does not certify MV
until its concrete phase implementation satisfies `Complete`, as proved in
`BlockingPhase`. -/
theorem run_isMaximum (search : Search G) (hsearch : Complete search) (M : Matching G) :
    (run search M).matching.IsMaximum := by
  rw [run]
  split
  next hz => exact M.noAugmentingPath_isMaximum (hsearch M hz)
  next hn =>
    exact run_isMaximum search hsearch (search M).run
termination_by n / 2 - M.cardinality
decreasing_by
  have hg := (search M).run_cardinality
  have hb := (search M).run.cardinality_le
  omega

end PhaseDriver
end MaximumMatching

end PhaseDriver
