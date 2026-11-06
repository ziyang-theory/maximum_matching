import MaximumMatching.Optimality
import MaximumMatching.Family

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
