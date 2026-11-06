import MaximumMatching.Levels
import MaximumMatching.Phase
import MaximumMatching.Min
import MaximumMatching.Bud

/-! Small kernel-checked boundary examples. These do not replace universal proofs. -/
namespace MaximumMatching.Examples

/-- The triangle with one matching edge, 1--2, and free vertex 0. -/
def triangle : Graph (Fin 3) where
  Adj u v := u ≠ v
  symm := Ne.symm
  loopless := by intro v h; exact h rfl

def triangleMatching : Matching triangle where
  mate v := if v = 0 then none else if v = 1 then some 2 else some 1
  symm := by decide
  edge := by dsimp [triangle]; decide

theorem triangle_free (v : Fin 3) : triangleMatching.Free v ↔ v = 0 := by
  unfold Matching.Free
  revert v
  decide

def triangleEvenPath : AltPath triangleMatching where
  length := 2
  vertex := fun i => i
  injective := by intro i j h; exact h
  adjacent := by dsimp [triangle]; decide
  start_free := rfl
  alternating := by decide

def triangleOddPath : AltPath triangleMatching where
  length := 1
  vertex := fun i => if i = 0 then 0 else 2
  injective := by decide
  adjacent := by dsimp [triangle]; decide
  start_free := rfl
  alternating := by decide

theorem triangle_evenlevel : evenlevel triangleMatching 2 = some 2 := by
  apply (level_eq_some_iff _ _ _ _).2
  refine ⟨⟨triangleEvenPath, rfl, rfl, rfl⟩, ?_⟩
  rintro k ⟨p, hend, hlen, hpar⟩
  by_cases hz : k = 0
  · have hi : (⟨0, by omega⟩ : Fin (p.length + 1)) = ⟨p.length, by omega⟩ :=
      Fin.ext (by omega)
    have hf := p.start_free
    rw [hi] at hf
    change triangleMatching.Free p.last at hf
    rw [hend] at hf
    have : (2 : Fin 3) = 0 := (triangle_free 2).1 hf
    contradiction
  · omega

theorem triangle_oddlevel : oddlevel triangleMatching 2 = some 1 := by
  apply (level_eq_some_iff _ _ _ _).2
  refine ⟨⟨triangleOddPath, rfl, rfl, rfl⟩, ?_⟩
  rintro k ⟨_, _, _, hpar⟩
  omega

theorem triangle_no_augmenting : ¬ ∃ p : AltPath triangleMatching, p.Augmenting := by
  rintro ⟨p, hp⟩
  have hf : p.first = 0 := (triangle_free p.first).1 p.start_free
  have hl : p.last = 0 := (triangle_free p.last).1 hp.2
  exact p.augmenting_distinct hp (hf.trans hl.symm)

theorem triangle_oddlevel_free_infinite : oddlevel triangleMatching 0 = none := by
  apply (level_eq_none_iff _ _ _).2
  rintro ⟨k, p, hend, hlen, hpar⟩
  apply triangle_no_augmenting
  refine ⟨p, ?_, ?_⟩
  · omega
  · rw [hend]
    exact (triangle_free 0).2 rfl

/-- The alternating walk 0,1,2,0 has free endpoints but repeats its first vertex.
Treating such a walk as an augmenting *path* would give a false positive. -/
def triangleWalk (i : Fin 4) : Fin 3 := if h : i.val = 3 then 0 else ⟨i.val, by omega⟩

theorem triangleWalk_edges : ∀ i : Fin 3,
    triangle.Adj (triangleWalk ⟨i.val, by omega⟩)
      (triangleWalk ⟨i.val + 1, by omega⟩) := by dsimp [triangle]; decide

theorem triangleWalk_alternates : ∀ i : Fin 3,
    (triangleMatching.mate (triangleWalk ⟨i.val, by omega⟩) =
      some (triangleWalk ⟨i.val + 1, by omega⟩)) ↔ i.val % 2 = 1 := by decide

theorem triangleWalk_not_simple :
    ¬ (∀ i j, triangleWalk i = triangleWalk j → i = j) := by
  intro h
  have he := h 0 3 (by decide)
  contradiction

/-- A four-vertex path with its middle edge matched. -/
def lineFour : Graph (Fin 4) where
  Adj u v := u.val + 1 = v.val ∨ v.val + 1 = u.val
  symm := fun h => h.elim Or.inr Or.inl
  loopless := by intro v h; omega

def middleMatching : Matching lineFour where
  mate v := if v = 1 then some 2 else if v = 2 then some 1 else none
  symm := by decide
  edge := by dsimp [lineFour]; decide

def linePath : AltPath middleMatching where
  length := 3
  vertex := fun i => i
  injective := by intro i j h; exact h
  adjacent := by dsimp [lineFour]; decide
  start_free := rfl
  alternating := by decide

theorem linePath_augmenting : linePath.Augmenting := ⟨rfl, rfl⟩

def lineAugmented : Matching lineFour := linePath.augment linePath_augmenting

theorem lineAugmented_mates :
    (List.finRange 4).map lineAugmented.mate = [some 1, some 0, some 3, some 2] := by decide

theorem lineAugmented_size : lineAugmented.cardinality = 2 := by decide

/-- Two free roots reach vertex 2 through unmatched edges at search level zero. -/
def completeFour : Graph (Fin 4) where
  Adj u v := u ≠ v
  symm := Ne.symm
  loopless := by intro v h; exact h rfl

instance : DecidableRel completeFour.Adj := fun u v => inferInstanceAs (Decidable (u ≠ v))

def tieMatching : Matching completeFour where
  mate v := if v = 2 then some 3 else if v = 3 then some 2 else none
  symm := by decide
  edge := by dsimp [completeFour]; decide

def afterFirstScan : Search.State (Fin 4) :=
  Search.scanCandidate tieMatching 0 0 2 (Search.initial tieMatching)

theorem min_keeps_tied_predecessors :
    (Search.scanCandidate tieMatching 0 1 2 afterFirstScan).predecessors 2 = [1, 0] := by decide

def budChain : BudForest (Fin 4) where
  parent v := ⟨v.val - 1, by omega⟩
  rank := Fin.val
  decreases := by
    intro v h
    have hv : v.val ≠ 0 := by
      intro he
      apply h
      exact Fin.ext (by simp [he])
    dsimp
    omega

theorem budChain_root : budChain.root 3 = 0 := by
  simp [BudForest.root, budChain]
  decide

theorem compressed_chain_root : (budChain.compress 3).root 3 = 0 := by
  rw [BudForest.compress_root]
  exact budChain_root

end MaximumMatching.Examples
