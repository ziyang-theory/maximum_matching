import MaximumMatching.Augmentation

/-! Operations on disjoint augmenting paths, as used by an MV phase.
This does not find the paths or prove maximality/shortestness of a family. -/
namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

def Disjoint (p q : AltPath M) : Prop := ∀ i j, p.vertex i ≠ q.vertex j

theorem disjoint_symm {p q : AltPath M} (h : p.Disjoint q) : q.Disjoint p := by
  intro j i he
  exact h i j he.symm

variable [DecidableEq V]

theorem augment_mate_on_disjoint (p q : AltPath M) (hp : p.Augmenting)
    (hd : p.Disjoint q) (j : Fin (q.length + 1)) :
    (p.augment hp).mate (q.vertex j) = M.mate (q.vertex j) := by
  exact p.flipMate_off_path hp (by rintro ⟨i, hi⟩; exact hd i j hi)

/-- A disjoint path is still an alternating simple path after the first flip.
Its vertices and edge length are unchanged. -/
def rebase (p : AltPath M) (hp : p.Augmenting) (q : AltPath M)
    (hd : p.Disjoint q) : AltPath (p.augment hp) where
  length := q.length
  vertex := q.vertex
  injective := q.injective
  adjacent := q.adjacent
  start_free := by
    change (p.augment hp).mate _ = none
    rw [p.augment_mate_on_disjoint q hp hd]
    exact q.start_free
  alternating := by
    intro i
    rw [p.augment_mate_on_disjoint q hp hd]
    exact q.alternating i

theorem rebase_augmenting (p : AltPath M) (hp : p.Augmenting) (q : AltPath M)
    (hq : q.Augmenting) (hd : p.Disjoint q) : (p.rebase hp q hd).Augmenting := by
  refine ⟨hq.1, ?_⟩
  change (p.augment hp).mate (q.vertex ⟨q.length, by omega⟩) = none
  rw [p.augment_mate_on_disjoint q hp hd]
  exact hq.2

/-- Two paths chosen against the same initial matching can be flipped in sequence. -/
def augmentPair (p q : AltPath M) (hp : p.Augmenting) (hq : q.Augmenting)
    (hd : p.Disjoint q) : Matching G :=
  (p.rebase hp q hd).augment (p.rebase_augmenting hp q hq hd)

theorem augmentPair_free_iff (p q : AltPath M) (hp : p.Augmenting)
    (hq : q.Augmenting) (hd : p.Disjoint q) (v : V) :
    (p.augmentPair q hp hq hd).Free v ↔
      M.Free v ∧ v ≠ p.first ∧ v ≠ p.last ∧ v ≠ q.first ∧ v ≠ q.last := by
  rw [augmentPair, augment_free_iff, augment_free_iff]
  change (M.Free v ∧ v ≠ p.first ∧ v ≠ p.last) ∧ v ≠ q.first ∧ v ≠ q.last ↔ _
  simp only [and_assoc]

end AltPath

namespace AltPath
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

theorem augmentPair_cardinality (p q : AltPath M) (hp : p.Augmenting)
    (hq : q.Augmenting) (hd : p.Disjoint q) :
    (p.augmentPair q hp hq hd).cardinality = M.cardinality + 2 := by
  unfold augmentPair
  rw [augment_cardinality, augment_cardinality]

end AltPath
end MaximumMatching
