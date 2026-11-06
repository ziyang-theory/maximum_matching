import Std

/-! Graph and matching data, independent of any algorithm's correctness property. -/
namespace MaximumMatching

structure Graph (V : Type) where
  Adj : V → V → Prop
  symm : ∀ {u v}, Adj u v → Adj v u
  loopless : ∀ v, ¬ Adj v v

structure Matching {V : Type} (G : Graph V) where
  mate : V → Option V
  symm : ∀ {u v}, mate u = some v → mate v = some u
  edge : ∀ {u v}, mate u = some v → G.Adj u v

namespace Matching
variable {V : Type} {G : Graph V}

def Free (M : Matching G) (v : V) : Prop := M.mate v = none

def empty (G : Graph V) : Matching G where
  mate := fun _ => none
  symm := by simp
  edge := by simp

theorem mate_ne_self (M : Matching G) {u : V} : M.mate u ≠ some u := by
  intro h
  exact G.loopless u (M.edge h)

theorem mate_unique (M : Matching G) {u v w : V}
    (hv : M.mate u = some v) (hw : M.mate u = some w) : v = w := by
  exact Option.some.inj (hv.symm.trans hw)
end Matching

/-- A vertex-simple alternating path beginning at a free vertex. Edge index zero is
unmatched. Indices and length are edge counts; the path has `length + 1` vertices. -/
structure AltPath {V : Type} {G : Graph V} (M : Matching G) where
  length : Nat
  vertex : Fin (length + 1) → V
  injective : ∀ i j, vertex i = vertex j → i = j
  adjacent : ∀ i : Fin length,
    G.Adj (vertex ⟨i.val, by omega⟩) (vertex ⟨i.val + 1, by omega⟩)
  start_free : M.Free (vertex ⟨0, by omega⟩)
  alternating : ∀ i : Fin length,
    (M.mate (vertex ⟨i.val, by omega⟩) =
      some (vertex ⟨i.val + 1, by omega⟩)) ↔ i.val % 2 = 1

namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

def first (p : AltPath M) : V := p.vertex ⟨0, by omega⟩
def last (p : AltPath M) : V := p.vertex ⟨p.length, by omega⟩

/-- An augmenting path has distinct free endpoints; odd length is explicit. -/
def Augmenting (p : AltPath M) : Prop := p.length % 2 = 1 ∧ M.Free p.last

def trivial (M : Matching G) (v : V) (hv : M.Free v) : AltPath M where
  length := 0
  vertex := fun _ => v
  injective := by intros; exact Fin.ext (by omega)
  adjacent := by intro i; exact Fin.elim0 i
  start_free := hv
  alternating := by intro i; exact Fin.elim0 i

theorem augmenting_pos (p : AltPath M) (h : p.Augmenting) : 0 < p.length := by
  have := h.1
  omega

theorem augmenting_distinct (p : AltPath M) (h : p.Augmenting) : p.first ≠ p.last := by
  intro heq
  have hi := p.injective ⟨0, by omega⟩ ⟨p.length, by omega⟩ heq
  have he : 0 = p.length := congrArg Fin.val hi
  have := p.augmenting_pos h
  omega
end AltPath
end MaximumMatching
