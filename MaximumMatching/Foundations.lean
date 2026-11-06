import Std

section Basic

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

end Basic

section PathLemmas

namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The matched neighbor of an odd-indexed, nonterminal path vertex is its successor. -/
theorem mate_next (p : AltPath M) (i : Nat) (hi : i < p.length) (hodd : i % 2 = 1) :
    M.mate (p.vertex ⟨i, by omega⟩) = some (p.vertex ⟨i + 1, by omega⟩) :=
  (p.alternating ⟨i, hi⟩).2 hodd

/-- The matched neighbor of a positive even-indexed path vertex is its predecessor. -/
theorem mate_previous (p : AltPath M) (i : Nat) (hi : i ≤ p.length)
    (hpos : 0 < i) (heven : i % 2 = 0) :
    M.mate (p.vertex ⟨i, by omega⟩) = some (p.vertex ⟨i - 1, by omega⟩) := by
  have h := M.symm (p.mate_next (i - 1) (by omega) (by omega))
  simpa only [show i - 1 + 1 = i by omega] using h

/-- Appending the matched neighbor of an odd terminal vertex does not repeat a vertex.
This is the nontrivial simplicity step in the proof of Lemma 5.2. -/
theorem matched_last_fresh (p : AltPath M) (hodd : p.length % 2 = 1)
    {v : V} (hv : M.mate p.last = some v) : ∀ i, p.vertex i ≠ v := by
  intro i heq
  have hvback : M.mate (p.vertex i) = some p.last := by
    simpa only [heq] using M.symm hv
  by_cases hz : i.val = 0
  · have hi : i = ⟨0, by omega⟩ := Fin.ext hz
    have hfree := p.start_free
    rw [hi] at hvback
    unfold Matching.Free at hfree
    rw [hfree] at hvback
    contradiction
  · by_cases hpar : i.val % 2 = 0
    · have hp := p.mate_previous i.val (by omega) (by omega) hpar
      have he := M.mate_unique hp hvback
      have he' := p.injective ⟨i.val - 1, by omega⟩ ⟨p.length, by omega⟩ he
      have hval : i.val - 1 = p.length := congrArg Fin.val he'
      omega
    · by_cases hlast : i.val = p.length
      · have hi : i = ⟨p.length, by omega⟩ := Fin.ext hlast
        have hl : p.last = v := by simpa only [hi, last] using heq
        exact M.mate_ne_self (hl ▸ hv)
      · have hn := p.mate_next i.val (by omega) (by omega)
        have he := M.mate_unique hn hvback
        have he' := p.injective ⟨i.val + 1, by omega⟩ ⟨p.length, by omega⟩ he
        have hval : i.val + 1 = p.length := congrArg Fin.val he'
        omega

/-- Restrict an alternating simple path to an initial segment. -/
def take (p : AltPath M) (k : Nat) (hk : k ≤ p.length) : AltPath M where
  length := k
  vertex := fun i => p.vertex ⟨i.val, by omega⟩
  injective := by
    intro i j he
    have hh := p.injective ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ he
    apply Fin.ext
    have hv : i.val = j.val := congrArg (fun x : Fin (p.length + 1) => x.val) hh
    exact hv
  adjacent := fun i => p.adjacent ⟨i.val, by omega⟩
  start_free := p.start_free
  alternating := fun i => p.alternating ⟨i.val, by omega⟩

@[simp] theorem take_length (p : AltPath M) (k : Nat) (hk : k ≤ p.length) :
    (p.take k hk).length = k := rfl

@[simp] theorem take_last (p : AltPath M) (k : Nat) (hk : k ≤ p.length) :
    (p.take k hk).last = p.vertex ⟨k, by omega⟩ := rfl

/-- Append a fresh adjacent vertex with the edge parity required by alternation. -/
def append (p : AltPath M) (v : V) (hfresh : ∀ i, p.vertex i ≠ v)
    (hadj : G.Adj p.last v)
    (hpar : (M.mate p.last = some v) ↔ p.length % 2 = 1) : AltPath M where
  length := p.length + 1
  vertex := fun i => if h : i.val ≤ p.length then p.vertex ⟨i.val, by omega⟩ else v
  injective := by
    intro i j he
    split at he <;> split at he
    · rename_i hi hj
      have hh := p.injective ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ he
      apply Fin.ext
      have hv : i.val = j.val := congrArg (fun x : Fin (p.length + 1) => x.val) hh
      exact hv
    · exact False.elim (hfresh _ he)
    · exact False.elim (hfresh _ he.symm)
    · exact Fin.ext (by omega)
  adjacent := by
    intro i
    by_cases hi : i.val < p.length
    · simpa only [dite_eq_left (show i.val ≤ p.length by omega),
        dite_eq_left (show i.val + 1 ≤ p.length by omega)] using p.adjacent ⟨i.val, hi⟩
    · have he : i.val = p.length := by omega
      simp only [he, Nat.le_refl, dite_true,
        show ¬p.length + 1 ≤ p.length by omega, dite_false]
      exact hadj
  start_free := by simpa using p.start_free
  alternating := by
    intro i
    by_cases hi : i.val < p.length
    · simpa only [dite_eq_left (show i.val ≤ p.length by omega),
        dite_eq_left (show i.val + 1 ≤ p.length by omega)] using p.alternating ⟨i.val, hi⟩
    · have he : i.val = p.length := by omega
      simp only [he, Nat.le_refl, dite_true,
        show ¬p.length + 1 ≤ p.length by omega, dite_false]
      exact hpar

@[simp] theorem append_length (p : AltPath M) (v : V) (hfresh : ∀ i, p.vertex i ≠ v)
    (hadj : G.Adj p.last v) (hpar : (M.mate p.last = some v) ↔ p.length % 2 = 1) :
    (p.append v hfresh hadj hpar).length = p.length + 1 := rfl

@[simp] theorem append_last (p : AltPath M) (v : V) (hfresh : ∀ i, p.vertex i ≠ v)
    (hadj : G.Adj p.last v) (hpar : (M.mate p.last = some v) ↔ p.length % 2 = 1) :
    (p.append v hfresh hadj hpar).last = v := by
  simp only [last, append]
  split
  · omega
  · rfl

/-- Extend an odd path by its terminal matched edge. -/
def appendMatched (p : AltPath M) (hodd : p.length % 2 = 1)
    {v : V} (hv : M.mate p.last = some v) : AltPath M :=
  p.append v (p.matched_last_fresh hodd hv) (M.edge hv) ⟨fun _ => hodd, fun _ => hv⟩

@[simp] theorem appendMatched_length (p : AltPath M) (hodd : p.length % 2 = 1)
    {v : V} (hv : M.mate p.last = some v) :
    (p.appendMatched hodd hv).length = p.length + 1 := rfl

@[simp] theorem appendMatched_last (p : AltPath M) (hodd : p.length % 2 = 1)
    {v : V} (hv : M.mate p.last = some v) :
    (p.appendMatched hodd hv).last = v := by simp [appendMatched]

end AltPath
end MaximumMatching

end PathLemmas

section Augmentation

/-! Augmentation along a simple alternating path. The construction pairs consecutive
vertices at even edge indices and leaves mates outside the path unchanged. -/
namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The partner after flipping an odd-length path. -/
def flipIndex (p : AltPath M) (hodd : p.length % 2 = 1)
    (i : Fin (p.length + 1)) : Fin (p.length + 1) :=
  if h : i.val % 2 = 0 then ⟨i.val + 1, by omega⟩
  else ⟨i.val - 1, by omega⟩

theorem flipIndex_involutive (p : AltPath M) (hodd : p.length % 2 = 1)
    (i : Fin (p.length + 1)) : p.flipIndex hodd (p.flipIndex hodd i) = i := by
  apply Fin.ext
  unfold flipIndex
  split <;> dsimp only <;> split <;> dsimp only <;> omega

theorem flipIndex_adjacent (p : AltPath M) (hodd : p.length % 2 = 1)
    (i : Fin (p.length + 1)) : G.Adj (p.vertex i) (p.vertex (p.flipIndex hodd i)) := by
  unfold flipIndex
  split
  next h =>
    have hi : i.val < p.length := by omega
    exact p.adjacent ⟨i.val, hi⟩
  next h =>
    have hi : i.val - 1 < p.length := by omega
    have he : i.val - 1 + 1 = i.val := by omega
    simpa only [he] using G.symm (p.adjacent ⟨i.val - 1, hi⟩)

/-- A matched edge incident to a vertex on an augmenting path remains inside it. -/
theorem old_mate_on_path (p : AltPath M) (hp : p.Augmenting)
    (i : Fin (p.length + 1)) {v : V} (hv : M.mate (p.vertex i) = some v) :
    ∃ j, p.vertex j = v := by
  by_cases hi0 : i.val = 0
  · have he : i = ⟨0, by omega⟩ := Fin.ext hi0
    rw [he] at hv
    have hf := p.start_free
    unfold Matching.Free at hf
    rw [hf] at hv
    contradiction
  by_cases hilast : i.val = p.length
  · have he : i = ⟨p.length, by omega⟩ := Fin.ext hilast
    rw [he] at hv
    have hf := hp.2
    change M.mate (p.vertex ⟨p.length, by omega⟩) = none at hf
    rw [hf] at hv
    contradiction
  by_cases heven : i.val % 2 = 0
  · exact ⟨⟨i.val - 1, by omega⟩,
      M.mate_unique (p.mate_previous i.val (by omega) (by omega) heven) hv⟩
  · exact ⟨⟨i.val + 1, by omega⟩,
      M.mate_unique (p.mate_next i.val (by omega) (by omega)) hv⟩

variable [DecidableEq V]

/-- Executable lookup of a vertex's unique index in a simple path. -/
def indexOf (p : AltPath M) (v : V) : Option (Fin (p.length + 1)) :=
  (List.finRange (p.length + 1)).find? (fun i => decide (p.vertex i = v))

theorem indexOf_some (p : AltPath M) {v : V} {i : Fin (p.length + 1)}
    (h : p.indexOf v = some i) : p.vertex i = v := by
  have h' := List.find?_some h
  exact of_decide_eq_true h'

theorem indexOf_none_iff (p : AltPath M) (v : V) :
    p.indexOf v = none ↔ ¬ ∃ i, p.vertex i = v := by
  simp only [indexOf, List.find?_eq_none]
  constructor
  · intro h ⟨i, hi⟩
    exact h i (List.mem_finRange i) (by simp [hi])
  · intro h i _ heq
    exact h ⟨i, of_decide_eq_true heq⟩

theorem indexOf_vertex (p : AltPath M) (i : Fin (p.length + 1)) :
    p.indexOf (p.vertex i) = some i := by
  cases h : p.indexOf (p.vertex i) with
  | none => exact False.elim ((p.indexOf_none_iff _).mp h ⟨i, rfl⟩)
  | some j =>
    have he := p.injective _ _ (p.indexOf_some h)
    subst j
    rfl

/-- Look up the vertex on the path and return its mate after the path flip. -/
def flipMate (p : AltPath M) (hp : p.Augmenting) (v : V) : Option V :=
  match p.indexOf v with
  | some i => some (p.vertex (p.flipIndex hp.1 i))
  | none => M.mate v

theorem flipMate_vertex (p : AltPath M) (hp : p.Augmenting)
    (i : Fin (p.length + 1)) :
    p.flipMate hp (p.vertex i) = some (p.vertex (p.flipIndex hp.1 i)) := by
  simp only [flipMate, p.indexOf_vertex]

theorem flipMate_off_path (p : AltPath M) (hp : p.Augmenting)
    {v : V} (hv : ¬ ∃ i, p.vertex i = v) : p.flipMate hp v = M.mate v := by
  simp only [flipMate, (p.indexOf_none_iff v).mpr hv]

theorem flipMate_symmetric (p : AltPath M) (hp : p.Augmenting)
    {u v : V} (huv : p.flipMate hp u = some v) : p.flipMate hp v = some u := by
  by_cases hu : ∃ i, p.vertex i = u
  · obtain ⟨i, rfl⟩ := hu
    rw [p.flipMate_vertex hp] at huv
    have hv : p.vertex (p.flipIndex hp.1 i) = v := Option.some.inj huv
    rw [← hv, p.flipMate_vertex hp, p.flipIndex_involutive]
  · rw [p.flipMate_off_path hp hu] at huv
    have hv : ¬ ∃ i, p.vertex i = v := by
      rintro ⟨i, hi⟩
      have hrev := M.symm huv
      rw [← hi] at hrev
      exact hu (p.old_mate_on_path hp i hrev)
    rw [p.flipMate_off_path hp hv]
    exact M.symm huv

theorem flipMate_edge (p : AltPath M) (hp : p.Augmenting)
    {u v : V} (huv : p.flipMate hp u = some v) : G.Adj u v := by
  by_cases hu : ∃ i, p.vertex i = u
  · obtain ⟨i, rfl⟩ := hu
    rw [p.flipMate_vertex hp] at huv
    have hv : p.vertex (p.flipIndex hp.1 i) = v := Option.some.inj huv
    rw [← hv]
    exact p.flipIndex_adjacent hp.1 i
  · rw [p.flipMate_off_path hp hu] at huv
    exact M.edge huv

/-- The actual augmentation operation; validity is proved from the path data. -/
def augment (p : AltPath M) (hp : p.Augmenting) : Matching G where
  mate := p.flipMate hp
  symm := p.flipMate_symmetric hp
  edge := p.flipMate_edge hp

/-- On each path edge, augmentation changes matched parity from odd to even. -/
theorem augment_path_edge (p : AltPath M) (hp : p.Augmenting) (i : Fin p.length) :
    ((p.augment hp).mate (p.vertex ⟨i.val, by omega⟩) =
      some (p.vertex ⟨i.val + 1, by omega⟩)) ↔ i.val % 2 = 0 := by
  change p.flipMate hp (p.vertex ⟨i.val, by omega⟩) = _ ↔ _
  rw [p.flipMate_vertex hp]
  constructor
  · intro h
    have he := p.injective _ _ (Option.some.inj h)
    have hv := congrArg Fin.val he
    unfold flipIndex at hv
    split at hv <;> dsimp only at hv
    · assumption
    · omega
  · intro hi
    unfold flipIndex
    simp only [hi, ↓reduceDIte]

/-- Every mate outside the path is unchanged. -/
theorem augment_off_path (p : AltPath M) (hp : p.Augmenting)
    {v : V} (hv : ¬ ∃ i, p.vertex i = v) : (p.augment hp).mate v = M.mate v :=
  p.flipMate_off_path hp hv

omit [DecidableEq V] in
/-- Every internal vertex was already matched before augmentation. -/
theorem internal_matched (p : AltPath M)
    (i : Fin (p.length + 1)) (h0 : i.val ≠ 0) (hlast : i.val ≠ p.length) :
    ∃ v, M.mate (p.vertex i) = some v := by
  by_cases heven : i.val % 2 = 0
  · exact ⟨_, p.mate_previous i.val (by omega) (by omega) heven⟩
  · exact ⟨_, p.mate_next i.val (by omega) (by omega)⟩

/-- Augmentation removes precisely the two endpoints from the free vertices. -/
theorem augment_free_iff (p : AltPath M) (hp : p.Augmenting) (v : V) :
    (p.augment hp).Free v ↔ M.Free v ∧ v ≠ p.first ∧ v ≠ p.last := by
  change p.flipMate hp v = none ↔ M.mate v = none ∧ v ≠ p.first ∧ v ≠ p.last
  constructor
  · intro hf
    have hoff : ¬ ∃ i, p.vertex i = v := by
      rintro ⟨i, rfl⟩
      rw [p.flipMate_vertex hp] at hf
      contradiction
    refine ⟨?_, ?_, ?_⟩
    · rwa [p.flipMate_off_path hp hoff] at hf
    · intro he; exact hoff ⟨⟨0, by omega⟩, he.symm⟩
    · intro he; exact hoff ⟨⟨p.length, by omega⟩, he.symm⟩
  · rintro ⟨hf, hfirst, hlast⟩
    have hoff : ¬ ∃ i, p.vertex i = v := by
      rintro ⟨i, rfl⟩
      have h0 : i.val ≠ 0 := by
        intro he
        exact hfirst (congrArg p.vertex (Fin.ext he))
      have hl : i.val ≠ p.length := by
        intro he
        exact hlast (congrArg p.vertex (Fin.ext he))
      obtain ⟨w, hw⟩ := p.internal_matched i h0 hl
      rw [hf] at hw
      contradiction
    rw [p.flipMate_off_path hp hoff, hf]


/-- Vertex count on an arbitrary list, including multiplicities. -/
theorem augment_matched_count_list (p : AltPath M) (hp : p.Augmenting) (vs : List V) :
    vs.countP (fun v => ((p.augment hp).mate v).isSome) =
      vs.countP (fun v => (M.mate v).isSome) + vs.count p.first + vs.count p.last := by
  have hdistinct := p.augmenting_distinct hp
  have hfirst : M.mate p.first = none := p.start_free
  have hlast : M.mate p.last = none := hp.2
  have hnew (v : V) : ((p.augment hp).mate v).isSome = true ↔
      (M.mate v).isSome = true ∨ v = p.first ∨ v = p.last := by
    simp only [Option.isSome_iff_ne_none]
    have h := p.augment_free_iff hp v
    unfold Matching.Free at h
    grind
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.countP_cons, List.count_cons]
    by_cases hvf : v = p.first
    · subst v
      have hn := (hnew p.first).mpr (Or.inr (Or.inl rfl))
      simp only [hn, hfirst, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        beq_self_eq_true, beq_iff_eq, hdistinct, ih]
      omega
    · by_cases hvl : v = p.last
      · subst v
        have hn := (hnew p.last).mpr (Or.inr (Or.inr rfl))
        simp only [hn, hlast, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          beq_self_eq_true, beq_iff_eq, hvf, ih]
        omega
      · have hn : ((p.augment hp).mate v).isSome = (M.mate v).isSome := by
          apply Bool.eq_iff_iff.mpr
          simpa only [hvf, hvl, or_false] using hnew v
        simp only [hn, beq_iff_eq, hvf, hvl, ↓reduceIte, ih]
        omega

end AltPath

namespace Matching
/-- A matching saturates an even number of vertices in any finite, duplicate-free
vertex list closed under its mate function. -/
theorem matched_count_even_list {V : Type} [DecidableEq V] {G : Graph V}
    (M : Matching G) (vs : List V) (hd : vs.Nodup)
    (hc : ∀ u ∈ vs, ∀ v, M.mate u = some v → v ∈ vs) :
    (vs.countP (fun v => (M.mate v).isSome)) % 2 = 0 := by
  cases vs with
  | nil => simp
  | cons u us =>
    obtain ⟨hunot, hdus⟩ := List.nodup_cons.mp hd
    cases hu : M.mate u with
    | none =>
      have hcus : ∀ x ∈ us, ∀ y, M.mate x = some y → y ∈ us := by
        intro x hx y hxy
        have hy := hc x (List.mem_cons_of_mem _ hx) y hxy
        rcases List.mem_cons.mp hy with he | he
        · subst y
          have hux := M.symm hxy
          rw [hu] at hux
          contradiction
        · exact he
      have ih := matched_count_even_list M us hdus hcus
      simpa only [List.countP_cons, hu, Option.isSome_none, Bool.false_eq_true,
        ↓reduceIte, Nat.add_zero] using ih
    | some v =>
      have huv : u ≠ v := by
        intro h; subst v; exact M.mate_ne_self hu
      have hvu := M.symm hu
      have hvus : v ∈ us := by
        have hv := hc u (List.mem_cons_self) v hu
        rcases List.mem_cons.mp hv with h | h
        · exact False.elim (huv h.symm)
        · exact h
      have hcrest : ∀ x ∈ us.erase v, ∀ y, M.mate x = some y → y ∈ us.erase v := by
        intro x hx y hxy
        obtain ⟨hxv, hxus⟩ := hdus.mem_erase_iff.mp hx
        have hy := hc x (List.mem_cons_of_mem _ hxus) y hxy
        have hyu : y ≠ u := by
          intro he; subst y
          have hxu := M.symm hxy
          have hxeq : x = v := M.mate_unique hxu hu
          exact hxv hxeq
        have hyv : y ≠ v := by
          intro he; subst y
          have hxv' := M.symm hxy
          have hxeq : x = u := M.mate_unique hxv' hvu
          exact hunot (hxeq ▸ hxus)
        apply hdus.mem_erase_iff.mpr
        refine ⟨hyv, ?_⟩
        rcases List.mem_cons.mp hy with he | he
        · exact False.elim (hyu he)
        · exact he
      have ih := matched_count_even_list M (us.erase v) (hdus.erase v) hcrest
      have hcoun := (List.perm_cons_erase hvus).countP_eq (fun x => (M.mate x).isSome)
      simp only [List.countP_cons, hu, hvu, Option.isSome_some, ↓reduceIte] at hcoun ⊢
      omega
termination_by vs.length
decreasing_by
  · simp_all only [List.length_cons]
    omega
  · have hlen := List.length_erase_le (l := us) (a := v)
    simp_all only [List.length_cons]
    omega

/-- Number of saturated vertices in a graph whose vertex type is `Fin n`. -/
def matchedCount {n : Nat} {G : Graph (Fin n)} (M : Matching G) : Nat :=
  (List.finRange n).countP (fun v => (M.mate v).isSome)

/-- Every matching on the finite vertex type `Fin n` saturates an even number of vertices. -/
theorem matchedCount_even {n : Nat} {G : Graph (Fin n)} (M : Matching G) :
    M.matchedCount % 2 = 0 :=
  matched_count_even_list M _ (List.nodup_finRange n)
    (fun _ _ v _ => List.mem_finRange v)

/-- Each undirected matching edge has two endpoints. -/
def cardinality {n : Nat} {G : Graph (Fin n)} (M : Matching G) : Nat :=
  M.matchedCount / 2

/-- The cardinality definition loses no remainder. -/
theorem twice_cardinality {n : Nat} {G : Graph (Fin n)} (M : Matching G) :
    2 * M.cardinality = M.matchedCount := by
  have h := Nat.mod_add_div M.matchedCount 2
  rw [M.matchedCount_even, Nat.zero_add] at h
  exact h
end Matching

namespace AltPath
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

/-- An augmentation saturates exactly two additional vertices. -/
theorem augment_matchedCount (p : AltPath M) (hp : p.Augmenting) :
    (p.augment hp).matchedCount = M.matchedCount + 2 := by
  have h := p.augment_matched_count_list hp (List.finRange n)
  have hf := (List.nodup_finRange n).count_of_mem (List.mem_finRange p.first)
  have hl := (List.nodup_finRange n).count_of_mem (List.mem_finRange p.last)
  simpa only [hf, hl, Nat.add_assoc, Matching.matchedCount] using h

/-- Exact cardinality gain of the executable path flip. -/
theorem augment_cardinality (p : AltPath M) (hp : p.Augmenting) :
    (p.augment hp).cardinality = M.cardinality + 1 := by
  unfold Matching.cardinality
  rw [p.augment_matchedCount hp]
  exact Nat.add_div_right _ (by decide)

end AltPath
end MaximumMatching

end Augmentation

section Phase

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

end Phase

section Family

/-! Sequential augmentation of a supplied finite, vertex-disjoint family.
Finding a maximal family of shortest paths remains the MV search obligation. -/
namespace MaximumMatching

structure AugmentingFamily {V : Type} {G : Graph V} (M : Matching G) where
  count : Nat
  path : Fin count → AltPath M
  augmenting : ∀ i, (path i).Augmenting
  disjoint : ∀ i j, i ≠ j → (path i).Disjoint (path j)

namespace AugmentingFamily
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

/-- Flip the first path and transport every remaining disjoint path. -/
def tailAfterFirst (f : AugmentingFamily M) (h : 0 < f.count) :
    AugmentingFamily ((f.path ⟨0, h⟩).augment (f.augmenting ⟨0, h⟩)) where
  count := f.count - 1
  path i := (f.path ⟨0, h⟩).rebase (f.augmenting ⟨0, h⟩)
    (f.path ⟨i.val + 1, by omega⟩)
    (f.disjoint ⟨0, h⟩ ⟨i.val + 1, by omega⟩ (by intro he; have := congrArg Fin.val he; simp at this))
  augmenting i := AltPath.rebase_augmenting _ _ _ (f.augmenting _) _
  disjoint := by
    intro i j hij
    change (f.path ⟨i.val + 1, by omega⟩).Disjoint (f.path ⟨j.val + 1, by omega⟩)
    apply f.disjoint
    intro he
    apply hij
    apply Fin.ext
    have hv : i.val + 1 = j.val + 1 := congrArg Fin.val he
    omega

/-- Execute all supplied flips; recursion consumes one path each time. -/
def run {M : Matching G} (f : AugmentingFamily M) : Matching G :=
  if h : f.count = 0 then M else (f.tailAfterFirst (by omega)).run
termination_by f.count
decreasing_by
  dsimp [tailAfterFirst]
  omega

end AugmentingFamily

namespace AugmentingFamily
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

/-- The exact gain is the number of input paths, without a correctness oracle. -/
theorem run_cardinality {M : Matching G} (f : AugmentingFamily M) :
    f.run.cardinality = M.cardinality + f.count := by
  rw [run]
  split
  next h => simp [h]
  next h =>
    rw [run_cardinality, AltPath.augment_cardinality]
    change M.cardinality + 1 + (f.count - 1) = M.cardinality + f.count
    omega
termination_by f.count
decreasing_by
  dsimp [tailAfterFirst]
  omega

end AugmentingFamily
end MaximumMatching

end Family
