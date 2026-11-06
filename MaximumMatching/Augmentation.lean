import MaximumMatching.PathLemmas

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
  · have hib : i.val - 1 < p.length := by omega
    have hpar : (i.val - 1) % 2 = 1 := by omega
    have hstep := (p.alternating ⟨i.val - 1, hib⟩).mpr hpar
    have he : i.val - 1 + 1 = i.val := by omega
    simp only [he] at hstep
    have hv' := M.symm hstep
    exact ⟨⟨i.val - 1, by omega⟩, M.mate_unique hv' hv⟩
  · have hib : i.val < p.length := by omega
    have hpar : i.val % 2 = 1 := by omega
    have hstep := (p.alternating ⟨i.val, hib⟩).mpr hpar
    exact ⟨⟨i.val + 1, by omega⟩, M.mate_unique hstep hv⟩

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

/-- This linear scan implements the mathematical path flip; no MV search or
linear-time path-expansion cost is asserted here. -/
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

/-- Saturated-vertex count is even, with no finiteness or matching obligation assumed. -/
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
