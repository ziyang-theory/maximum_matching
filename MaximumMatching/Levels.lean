import MaximumMatching.PathLemmas

/-! Semantic levels of the source paper, Definitions 3.2 and 3.6.
`none` denotes infinity. The definitions use mathematical choice and are specifications,
not the operational MIN/MAX level computation. -/
namespace MaximumMatching

private theorem exists_least (P : Nat → Prop) (h : ∃ k, P k) :
    ∃ k, P k ∧ ∀ l, P l → k ≤ l := by
  classical
  obtain ⟨k, hk⟩ := h
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hs : ∃ l, l < k ∧ P l
    · obtain ⟨l, hl, hp⟩ := hs
      exact ih l hl hp
    · refine ⟨k, hk, ?_⟩
      intro l hl
      exact Nat.le_of_not_lt (fun hlt => hs ⟨l, hlt, hl⟩)

variable {V : Type} {G : Graph V}

/-- Existence of a simple alternating path of a prescribed parity and edge length. -/
def HasPathLength (M : Matching G) (parity : Nat) (v : V) (k : Nat) : Prop :=
  ∃ p : AltPath M, p.last = v ∧ p.length = k ∧ k % 2 = parity

/-- Minimality is specified independently of MIN and MAX. -/
def IsShortest (M : Matching G) (parity : Nat) (v : V) (k : Nat) : Prop :=
  HasPathLength M parity v k ∧ ∀ l, HasPathLength M parity v l → k ≤ l

private theorem shortest_exists (M : Matching G) (parity : Nat) (v : V)
    (h : ∃ k, HasPathLength M parity v k) : ∃ k, IsShortest M parity v k :=
  exists_least _ h

/-- The least path length of the specified parity, or infinity when no path exists. -/
noncomputable def level (M : Matching G) (parity : Nat) (v : V) : Option Nat :=
  by
    classical
    exact if h : ∃ k, IsShortest M parity v k then some (Classical.choose h) else none

theorem level_eq_some_iff (M : Matching G) (parity : Nat) (v : V) (k : Nat) :
    level M parity v = some k ↔ IsShortest M parity v k := by
  classical
  unfold level
  split
  · rename_i h
    have hs := Classical.choose_spec h
    constructor
    · intro he
      have he' := Option.some.inj he
      exact he' ▸ hs
    · intro hk
      have h1 := hs.2 k hk.1
      have h2 := hk.2 (Classical.choose h) hs.1
      have he : Classical.choose h = k := by omega
      exact congrArg some he
  · rename_i h
    constructor
    · intro he; contradiction
    · intro hk; exact False.elim (h ⟨k, hk⟩)

theorem level_eq_none_iff (M : Matching G) (parity : Nat) (v : V) :
    level M parity v = none ↔ ¬ ∃ k, HasPathLength M parity v k := by
  classical
  unfold level
  split
  · rename_i h
    constructor
    · intro he; contradiction
    · intro hn
      obtain ⟨k, hk⟩ := h
      exact False.elim (hn ⟨k, hk.1⟩)
  · rename_i h
    constructor
    · intro _ hp
      exact h (shortest_exists M parity v hp)
    · intro _; rfl

noncomputable abbrev evenlevel (M : Matching G) (v : V) : Option Nat := level M 0 v
noncomputable abbrev oddlevel (M : Matching G) (v : V) : Option Nat := level M 1 v

/-- A finite parity level has exactly its declared parity. -/
theorem level_parity (M : Matching G) (parity : Nat) (v : V) (k : Nat)
    (h : level M parity v = some k) : k % 2 = parity := by
  obtain ⟨_, _, _, hp⟩ := ((level_eq_some_iff M parity v k).1 h).1
  exact hp

/-- The even level is zero exactly at free vertices (Definition 3.2). -/
theorem evenlevel_zero_iff_free (M : Matching G) (v : V) :
    evenlevel M v = some 0 ↔ M.Free v := by
  rw [level_eq_some_iff]
  constructor
  · rintro ⟨⟨p, hp, hlen, _⟩, _⟩
    have hi : (⟨0, by omega⟩ : Fin (p.length + 1)) = ⟨p.length, by omega⟩ :=
      Fin.ext hlen.symm
    have hf := p.start_free
    rw [hi] at hf
    change M.Free p.last at hf
    rwa [hp] at hf
  · intro hf
    refine ⟨⟨AltPath.trivial M v hf, rfl, rfl, rfl⟩, ?_⟩
    intro l _
    omega

namespace AltPath
variable {M : Matching G}

/-- Every nontrivial even path ends with its terminal vertex's matched edge. -/
theorem even_last_mate (p : AltPath M) (heven : p.length % 2 = 0)
    (hpos : 0 < p.length) :
    M.mate p.last = some (p.vertex ⟨p.length - 1, by omega⟩) :=
  p.mate_previous p.length (by omega) hpos heven

/-- An even path to a matched vertex cannot be the zero-length path. -/
theorem even_matched_pos (p : AltPath M) {u : V} (hu : M.mate p.last = some u) :
    0 < p.length := by
  by_cases h : 0 < p.length
  · exact h
  have he : p.length = 0 := by omega
  have hf : p.first = p.last := by
    unfold first last
    congr 1
    exact Fin.ext (by simpa using he.symm)
  have hfree : M.mate p.first = none := p.start_free
  rw [hf, hu] at hfree
  contradiction

end AltPath

/-- The path correspondence underlying Lemma 5.2, including vertex simplicity. -/
theorem matched_path_length_iff (M : Matching G) {u v : V}
    (hm : M.mate u = some v) (k : Nat) :
    HasPathLength M 0 v (k + 1) ↔ HasPathLength M 1 u k := by
  constructor
  · rintro ⟨p, hp, hlen, hpar⟩
    have heven : p.length % 2 = 0 := by omega
    have hpos : 0 < p.length := by omega
    have hv : M.mate p.last = some u := by rw [hp]; exact M.symm hm
    have hprev := p.even_last_mate heven hpos
    have hend : p.vertex ⟨p.length - 1, by omega⟩ = u := M.mate_unique hprev hv
    refine ⟨p.take k (by omega), ?_, rfl, by omega⟩
    simp only [AltPath.take_last]
    have he : k = p.length - 1 := by omega
    subst k
    exact hend
  · rintro ⟨p, hp, hlen, hpar⟩
    have hm' : M.mate p.last = some v := by rw [hp]; exact hm
    have hodd : p.length % 2 = 1 := by omega
    refine ⟨p.appendMatched hodd hm', by simp, ?_, by omega⟩
    simp only [AltPath.appendMatched_length, hlen]

private theorem no_zero_even_path_to_matched (M : Matching G) {u v : V}
    (hm : M.mate u = some v) : ¬ HasPathLength M 0 v 0 := by
  rintro ⟨p, hp, hlen, _⟩
  have hv : M.mate p.last = some u := by rw [hp]; exact M.symm hm
  have hpos := p.even_matched_pos hv
  omega

theorem matched_shortest_iff (M : Matching G) {u v : V}
    (hm : M.mate u = some v) (k : Nat) :
    IsShortest M 0 v (k + 1) ↔ IsShortest M 1 u k := by
  constructor
  · intro hk
    refine ⟨(matched_path_length_iff M hm k).1 hk.1, ?_⟩
    intro l hl
    have hh := hk.2 (l + 1) ((matched_path_length_iff M hm l).2 hl)
    omega
  · intro hk
    refine ⟨(matched_path_length_iff M hm k).2 hk.1, ?_⟩
    intro l hl
    cases l with
    | zero => exact False.elim (no_zero_even_path_to_matched M hm hl)
    | succ l =>
      have hh := hk.2 l ((matched_path_length_iff M hm l).1 hl)
      omega

/-- Lemma 5.2's first equality. `Option.map` adds one and preserves infinity. -/
theorem evenlevel_matched (M : Matching G) {u v : V} (hm : M.mate u = some v) :
    evenlevel M v = (oddlevel M u).map (· + 1) := by
  cases ho : oddlevel M u with
  | none =>
    have hn := (level_eq_none_iff M 1 u).1 ho
    have hv : evenlevel M v = none := (level_eq_none_iff M 0 v).2 (by
      rintro ⟨k, hk⟩
      cases k with
      | zero => exact no_zero_even_path_to_matched M hm hk
      | succ k => exact hn ⟨k, (matched_path_length_iff M hm k).1 hk⟩)
    simpa using hv
  | some k =>
    have hk := (level_eq_some_iff M 1 u k).1 ho
    have hv := (level_eq_some_iff M 0 v (k + 1)).2
      ((matched_shortest_iff M hm k).2 hk)
    simpa using hv

/-- Addition on natural lengths extended by infinity (`none`). -/
def levelAdd : Option Nat → Option Nat → Option Nat
  | some a, some b => some (a + b)
  | _, _ => none

/-- Definition 3.6: vertex tenacity. -/
noncomputable def tenacity (M : Matching G) (v : V) : Option Nat :=
  levelAdd (evenlevel M v) (oddlevel M v)

/-- Definition 3.6: tenacity of a matched edge (the matched-edge branch). -/
noncomputable def matchedEdgeTenacity (M : Matching G) (u v : V) : Option Nat :=
  (levelAdd (oddlevel M u) (oddlevel M v)).map (· + 1)

/-- Lemma 5.2, including the cases where one or both levels are infinite. -/
theorem matched_tenacity (M : Matching G) {u v : V} (hm : M.mate u = some v) :
    tenacity M u = tenacity M v ∧ tenacity M v = matchedEdgeTenacity M u v := by
  have hu := evenlevel_matched M (M.symm hm)
  have hv := evenlevel_matched M hm
  unfold tenacity matchedEdgeTenacity
  rw [hu, hv]
  cases ho : oddlevel M u <;> cases hv' : oddlevel M v <;>
    simp [levelAdd, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]

/-- Every finite vertex tenacity is odd. -/
theorem tenacity_odd (M : Matching G) (v : V) (t : Nat)
    (h : tenacity M v = some t) : t % 2 = 1 := by
  unfold tenacity at h
  cases he : evenlevel M v with
  | none => simp [he, levelAdd] at h
  | some a =>
    cases ho : oddlevel M v with
    | none => simp [he, ho, levelAdd] at h
    | some b =>
      have ha := level_parity M 0 v a he
      have hb := level_parity M 1 v b ho
      have hab : a + b = t := by simpa [he, ho, levelAdd] using h
      omega

end MaximumMatching
