import MaximumMatching.Foundations

section Levels

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

end Levels

section Honesty

/-! Prefix minimality and path splicing for the limited BFS-honesty argument.
These declarations do not yet establish Theorem 5.3 of the source paper. -/
namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Definition 5.1: the prefix ending at index `i` is shortest among paths of its parity. -/
def BFSHonest (p : AltPath M) (i : Fin (p.length + 1)) : Prop :=
  IsShortest M (i.val % 2) (p.vertex i) i.val

/-- A path is shortest among all free-rooted alternating paths of its own parity. -/
def Shortest (p : AltPath M) : Prop :=
  IsShortest M (p.length % 2) p.last p.length

theorem prefix_witness (p : AltPath M) (i : Fin (p.length + 1)) :
    HasPathLength M (i.val % 2) (p.vertex i) i.val :=
  ⟨p.take i.val (by omega), rfl, rfl, rfl⟩

theorem honest_iff_level (p : AltPath M) (i : Fin (p.length + 1)) :
    p.BFSHonest i ↔ level M (i.val % 2) (p.vertex i) = some i.val :=
  (level_eq_some_iff M _ _ _).symm

/-- Prefixes always give upper bounds for the corresponding semantic levels. -/
theorem prefix_level_bound (p : AltPath M) (i : Fin (p.length + 1)) :
    ∃ k, level M (i.val % 2) (p.vertex i) = some k ∧ k ≤ i.val := by
  cases he : level M (i.val % 2) (p.vertex i) with
  | none =>
    have hn := (level_eq_none_iff M _ _).1 he
    exact False.elim (hn ⟨i.val, p.prefix_witness i⟩)
  | some k =>
    exact ⟨k, rfl, ((level_eq_some_iff M _ _ _).1 he).2 _ (p.prefix_witness i)⟩

/-- The replacement path does not meet the strict suffix being retained. -/
def SuffixDisjoint (q p : AltPath M) (k : Nat) : Prop :=
  ∀ (i : Fin (q.length + 1)) (j : Fin (p.length + 1)),
    k < j.val → q.vertex i ≠ p.vertex j

/-- Replace a prefix by a same-parity path with the same endpoint, provided its
vertices avoid the retained suffix. The fresh start may be a different free vertex. -/
def splice (q p : AltPath M) (k : Nat) (hk : k ≤ p.length)
    (hjoin : q.last = p.vertex ⟨k, by omega⟩)
    (hpar : q.length % 2 = k % 2) (hdisj : q.SuffixDisjoint p k) : AltPath M where
  length := q.length + (p.length - k)
  vertex := fun i => if h : i.val ≤ q.length then q.vertex ⟨i.val, by omega⟩
    else p.vertex ⟨i.val - q.length + k, by omega⟩
  injective := by
    intro i j he
    split at he <;> split at he
    · have hi := q.injective _ _ he
      apply Fin.ext
      exact congrArg (fun x : Fin (q.length + 1) => x.val) hi
    · exact False.elim (hdisj _ _ (by change k < j.val - q.length + k; omega) he)
    · exact False.elim (hdisj _ _ (by change k < i.val - q.length + k; omega) he.symm)
    · have hi := p.injective _ _ he
      have heq : i.val - q.length + k = j.val - q.length + k :=
        congrArg (fun x : Fin (p.length + 1) => x.val) hi
      apply Fin.ext
      omega
  adjacent := by
    intro i
    by_cases hi : i.val < q.length
    · simpa only [dite_eq_left (show i.val ≤ q.length by omega),
        dite_eq_left (show i.val + 1 ≤ q.length by omega)] using q.adjacent ⟨i.val, hi⟩
    · by_cases heq : i.val = q.length
      · simp only [heq, Nat.le_refl, dite_true,
          show ¬q.length + 1 ≤ q.length by omega, dite_false]
        change G.Adj q.last _
        rw [hjoin]
        have he : q.length + 1 - q.length + k = k + 1 := by omega
        simpa only [he] using p.adjacent ⟨k, by omega⟩
      · simp only [dite_eq_right (show ¬i.val ≤ q.length by omega),
          dite_eq_right (show ¬i.val + 1 ≤ q.length by omega)]
        have he : i.val + 1 - q.length + k = (i.val - q.length + k) + 1 := by omega
        simpa only [he] using p.adjacent ⟨i.val - q.length + k, by omega⟩
  start_free := by simpa using q.start_free
  alternating := by
    intro i
    by_cases hi : i.val < q.length
    · simpa only [dite_eq_left (show i.val ≤ q.length by omega),
        dite_eq_left (show i.val + 1 ≤ q.length by omega)] using q.alternating ⟨i.val, hi⟩
    · by_cases heq : i.val = q.length
      · simp only [heq, Nat.le_refl, dite_true,
          show ¬q.length + 1 ≤ q.length by omega, dite_false]
        change (M.mate q.last = some _) ↔ q.length % 2 = 1
        rw [hjoin, hpar]
        have he : q.length + 1 - q.length + k = k + 1 := by omega
        simpa only [he] using p.alternating ⟨k, by omega⟩
      · simp only [dite_eq_right (show ¬i.val ≤ q.length by omega),
          dite_eq_right (show ¬i.val + 1 ≤ q.length by omega)]
        have he : i.val + 1 - q.length + k = (i.val - q.length + k) + 1 := by omega
        have hp : (i.val - q.length + k) % 2 = i.val % 2 := by omega
        simpa only [he, hp] using p.alternating ⟨i.val - q.length + k, by omega⟩

@[simp] theorem splice_length (q p : AltPath M) (k : Nat) (hk : k ≤ p.length)
    (hjoin : q.last = p.vertex ⟨k, by omega⟩)
    (hpar : q.length % 2 = k % 2) (hdisj : q.SuffixDisjoint p k) :
    (q.splice p k hk hjoin hpar hdisj).length = q.length + (p.length - k) := rfl

@[simp] theorem splice_last (q p : AltPath M) (k : Nat) (hk : k ≤ p.length)
    (hjoin : q.last = p.vertex ⟨k, by omega⟩)
    (hpar : q.length % 2 = k % 2) (hdisj : q.SuffixDisjoint p k) :
    (q.splice p k hk hjoin hpar hdisj).last = p.last := by
  simp only [last, splice]
  split
  · rename_i h
    have hlen : k = p.length := by omega
    have hnew : q.length + (p.length - k) = q.length := by omega
    simp only [hnew]
    exact hlen ▸ hjoin
  · have he : q.length + (p.length - k) - q.length + k = p.length := by omega
    congr 1
    exact Fin.ext he

theorem splice_parity (q p : AltPath M) (k : Nat) (hk : k ≤ p.length)
    (hjoin : q.last = p.vertex ⟨k, by omega⟩)
    (hpar : q.length % 2 = k % 2) (hdisj : q.SuffixDisjoint p k) :
    (q.splice p k hk hjoin hpar hdisj).length % 2 = p.length % 2 := by
  simp only [splice_length]
  omega

/-- A shortest path cannot have a shorter same-parity replacement prefix disjoint
from the retained suffix. This is the elementary splice contradiction in Theorem 5.3. -/
theorem no_shorter_disjoint_prefix (p : AltPath M) (hp : p.Shortest)
    (k : Nat) (hk : k ≤ p.length) (q : AltPath M)
    (hjoin : q.last = p.vertex ⟨k, by omega⟩)
    (hpar : q.length % 2 = k % 2) (hdisj : q.SuffixDisjoint p k) : k ≤ q.length := by
  let r := q.splice p k hk hjoin hpar hdisj
  have hr : HasPathLength M (p.length % 2) p.last r.length :=
    ⟨r, splice_last _ _ _ _ _ _ _, rfl, splice_parity _ _ _ _ _ _ _⟩
  have hh := hp.2 r.length hr
  change p.length ≤ q.length + (p.length - k) at hh
  omega

/-- If a shorter same-parity prefix exists, it must hit the strict suffix.
This asserts an actual shared vertex, not merely failed splice construction. -/
theorem shorter_prefix_intersects (p : AltPath M) (hp : p.Shortest)
    (k : Nat) (hk : k ≤ p.length) (q : AltPath M)
    (hjoin : q.last = p.vertex ⟨k, by omega⟩)
    (hpar : q.length % 2 = k % 2) (hlt : q.length < k) :
    ∃ (i : Fin (q.length + 1)) (j : Fin (p.length + 1)),
      k < j.val ∧ q.vertex i = p.vertex j := by
  classical
  apply Classical.byContradiction
  intro hn
  have hd : q.SuffixDisjoint p k := by
    intro i j hj he
    exact hn ⟨i, j, hj, he⟩
  have hh := p.no_shorter_disjoint_prefix hp k hk q hjoin hpar hd
  omega

/-- Reverse an augmenting path. Odd length makes the reversed first edge unmatched. -/
def reverseAugmenting (p : AltPath M) (ha : p.Augmenting) : AltPath M where
  length := p.length
  vertex := fun i => p.vertex ⟨p.length - i.val, by omega⟩
  injective := by
    intro i j he
    have hh := p.injective _ _ he
    have hv : p.length - i.val = p.length - j.val :=
      congrArg (fun x : Fin (p.length + 1) => x.val) hh
    apply Fin.ext
    omega
  adjacent := by
    intro i
    have hh := G.symm (p.adjacent ⟨p.length - i.val - 1, by omega⟩)
    have he : p.length - i.val - 1 + 1 = p.length - i.val := by omega
    have he' : p.length - (i.val + 1) = p.length - i.val - 1 := by omega
    simpa only [he, he'] using hh
  start_free := by
    change M.Free (p.vertex ⟨p.length - 0, _⟩)
    simpa only [Nat.sub_zero] using (show M.Free (p.vertex ⟨p.length, by omega⟩) from ha.2)
  alternating := by
    intro i
    have hpar : (p.length - i.val - 1) % 2 = i.val % 2 := by
      have hh := ha.1
      omega
    have he : p.length - i.val - 1 + 1 = p.length - i.val := by omega
    have he' : p.length - (i.val + 1) = p.length - i.val - 1 := by omega
    have hh := p.alternating ⟨p.length - i.val - 1, by omega⟩
    rw [hpar] at hh
    constructor
    · intro hm
      apply hh.1
      have hm' := M.symm hm
      simpa only [he, he'] using hm'
    · intro hp
      have hm := M.symm (hh.2 hp)
      simpa only [he, he'] using hm

@[simp] theorem reverseAugmenting_length (p : AltPath M) (ha : p.Augmenting) :
    (p.reverseAugmenting ha).length = p.length := rfl

/-- Both parity levels of a vertex on an augmenting path are finite. Its tenacity
is no larger than that path's length; this statement needs no shortest-path premise. -/
theorem augmenting_tenacity_bound (p : AltPath M) (ha : p.Augmenting)
    (i : Fin (p.length + 1)) :
    ∃ t, tenacity M (p.vertex i) = some t ∧ t ≤ p.length := by
  let r := p.reverseAugmenting ha
  let j : Fin (r.length + 1) := ⟨p.length - i.val, by simp only [r, reverseAugmenting_length]; omega⟩
  have hj : r.vertex j = p.vertex i := by
    change p.vertex ⟨p.length - (p.length - i.val), _⟩ = p.vertex i
    congr 1
    apply Fin.ext
    simp only
    omega
  obtain ⟨a, ha', hab⟩ := p.prefix_level_bound i
  obtain ⟨b, hb', hbb⟩ := r.prefix_level_bound j
  rw [hj] at hb'
  have hbb' : b ≤ p.length - i.val := hbb
  have hpar := ha.1
  by_cases hi : i.val % 2 = 0
  · have hjpar : j.val % 2 = 1 := by change (p.length - i.val) % 2 = 1; omega
    rw [hi] at ha'
    rw [hjpar] at hb'
    refine ⟨a + b, ?_, by omega⟩
    simp only [tenacity, evenlevel, oddlevel, ha', hb', levelAdd]
  · have hi' : i.val % 2 = 1 := by omega
    have hjpar : j.val % 2 = 0 := by change (p.length - i.val) % 2 = 0; omega
    rw [hi'] at ha'
    rw [hjpar] at hb'
    refine ⟨b + a, ?_, by omega⟩
    simp only [tenacity, evenlevel, oddlevel, ha', hb', levelAdd]

/-- Limited BFS-honesty on augmenting paths. At a vertex with tenacity at least the
path length, both prefix upper bounds must be equalities. -/
theorem honest_on_augmenting_of_tenacity_ge (p : AltPath M) (ha : p.Augmenting)
    (i : Fin (p.length + 1)) (t : Nat)
    (ht : tenacity M (p.vertex i) = some t) (hge : p.length ≤ t) : p.BFSHonest i := by
  let r := p.reverseAugmenting ha
  let j : Fin (r.length + 1) := ⟨p.length - i.val, by simp only [r, reverseAugmenting_length]; omega⟩
  have hj : r.vertex j = p.vertex i := by
    change p.vertex ⟨p.length - (p.length - i.val), _⟩ = p.vertex i
    congr 1
    apply Fin.ext
    simp only
    omega
  obtain ⟨a, ha', hab⟩ := p.prefix_level_bound i
  obtain ⟨b, hb', hbb⟩ := r.prefix_level_bound j
  rw [hj] at hb'
  have hbb' : b ≤ p.length - i.val := hbb
  have hpar := ha.1
  apply (p.honest_iff_level i).2
  by_cases hi : i.val % 2 = 0
  · have hjpar : j.val % 2 = 1 := by change (p.length - i.val) % 2 = 1; omega
    rw [hi] at ha' ⊢
    rw [hjpar] at hb'
    have hsum : a + b = t := by
      simpa only [tenacity, evenlevel, oddlevel, ha', hb', levelAdd, Option.some.injEq] using ht
    have he : a = i.val := by omega
    exact he ▸ ha'
  · have hi' : i.val % 2 = 1 := by omega
    have hjpar : j.val % 2 = 0 := by change (p.length - i.val) % 2 = 0; omega
    rw [hi'] at ha' ⊢
    rw [hjpar] at hb'
    have hsum : b + a = t := by
      simpa only [tenacity, evenlevel, oddlevel, ha', hb', levelAdd, Option.some.injEq] using ht
    have he : a = i.val := by omega
    exact he ▸ ha'

end AltPath
end MaximumMatching

end Honesty
