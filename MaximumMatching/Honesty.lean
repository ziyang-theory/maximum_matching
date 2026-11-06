import MaximumMatching.Levels

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
