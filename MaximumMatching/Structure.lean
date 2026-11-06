import MaximumMatching.Levels

section Splice

namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The replacement path avoids the segment traversed in reverse. -/
def ReverseDisjoint (q p : AltPath M) (k j : Nat) : Prop :=
  ∀ (a : Fin (q.length + 1)) (b : Fin (p.length + 1)),
    k ≤ b.val → b.val < j → q.vertex a ≠ p.vertex b

/-- Join an odd-length path to an even-indexed vertex, then follow a segment backward. -/
def spliceReverse (q p : AltPath M) (k j : Nat) (hkj : k ≤ j) (hj : j ≤ p.length)
    (hjoin : q.last = p.vertex ⟨j, by omega⟩)
    (hqo : q.length % 2 = 1) (hje : j % 2 = 0)
    (hdisj : q.ReverseDisjoint p k j) : AltPath M where
  length := q.length + (j - k)
  vertex := fun a => if h : a.val ≤ q.length then q.vertex ⟨a.val, by omega⟩
    else p.vertex ⟨j - (a.val - q.length), by omega⟩
  injective := by
    intro a b he
    split at he <;> split at he
    · have hh := q.injective _ _ he
      apply Fin.ext
      exact congrArg (fun x : Fin (q.length + 1) => x.val) hh
    · exact False.elim (hdisj _ _ (by change k ≤ j - (b.val - q.length); omega)
        (by change j - (b.val - q.length) < j; omega) he)
    · exact False.elim (hdisj _ _ (by change k ≤ j - (a.val - q.length); omega)
        (by change j - (a.val - q.length) < j; omega) he.symm)
    · have hh := p.injective _ _ he
      have heq : j - (a.val - q.length) = j - (b.val - q.length) :=
        congrArg (fun x : Fin (p.length + 1) => x.val) hh
      apply Fin.ext
      omega
  adjacent := by
    intro a
    by_cases ha : a.val < q.length
    · simpa only [dite_eq_left (show a.val ≤ q.length by omega),
        dite_eq_left (show a.val + 1 ≤ q.length by omega)] using q.adjacent ⟨a.val, ha⟩
    · by_cases heq : a.val = q.length
      · simp only [heq, Nat.le_refl, dite_true,
          show ¬q.length + 1 ≤ q.length by omega, dite_false]
        change G.Adj q.last _
        rw [hjoin]
        have he : j - (q.length + 1 - q.length) = j - 1 := by omega
        have he' : j - 1 + 1 = j := by omega
        simpa only [he, he'] using G.symm (p.adjacent ⟨j - 1, by omega⟩)
      · simp only [dite_eq_right (show ¬a.val ≤ q.length by omega),
          dite_eq_right (show ¬a.val + 1 ≤ q.length by omega)]
        have he : j - (a.val + 1 - q.length) + 1 = j - (a.val - q.length) := by omega
        simpa only [he] using G.symm (p.adjacent ⟨j - (a.val + 1 - q.length), by omega⟩)
  start_free := by simpa using q.start_free
  alternating := by
    intro a
    by_cases ha : a.val < q.length
    · simpa only [dite_eq_left (show a.val ≤ q.length by omega),
        dite_eq_left (show a.val + 1 ≤ q.length by omega)] using q.alternating ⟨a.val, ha⟩
    · by_cases heq : a.val = q.length
      · simp only [heq, Nat.le_refl, dite_true,
          show ¬q.length + 1 ≤ q.length by omega, dite_false]
        change (M.mate q.last = some _) ↔ q.length % 2 = 1
        rw [hjoin]
        have hm := p.mate_previous j hj (by omega) hje
        have he : j - (q.length + 1 - q.length) = j - 1 := by omega
        constructor
        · intro _; exact hqo
        · intro _; simpa only [he] using hm
      · simp only [dite_eq_right (show ¬a.val ≤ q.length by omega),
          dite_eq_right (show ¬a.val + 1 ≤ q.length by omega)]
        have he : j - (a.val + 1 - q.length) + 1 = j - (a.val - q.length) := by omega
        have hpar : (j - (a.val + 1 - q.length)) % 2 = a.val % 2 := by omega
        have hh := p.alternating ⟨j - (a.val + 1 - q.length), by omega⟩
        rw [hpar] at hh
        constructor
        · intro hm
          apply hh.1
          simpa only [he] using M.symm hm
        · intro hp
          simpa only [he] using M.symm (hh.2 hp)

@[simp] theorem spliceReverse_length (q p : AltPath M) (k j : Nat)
    (hkj : k ≤ j) (hj : j ≤ p.length) (hjoin : q.last = p.vertex ⟨j, by omega⟩)
    (hqo : q.length % 2 = 1) (hje : j % 2 = 0) (hdisj : q.ReverseDisjoint p k j) :
    (q.spliceReverse p k j hkj hj hjoin hqo hje hdisj).length = q.length + (j - k) := rfl

@[simp] theorem spliceReverse_last (q p : AltPath M) (k j : Nat)
    (hkj : k ≤ j) (hj : j ≤ p.length) (hjoin : q.last = p.vertex ⟨j, by omega⟩)
    (hqo : q.length % 2 = 1) (hje : j % 2 = 0) (hdisj : q.ReverseDisjoint p k j) :
    (q.spliceReverse p k j hkj hj hjoin hqo hje hdisj).last = p.vertex ⟨k, by omega⟩ := by
  simp only [last, spliceReverse]
  split
  · have hlen : k = j := by omega
    have hnew : q.length + (j - k) = q.length := by omega
    simp only [hnew]
    exact hlen ▸ hjoin
  · have he : j - (q.length + (j - k) - q.length) = k := by omega
    congr 1
    exact Fin.ext he

/-- A first intersection of `q` with the suffix of `p` beginning at `cut`. -/
structure FirstHit (q p : AltPath M) (cut : Nat) where
  qi : Fin (q.length + 1)
  pi : Fin (p.length + 1)
  in_suffix : cut ≤ pi.val
  hit : q.vertex qi = p.vertex pi
  first : ∀ (a : Fin (q.length + 1)) (b : Fin (p.length + 1)),
    a.val < qi.val → cut ≤ b.val → q.vertex a ≠ p.vertex b

private theorem least_hit (P : Nat → Prop) (n : Nat) (hn : P n) :
    ∃ m, P m ∧ ∀ l, l < m → ¬P l := by
  classical
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hs : ∃ m, m < n ∧ P m
    · obtain ⟨m, hm, hp⟩ := hs
      exact ih m hm hp
    · refine ⟨n, hn, ?_⟩
      intro m hm hp
      exact hs ⟨m, hm, hp⟩

theorem firstHit_exists (q p : AltPath M) (cut : Nat)
    (h : ∃ (i : Fin (q.length + 1)) (j : Fin (p.length + 1)),
      cut ≤ j.val ∧ q.vertex i = p.vertex j) : Nonempty (FirstHit q p cut) := by
  classical
  let P (i : Nat) := ∃ (hi : i < q.length + 1) (j : Fin (p.length + 1)),
    cut ≤ j.val ∧ q.vertex ⟨i, hi⟩ = p.vertex j
  obtain ⟨i, j, hc, hh⟩ := h
  have hi : P i.val := ⟨i.isLt, j, hc, hh⟩
  obtain ⟨m, ⟨hm, j, hc, hh⟩, hmin⟩ := least_hit P i.val hi
  refine ⟨⟨⟨m, hm⟩, j, hc, hh, ?_⟩⟩
  intro a b ha hb he
  exact hmin a.val ha ⟨a.isLt, b, hb, he⟩

/-- In an even path, an odd-indexed suffix is a union of complete matched pairs. -/
theorem even_suffix_matched_closed (p : AltPath M) (he : p.length % 2 = 0)
    (cut : Nat) (hc : cut % 2 = 1) (j : Fin (p.length + 1)) (hj : cut ≤ j.val) :
    ∃ j' : Fin (p.length + 1), cut ≤ j'.val ∧ M.mate (p.vertex j) = some (p.vertex j') := by
  by_cases hje : j.val % 2 = 0
  · refine ⟨⟨j.val - 1, by omega⟩, ?_, ?_⟩
    · change cut ≤ j.val - 1
      omega
    · exact p.mate_previous j.val (by omega) (by omega) hje
  · refine ⟨⟨j.val + 1, by omega⟩, ?_, ?_⟩
    · change cut ≤ j.val + 1
      omega
    · exact p.mate_next j.val (by omega) (by omega)

/-- The first hit on a suffix consisting of matched pairs occurs at odd parity. -/
theorem FirstHit.odd {q p : AltPath M} {cut : Nat} (h : FirstHit q p cut)
    (he : p.length % 2 = 0) (hc : cut % 2 = 1) : h.qi.val % 2 = 1 := by
  obtain ⟨j, hj, hm⟩ := p.even_suffix_matched_closed he cut hc h.pi h.in_suffix
  have hq : M.mate (q.vertex h.qi) = some (p.vertex j) := by rw [h.hit]; exact hm
  by_cases hz : h.qi.val = 0
  · have hi : h.qi = ⟨0, by omega⟩ := Fin.ext hz
    rw [hi] at hq
    have hf := q.start_free
    unfold Matching.Free at hf
    rw [hf] at hq
    contradiction
  · by_cases heven : h.qi.val % 2 = 0
    · have hp := q.mate_previous h.qi.val (by omega) (by omega) heven
      have hv := M.mate_unique hp hq
      exact False.elim (h.first ⟨h.qi.val - 1, by omega⟩ j (by change h.qi.val - 1 < h.qi.val; omega) hj hv)
    · omega

/-- At a first hit, the prefix avoids every vertex strictly after the hit in `p`. -/
theorem FirstHit.forward_disjoint {q p : AltPath M} {cut : Nat} (h : FirstHit q p cut) :
    (q.take h.qi.val (by omega)).SuffixDisjoint p h.pi.val := by
  intro a b hb he
  change q.vertex ⟨a.val, _⟩ = p.vertex b at he
  have habound : a.val ≤ h.qi.val := by
    have ha := a.isLt
    change a.val < h.qi.val + 1 at ha
    omega
  by_cases ha : a.val < h.qi.val
  · exact h.first ⟨a.val, by omega⟩ b ha (by have := h.in_suffix; omega) he
  · have heq : a.val = h.qi.val := by omega
    have ha' : (⟨a.val, by omega⟩ : Fin (q.length + 1)) = h.qi := Fin.ext heq
    rw [ha', h.hit] at he
    have hi := p.injective _ _ he
    have hi' : h.pi.val = b.val := congrArg Fin.val hi
    omega

/-- At a first hit, the prefix avoids every earlier vertex in the suffix of `p`. -/
theorem FirstHit.reverse_disjoint {q p : AltPath M} {cut : Nat} (h : FirstHit q p cut)
    (k : Nat) (hk : cut ≤ k) :
    (q.take h.qi.val (by omega)).ReverseDisjoint p k h.pi.val := by
  intro a b hb hb' he
  change q.vertex ⟨a.val, _⟩ = p.vertex b at he
  have habound : a.val ≤ h.qi.val := by
    have ha := a.isLt
    change a.val < h.qi.val + 1 at ha
    omega
  by_cases ha : a.val < h.qi.val
  · exact h.first ⟨a.val, by omega⟩ b ha (by omega) he
  · have heq : a.val = h.qi.val := by omega
    have ha' : (⟨a.val, by omega⟩ : Fin (q.length + 1)) = h.qi := Fin.ext heq
    rw [ha', h.hit] at he
    have hi := p.injective _ _ he
    have hi' : h.pi.val = b.val := congrArg Fin.val hi
    omega

end AltPath
end MaximumMatching

end Splice

section Structure

/-! Semantic specification for the structural core of MV.
Source: Definitions 3.1, 3.3--3.9 and 6.1--6.4, pp.8--10 and 20--21.

These are mathematical definitions, independent of operational MIN/MAX state.
`BaseOnPath` does not assert that different shortest paths have the same base;
that path-independence assertion is proved separately in GeneralStructureInduction.
-/
namespace MaximumMatching

/-- Natural levels extended by a top element, represented as `none`. -/
def levelLE : Option Nat → Option Nat → Prop
  | _, none => True
  | none, some _ => False
  | some a, some b => a ≤ b

def levelLT : Option Nat → Option Nat → Prop
  | none, _ => False
  | some _, none => True
  | some a, some b => a < b

def levelMin : Option Nat → Option Nat → Option Nat
  | none, b => b
  | a, none => a
  | some a, some b => some (min a b)

def levelMax : Option Nat → Option Nat → Option Nat
  | some a, some b => some (max a b)
  | _, _ => none

variable {V : Type} {G : Graph V}

noncomputable def minlevel (M : Matching G) (v : V) : Option Nat :=
  levelMin (evenlevel M v) (oddlevel M v)

noncomputable def maxlevel (M : Matching G) (v : V) : Option Nat :=
  levelMax (evenlevel M v) (oddlevel M v)

noncomputable def Outer (M : Matching G) (v : V) : Prop :=
  levelLT (evenlevel M v) (oddlevel M v)

noncomputable def Inner (M : Matching G) (v : V) : Prop :=
  (∃ k, minlevel M v = some k) ∧ ¬ Outer M v

theorem minlevel_add_maxlevel (M : Matching G) (v : V) :
    levelAdd (minlevel M v) (maxlevel M v) = tenacity M v := by
  unfold minlevel maxlevel tenacity
  cases he : evenlevel M v <;> cases ho : oddlevel M v <;>
    simp only [levelMin, levelMax, levelAdd]
  next a b =>
    congr 1
    omega

noncomputable def edgeTenacity (M : Matching G) (u v : V) : Option Nat := by
  classical
  exact if M.mate u = some v then matchedEdgeTenacity M u v
    else (levelAdd (evenlevel M u) (evenlevel M v)).map (· + 1)

/-- Oriented predecessor; the underlying prop edge is undirected. -/
noncomputable def Predecessor (M : Matching G) (u v : V) : Prop :=
  ∃ p : AltPath M, p.last = v ∧ minlevel M v = some p.length ∧
    ∃ h : 0 < p.length, p.vertex ⟨p.length - 1, by omega⟩ = u

noncomputable def PropEdge (M : Matching G) (u v : V) : Prop :=
  Predecessor M u v ∨ Predecessor M v u

noncomputable def Bridge (M : Matching G) (u v : V) : Prop :=
  G.Adj u v ∧ ¬ PropEdge M u v

namespace AltPath
variable {M : Matching G}

def ContainsEdge (p : AltPath M) (u v : V) : Prop :=
  ∃ i : Fin p.length,
    (p.vertex ⟨i.val, by omega⟩ = u ∧ p.vertex ⟨i.val + 1, by omega⟩ = v) ∨
    (p.vertex ⟨i.val, by omega⟩ = v ∧ p.vertex ⟨i.val + 1, by omega⟩ = u)

theorem containsEdge_symm (p : AltPath M) (u v : V) :
    p.ContainsEdge u v ↔ p.ContainsEdge v u := by
  simp only [ContainsEdge, Or.comm]

/-- The last vertex on this path whose tenacity is greater than `t`.
The threshold is finite; comparisons explicitly include infinite tenacity. -/
noncomputable def BaseOnPath (p : AltPath M) (t : Nat) (b : V) : Prop :=
  ∃ i : Fin (p.length + 1), p.vertex i = b ∧ levelLT (some t) (tenacity M b) ∧
    ∀ j : Fin (p.length + 1), i.val < j.val →
      ¬ levelLT (some t) (tenacity M (p.vertex j))

/-- Lastness gives uniqueness on one path. It does not prove path independence. -/
theorem baseOnPath_unique (p : AltPath M) (t : Nat) (b c : V)
    (hb : p.BaseOnPath t b) (hc : p.BaseOnPath t c) : b = c := by
  obtain ⟨i, hi, hbt, hblast⟩ := hb
  obtain ⟨j, hj, hct, hclast⟩ := hc
  have hij : i.val = j.val := by
    by_cases h : i.val < j.val
    · exact False.elim (hblast j h (hj ▸ hct))
    · by_cases h' : j.val < i.val
      · exact False.elim (hclast i h' (hi ▸ hbt))
      · omega
  have he : i = j := Fin.ext hij
  exact hi.symm.trans ((congrArg p.vertex he).trans hj)
end AltPath

/-- `t ≤ l_m`, expressed without selecting a shortest path. If no augmenting
path exists, the universal condition is true, agreeing with `l_m = ∞`. -/
def AtMostShortestAugmenting (M : Matching G) (t : Nat) : Prop :=
  ∀ p : AltPath M, p.Augmenting → t ≤ p.length

/-- Definition 6.1. The existence clause expresses `t_m ≤ t`; the strict path
bound expresses `t < l_m`, including the case of no augmenting path. -/
noncomputable def EligibleTenacity (M : Matching G) (t : Nat) : Prop :=
  t % 2 = 1 ∧ (∃ v, levelLE (tenacity M v) (some t)) ∧
    ∀ p : AltPath M, p.Augmenting → t < p.length

/-- Definition 3.9, including the permitted bridge-tenacity range. -/
noncomputable def InSupport (M : Matching G) (u v w : V) : Prop :=
  Bridge M u v ∧ ∃ t : Nat, AtMostShortestAugmenting M t ∧
    edgeTenacity M u v = some t ∧ tenacity M w = some t ∧
    ∃ p : AltPath M, p.last = w ∧ maxlevel M w = some p.length ∧ p.ContainsEdge u v

/-- Every free vertex has tenacity above a strict lower bound on all augmenting
path lengths; this includes vertices with infinite odd level. -/
theorem free_tenacity_above (M : Matching G) (t : Nat) (f : V) (hf : M.Free f)
    (ht : ∀ p : AltPath M, p.Augmenting → t < p.length) :
    levelLT (some t) (tenacity M f) := by
  have he := (evenlevel_zero_iff_free M f).2 hf
  unfold tenacity
  rw [he]
  cases ho : oddlevel M f with
  | none => trivial
  | some k =>
    obtain ⟨q, hq, hlen, hpar⟩ := ((level_eq_some_iff M 1 f k).1 ho).1
    have ha : q.Augmenting := ⟨by omega, by rw [hq]; exact hf⟩
    have hb := ht q ha
    change t < 0 + k
    omega

private theorem exists_last_index (P : Nat → Prop) (k : Nat) (h : P 0) :
    ∃ i, i ≤ k ∧ P i ∧ ∀ j, j ≤ k → i < j → ¬ P j := by
  classical
  induction k with
  | zero => exact ⟨0, Nat.le_refl 0, h, by intros; omega⟩
  | succ k ih =>
    by_cases hk : P (k + 1)
    · exact ⟨k + 1, Nat.le_refl _, hk, by intros; omega⟩
    · obtain ⟨i, hi, hp, hlast⟩ := ih
      refine ⟨i, by omega, hp, ?_⟩
      intro j hj hij hpj
      by_cases he : j = k + 1
      · exact hk (he ▸ hpj)
      · exact hlast j (by omega) hij hpj

namespace AltPath
variable {M : Matching G}

/-- A finite path whose first vertex exceeds the threshold has a last such vertex. -/
theorem baseOnPath_exists (p : AltPath M) (t : Nat)
    (hfirst : levelLT (some t) (tenacity M p.first)) :
    ∃ b, p.BaseOnPath t b := by
  let P : Nat → Prop := fun i => ∃ hi : i ≤ p.length,
    levelLT (some t) (tenacity M (p.vertex ⟨i, by omega⟩))
  have hP0 : P 0 := ⟨by omega, hfirst⟩
  obtain ⟨i, hi, hPi, hlast⟩ := exists_last_index P p.length hP0
  obtain ⟨_, hhigh⟩ := hPi
  refine ⟨p.vertex ⟨i, by omega⟩, ⟨⟨i, by omega⟩, rfl, hhigh, ?_⟩⟩
  intro j hij hh
  exact hlast j.val (by omega) hij ⟨by omega, hh⟩

/-- Eligible tenacity guarantees existence on each path separately. Equality of
these bases across different shortest paths is still the structural core. -/
theorem baseOnPath_exists_of_eligible (p : AltPath M) (t : Nat)
    (ht : EligibleTenacity M t) : ∃ b, p.BaseOnPath t b :=
  p.baseOnPath_exists t (free_tenacity_above M t p.first p.start_free ht.2.2)
end AltPath

/-- The path-independence target for a vertex of finite eligible tenacity.
No theorem below assumes this predicate as an established property of MV. -/
noncomputable def HasUniqueBase (M : Matching G) (v : V) (t : Nat) : Prop :=
  ∃ b : V, (∀ p : AltPath M, p.last = v → p.Shortest → p.BaseOnPath t b) ∧
    ∀ c : V, (∀ p : AltPath M, p.last = v → p.Shortest → p.BaseOnPath t c) → c = b

end MaximumMatching

end Structure

section LimitedHonesty

namespace MaximumMatching

theorem levelLT_le {a b : Option Nat} (h : levelLT a b) : levelLE a b := by
  cases a <;> cases b <;> simp only [levelLT, levelLE] at h ⊢
  omega

namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A first hit strictly beyond a replacement path's target still permits reversal
all the way to that target: the target occurs only at the replacement path's end. -/
theorem FirstHit.reverse_disjoint_to_target {q p : AltPath M} {k : Nat}
    (h : FirstHit q p (k + 1)) (hk : k ≤ p.length)
    (hend : q.last = p.vertex ⟨k, by omega⟩) :
    (q.take h.qi.val (by omega)).ReverseDisjoint p k h.pi.val := by
  have hqi : h.qi.val < q.length := by
    by_cases hlt : h.qi.val < q.length
    · exact hlt
    · have he : h.qi = ⟨q.length, by omega⟩ := Fin.ext (by change h.qi.val = q.length; omega)
      have hh : p.vertex ⟨k, by omega⟩ = p.vertex h.pi := by
        have hhit := h.hit
        rw [he] at hhit
        exact hend.symm.trans hhit
      have hh' := p.injective _ _ hh
      have hv : k = h.pi.val := congrArg (fun x : Fin (p.length + 1) => x.val) hh'
      have := h.in_suffix
      omega
  intro a b hb hb' he
  have habound : a.val ≤ h.qi.val := by
    have ha := a.isLt
    change a.val < h.qi.val + 1 at ha
    omega
  change q.vertex ⟨a.val, _⟩ = p.vertex b at he
  by_cases hkb : k < b.val
  · exact h.reverse_disjoint (k + 1) (by omega) a b (by omega) hb' he
  · have hbk : b = ⟨k, by omega⟩ := Fin.ext (by change b.val = k; omega)
    rw [hbk, ← hend] at he
    have hh := q.injective ⟨a.val, by omega⟩ ⟨q.length, by omega⟩ he
    have hv : a.val = q.length := congrArg (fun x : Fin (q.length + 1) => x.val) hh
    omega

/-- Core first-intersection argument from Theorem 5.3: if an even vertex on a
shortest even path has a shorter even path, it has an odd path shorter than the
original path. This does not assume BFS-honesty of intermediate vertices. -/
theorem shorter_even_prefix_opposite (p : AltPath M) (hp : p.Shortest)
    (heven : p.length % 2 = 0) (k : Nat) (hk : k ≤ p.length) (hke : k % 2 = 0)
    (q : AltPath M) (hend : q.last = p.vertex ⟨k, by omega⟩)
    (hqe : q.length % 2 = 0) (hlt : q.length < k) :
    ∃ l, HasPathLength M 1 (p.vertex ⟨k, by omega⟩) l ∧ l < p.length := by
  have hinter := p.shorter_prefix_intersects hp k hk q hend (by omega) hlt
  have hh : Nonempty (FirstHit q p (k + 1)) := firstHit_exists q p (k + 1) (by
    obtain ⟨a, b, hb, hab⟩ := hinter
    exact ⟨a, b, by omega, hab⟩)
  obtain ⟨h⟩ := hh
  have hqo := h.odd heven (by omega)
  have hj : h.pi.val % 2 = 0 := by
    by_cases hje : h.pi.val % 2 = 0
    · exact hje
    · have hjo : h.pi.val % 2 = 1 := by omega
      have hjoin : (q.take h.qi.val (by omega)).last = p.vertex h.pi := h.hit
      have hpar : (q.take h.qi.val (by omega)).length % 2 = h.pi.val % 2 := by
        simp only [take_length, hqo, hjo]
      have hbound := p.no_shorter_disjoint_prefix hp h.pi.val (by omega)
        (q.take h.qi.val (by omega)) hjoin hpar h.forward_disjoint
      change h.pi.val ≤ h.qi.val at hbound
      have := h.in_suffix
      omega
  have hjoin : (q.take h.qi.val (by omega)).last = p.vertex h.pi := h.hit
  have hkj : k ≤ h.pi.val := by have := h.in_suffix; omega
  have hdisj := h.reverse_disjoint_to_target hk hend
  let r := (q.take h.qi.val (by omega)).spliceReverse p k h.pi.val hkj
    (by omega) hjoin hqo hj hdisj
  have hrlen : r.length = h.qi.val + (h.pi.val - k) := rfl
  have hrend : r.last = p.vertex ⟨k, by omega⟩ := spliceReverse_last _ _ _ _ _ _ _ _ _ _
  refine ⟨r.length, ⟨r, hrend, rfl, by rw [hrlen]; omega⟩, ?_⟩
  rw [hrlen]
  omega

/-- Comparison with an odd path to the terminal vertex. The first-intersection
case split yields either a bounded odd path to the interior vertex or a lower
bound on the odd terminal path's length. -/
theorem odd_terminal_comparison (p : AltPath M) (hp : p.Shortest)
    (heven : p.length % 2 = 0) (k : Nat) (hk : k ≤ p.length)
    (hkpos : 0 < k) (hke : k % 2 = 0)
    (r : AltPath M) (hrend : r.last = p.last) :
    (∃ l, HasPathLength M 1 (p.vertex ⟨k, by omega⟩) l ∧
      l ≤ r.length + (p.length - k)) ∨ k - 1 ≤ r.length := by
  have hh : Nonempty (FirstHit r p (k - 1)) := firstHit_exists r p (k - 1)
    ⟨⟨r.length, by omega⟩, ⟨p.length, by omega⟩, by change k - 1 ≤ p.length; omega, hrend⟩
  obtain ⟨h⟩ := hh
  have hqo := h.odd heven (by omega)
  have hjoin : (r.take h.qi.val (by omega)).last = p.vertex h.pi := h.hit
  by_cases hje : h.pi.val % 2 = 0
  · have hkj : k ≤ h.pi.val := by have := h.in_suffix; omega
    have hd := h.reverse_disjoint k (by omega)
    let z := (r.take h.qi.val (by omega)).spliceReverse p k h.pi.val hkj
      (by omega) hjoin hqo hje hd
    have hzlen : z.length = h.qi.val + (h.pi.val - k) := rfl
    have hzend : z.last = p.vertex ⟨k, by omega⟩ := spliceReverse_last _ _ _ _ _ _ _ _ _ _
    left
    refine ⟨z.length, ⟨z, hzend, rfl, by rw [hzlen]; omega⟩, ?_⟩
    rw [hzlen]
    omega
  · have hjo : h.pi.val % 2 = 1 := by omega
    have hpar : (r.take h.qi.val (by omega)).length % 2 = h.pi.val % 2 := by
      simp only [take_length, hqo, hjo]
    have hb := p.no_shorter_disjoint_prefix hp h.pi.val (by omega)
      (r.take h.qi.val (by omega)) hjoin hpar h.forward_disjoint
    change h.pi.val ≤ h.qi.val at hb
    right
    have := h.in_suffix
    omega

private theorem level_bound_of_witness (parity : Nat) (v : V) (l : Nat)
    (hl : HasPathLength M parity v l) :
    ∃ k, level M parity v = some k ∧ k ≤ l := by
  cases he : level M parity v with
  | none => exact False.elim ((level_eq_none_iff M parity v).1 he ⟨l, hl⟩)
  | some k => exact ⟨k, rfl, ((level_eq_some_iff M parity v k).1 he).2 l hl⟩

/-- The even-terminal/even-interior core of Theorem 5.3, with infinite levels
included. The order premise uses infinity as the greatest element. -/
theorem even_vertex_honest (p : AltPath M) (hp : p.Shortest)
    (heven : p.length % 2 = 0) (k : Nat) (hk : k ≤ p.length) (hke : k % 2 = 0)
    (ht : levelLE (tenacity M p.last) (tenacity M (p.vertex ⟨k, by omega⟩))) :
    p.BFSHonest ⟨k, by omega⟩ := by
  obtain ⟨a, hae, hak⟩ := p.prefix_level_bound ⟨k, by omega⟩
  change level M (k % 2) (p.vertex ⟨k, by omega⟩) = some a at hae
  rw [hke] at hae
  change a ≤ k at hak
  have hve : evenlevel M p.last = some p.length :=
    (level_eq_some_iff M 0 p.last p.length).2 (by simpa only [Shortest, heven] using hp)
  apply (p.honest_iff_level ⟨k, by omega⟩).2
  change level M (k % 2) (p.vertex ⟨k, by omega⟩) = some k
  rw [hke]
  by_cases heq : a = k
  · exact heq ▸ hae
  · have hlt : a < k := by omega
    obtain ⟨q, hqend, hqlen, hqpar⟩ := ((level_eq_some_iff M 0 _ a).1 hae).1
    have hqe : q.length % 2 = 0 := by omega
    obtain ⟨l, hl, hlL⟩ := p.shorter_even_prefix_opposite hp heven k hk hke q hqend hqe (by omega)
    obtain ⟨b, hbo, hbl⟩ := level_bound_of_witness 1 _ l hl
    have htb : tenacity M (p.vertex ⟨k, by omega⟩) = some (a + b) := by
      simp only [tenacity, evenlevel, oddlevel, hae, hbo, levelAdd]
    rw [htb] at ht
    cases hvo : oddlevel M p.last with
    | none =>
      simp only [tenacity, hve, hvo, levelAdd, levelLE] at ht
    | some s =>
      have hsum : p.length + s ≤ a + b := by
        simpa only [tenacity, hve, hvo, levelAdd, levelLE] using ht
      obtain ⟨r, hrend, hrlen, _⟩ := ((level_eq_some_iff M 1 p.last s).1 hvo).1
      rcases p.odd_terminal_comparison hp heven k hk (by omega) hke r hrend with hb | hs
      · obtain ⟨c, hc, hcl⟩ := hb
        have hbc := ((level_eq_some_iff M 1 _ b).1 hbo).2 c hc
        omega
      · omega

/-- The strict-tenacity conclusion of Theorem 5.3 for even paths and even indices. -/
theorem even_vertex_minlevel (p : AltPath M) (hp : p.Shortest)
    (heven : p.length % 2 = 0) (k : Nat) (hk : k ≤ p.length) (hke : k % 2 = 0)
    (ht : levelLT (tenacity M p.last) (tenacity M (p.vertex ⟨k, by omega⟩))) :
    minlevel M (p.vertex ⟨k, by omega⟩) = some k := by
  have hhon := p.even_vertex_honest hp heven k hk hke (levelLT_le ht)
  have hue : evenlevel M (p.vertex ⟨k, by omega⟩) = some k := by
    have hh := (p.honest_iff_level ⟨k, by omega⟩).1 hhon
    simpa only [hke] using hh
  have hve : evenlevel M p.last = some p.length :=
    (level_eq_some_iff M 0 p.last p.length).2 (by simpa only [Shortest, heven] using hp)
  unfold minlevel
  rw [hue]
  cases huo : oddlevel M (p.vertex ⟨k, by omega⟩) with
  | none => rfl
  | some b =>
    change some (min k b) = some k
    by_cases hkb : k ≤ b
    · exact congrArg some (Nat.min_eq_left hkb)
    · have hblt : b < k := by omega
      cases hvo : oddlevel M p.last with
      | none =>
        simp only [tenacity, hue, huo, hve, hvo, levelAdd, levelLT] at ht
      | some s =>
        have hsum : p.length + s < k + b := by
          simpa only [tenacity, hue, huo, hve, hvo, levelAdd, levelLT] using ht
        obtain ⟨r, hrend, hrlen, _⟩ := ((level_eq_some_iff M 1 p.last s).1 hvo).1
        rcases p.odd_terminal_comparison hp heven k hk (by omega) hke r hrend with hb | hs
        · obtain ⟨c, hc, hcl⟩ := hb
          have hbc := ((level_eq_some_iff M 1 _ b).1 huo).2 c hc
          omega
        · omega

/-- Limited BFS-honesty for even-terminal paths, at both parities of interior vertex. -/
theorem limited_honesty_even (p : AltPath M) (hp : p.Shortest)
    (heven : p.length % 2 = 0) (i : Fin (p.length + 1))
    (ht : levelLE (tenacity M p.last) (tenacity M (p.vertex i))) :
    p.BFSHonest i ∧
      (levelLT (tenacity M p.last) (tenacity M (p.vertex i)) →
        minlevel M (p.vertex i) = some i.val) := by
  by_cases hie : i.val % 2 = 0
  · exact ⟨p.even_vertex_honest hp heven i.val (by omega) hie ht,
      p.even_vertex_minlevel hp heven i.val (by omega) hie⟩
  · have hio : i.val % 2 = 1 := by omega
    let j : Fin (p.length + 1) := ⟨i.val + 1, by omega⟩
    have hje : j.val % 2 = 0 := by change (i.val + 1) % 2 = 0; omega
    have hm : M.mate (p.vertex i) = some (p.vertex j) := p.mate_next i.val (by omega) hio
    have hten := (matched_tenacity M hm).1
    have htj : levelLE (tenacity M p.last) (tenacity M (p.vertex j)) := by rwa [← hten]
    have hhon := p.even_vertex_honest hp heven j.val (by omega) hje htj
    have hjelevel : evenlevel M (p.vertex j) = some j.val := by
      have hh := (p.honest_iff_level j).1 hhon
      simpa only [hje] using hh
    have hueq := evenlevel_matched M hm
    have huolevel : oddlevel M (p.vertex i) = some i.val := by
      rw [hjelevel] at hueq
      cases huo : oddlevel M (p.vertex i) with
      | none => simp [huo] at hueq
      | some a =>
        have he : j.val = a + 1 := by simpa only [huo, Option.map_some, Option.some.injEq] using hueq
        have hv : a = i.val := by change i.val + 1 = a + 1 at he; omega
        exact congrArg some hv
    refine ⟨?_, ?_⟩
    · apply (p.honest_iff_level i).2
      simpa only [hio] using huolevel
    · intro hstrict
      have hstrictj : levelLT (tenacity M p.last) (tenacity M (p.vertex j)) := by rwa [← hten]
      have hminj := p.even_vertex_minlevel hp heven j.val (by omega) hje hstrictj
      have hue := evenlevel_matched M (M.symm hm)
      unfold minlevel
      rw [huolevel, hue]
      cases hjo : oddlevel M (p.vertex j) with
      | none => rfl
      | some b =>
        have hmin : min j.val b = j.val := by
          simpa only [minlevel, hjelevel, hjo, levelMin, Option.some.injEq] using hminj
        have hbj : j.val ≤ b := by omega
        change some (min (b + 1) i.val) = some i.val
        exact congrArg some (Nat.min_eq_right (by change i.val + 1 ≤ b at hbj; omega))

/-- Theorem 5.3 of the supplied paper: limited BFS-honesty. The formal statement
includes both endpoint parities, free endpoints, and infinite levels. The strict
comparison gives the paper's additional minlevel conclusion. -/
theorem limited_bfs_honesty (p : AltPath M) (hp : p.Shortest)
    (i : Fin (p.length + 1))
    (ht : levelLE (tenacity M p.last) (tenacity M (p.vertex i))) :
    p.BFSHonest i ∧
      (levelLT (tenacity M p.last) (tenacity M (p.vertex i)) →
        minlevel M (p.vertex i) = some i.val) := by
  by_cases heven : p.length % 2 = 0
  · exact p.limited_honesty_even hp heven i ht
  · have hodd : p.length % 2 = 1 := by omega
    cases hm : M.mate p.last with
    | none =>
      have ha : p.Augmenting := ⟨hodd, hm⟩
      have hve : evenlevel M p.last = some 0 := (evenlevel_zero_iff_free M p.last).2 hm
      have hvo : oddlevel M p.last = some p.length :=
        (level_eq_some_iff M 1 p.last p.length).2 (by simpa only [Shortest, hodd] using hp)
      have hvt : tenacity M p.last = some p.length := by
        simp only [tenacity, hve, hvo, levelAdd, Nat.zero_add]
      obtain ⟨t, hut, htL⟩ := p.augmenting_tenacity_bound ha i
      have hLt : p.length ≤ t := by simpa only [hvt, hut, levelLE] using ht
      refine ⟨p.honest_on_augmenting_of_tenacity_ge ha i t hut hLt, ?_⟩
      intro hstrict
      have hh : p.length < t := by simpa only [hvt, hut, levelLT] using hstrict
      omega
    | some v =>
      let q := p.appendMatched hodd hm
      have hqlen : q.length = p.length + 1 := rfl
      have hqend : q.last = v := appendMatched_last _ _ _
      have hqeven : q.length % 2 = 0 := by omega
      have hqshort : q.Shortest := by
        unfold Shortest
        rw [hqeven, hqend, hqlen]
        exact (matched_shortest_iff M hm p.length).2 (by simpa only [Shortest, hodd] using hp)
      let j : Fin (q.length + 1) := ⟨i.val, by omega⟩
      have hvertex : q.vertex j = p.vertex i := by
        change (if h : i.val ≤ p.length then p.vertex ⟨i.val, _⟩ else v) = p.vertex i
        simp only [dite_eq_left (show i.val ≤ p.length by omega)]
      have htend : tenacity M q.last = tenacity M p.last := by
        rw [hqend]
        exact (matched_tenacity M hm).1.symm
      have htq : levelLE (tenacity M q.last) (tenacity M (q.vertex j)) := by
        simpa only [htend, hvertex] using ht
      obtain ⟨hhon, hmin⟩ := q.limited_honesty_even hqshort hqeven j htq
      refine ⟨?_, ?_⟩
      · simpa only [BFSHonest, hvertex] using hhon
      · intro hstrict
        have hstrictq : levelLT (tenacity M q.last) (tenacity M (q.vertex j)) := by
          simpa only [htend, hvertex] using hstrict
        simpa only [hvertex] using hmin hstrictq

end AltPath
end MaximumMatching

end LimitedHonesty
