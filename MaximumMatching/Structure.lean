import MaximumMatching.Honesty

/-! Semantic specification for the structural core of MV.
Source: Definitions 3.1, 3.3--3.9 and 6.1--6.4, pp.8--10 and 20--21.

These are mathematical definitions, independent of operational MIN/MAX state.
`BaseOnPath` does not assert that different shortest paths have the same base;
that path-independence assertion is the open Claim 6.4 / Theorem 6.19 obligation.
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
