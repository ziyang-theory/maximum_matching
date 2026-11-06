import MaximumMatching.Foundations
import MaximumMatching.Structure

section Min

/-! Executable local updates from MIN, Algorithm 1 (source p.13).

The module does not claim frontier completeness or correctness of assigned levels.
Those properties require Theorems 6.19 and 8.3. Scan candidates must be supplied by
the eventual phase implementation. Unknown tenacity is represented by `none`. -/
namespace MaximumMatching
namespace Search

structure State (V : Type) where
  minLabel : V → Option Nat
  maxLabel : V → Option Nat
  predecessors : V → List V
  scanned : List (V × V)
  props : List (V × V)
  bridges : List (V × V)
  bucket : Nat → List (V × V)

variable {V : Type} [DecidableEq V] {G : Graph V}

def initial (M : Matching G) : State V where
  minLabel v := if M.mate v = none then some 0 else none
  maxLabel := fun _ => none
  predecessors := fun _ => []
  scanned := []
  props := []
  bridges := []
  bucket := fun _ => []

/-- Retrieve the currently known label of a specified parity. -/
def parityLabel (s : State V) (v : V) (parity : Nat) : Option Nat := do
  let lo ← s.minLabel v
  if lo % 2 = parity then some lo else do
    let hi ← s.maxLabel v
    if hi % 2 = parity then some hi else none

def edgeTenacity (M : Matching G) (s : State V) (u v : V) : Option Nat := do
  let parity := if M.mate u = some v then 1 else 0
  let a ← parityLabel s u parity
  let b ← parityLabel s v parity
  some (a + b + 1)

/-- `none` is infinity, not level zero. Ties must admit another predecessor. -/
def admits (old : Option Nat) (next : Nat) : Bool :=
  match old with
  | none => true
  | some k => decide (next ≤ k)

def seen (s : State V) (u v : V) : Bool :=
  decide ((u, v) ∈ s.scanned ∨ (v, u) ∈ s.scanned)

def enqueue (s : State V) (u v : V) (t : Option Nat) : State V :=
  match t with
  | none => s
  | some t => { s with bucket := fun k => if k = t then (u, v) :: s.bucket k else s.bucket k }

/-- One scan of an appropriate edge, after the caller has selected its source level. -/
def scan (M : Matching G) (i : Nat) (u v : V) (s : State V) : State V :=
  if seen s u v then s else
  let marked := { s with scanned := (u, v) :: s.scanned }
  if admits (s.minLabel v) (i + 1) then
    { marked with
      minLabel := fun w => if w = v then some (i + 1) else s.minLabel w
      predecessors := fun w => if w = v then u :: s.predecessors w else s.predecessors w
      props := (u, v) :: s.props }
  else
    enqueue { marked with bridges := (u, v) :: s.bridges } u v (edgeTenacity M s u v)

/-- The adjacency/parity/frontier guard used before scanning. The complete phase
must supply an adjacency enumeration and establish frontier completeness. -/
def scanCandidate [DecidableRel G.Adj] (M : Matching G) (i : Nat) (u v : V) (s : State V) : State V :=
  if G.Adj u v ∧ parityLabel s u (i % 2) = some i ∧
      ((M.mate u = some v) ↔ i % 2 = 1) then scan M i u v s else s

def scanCandidates [DecidableRel G.Adj] (M : Matching G) (i : Nat) (candidates : List (V × V))
    (s : State V) : State V :=
  candidates.foldl (fun s e => scanCandidate M i e.1 e.2 s) s

omit [DecidableEq V] in
theorem initial_free_iff (M : Matching G) (v : V) :
    (initial M).minLabel v = some 0 ↔ M.Free v := by
  simp only [initial, Matching.Free]
  split <;> simp_all

omit [DecidableEq V] in
theorem initial_max_unknown (M : Matching G) (v : V) :
    (initial M).maxLabel v = none := rfl

theorem admits_tie (i : Nat) : admits (some (i + 1)) (i + 1) = true := by
  simp [admits]

theorem scan_seen (M : Matching G) (i : Nat) (u v : V) (s : State V)
    (h : seen s u v = true) : scan M i u v s = s := by
  simp [scan, h]

theorem scan_marks (M : Matching G) (i : Nat) (u v : V) (s : State V) :
    seen (scan M i u v s) u v = true := by
  unfold scan
  split
  · assumption
  · split
    · simp [seen]
    · unfold enqueue
      split <;> simp [seen]

theorem seen_comm (s : State V) (u v : V) : seen s u v = seen s v u := by
  simp [seen, Or.comm]

theorem scan_reverse_noop (M : Matching G) (i j : Nat) (u v : V) (s : State V) :
    scan M j v u (scan M i u v s) = scan M i u v s := by
  apply scan_seen
  rw [seen_comm]
  exact scan_marks M i u v s

theorem scan_assigns (M : Matching G) (i : Nat) (u v : V) (s : State V)
    (hs : seen s u v = false) (ha : admits (s.minLabel v) (i + 1) = true) :
    (scan M i u v s).minLabel v = some (i + 1) ∧
    (scan M i u v s).predecessors v = u :: s.predecessors v ∧
    (scan M i u v s).props = (u, v) :: s.props := by
  simp [scan, hs, ha]

/-- A second predecessor at the same level is retained, not discarded by `<`. -/
theorem scan_tie_adds_predecessor (M : Matching G) (i : Nat) (u v : V) (s : State V)
    (hs : seen s u v = false) (hlevel : s.minLabel v = some (i + 1)) :
    (scan M i u v s).predecessors v = u :: s.predecessors v := by
  exact (scan_assigns M i u v s hs (by rw [hlevel]; exact admits_tie i)).2.1

theorem scan_preserves_other_label (M : Matching G) (i : Nat) (u v w : V)
    (s : State V) (hw : w ≠ v) :
    (scan M i u v s).minLabel w = s.minLabel w := by
  unfold scan
  split
  · rfl
  · split
    · simp [hw]
    · unfold enqueue
      split <;> rfl

theorem scan_preserves_max (M : Matching G) (i : Nat) (u v w : V) (s : State V) :
    (scan M i u v s).maxLabel w = s.maxLabel w := by
  unfold scan
  split
  · rfl
  · split
    · rfl
    · unfold enqueue
      split <;> rfl

/-- Assignment from MAX for a vertex whose support membership is still to be
established by DDFS. This is only the local arithmetic update, not support search. -/
def assignMax (s : State V) (t : Nat) (v : V) : State V :=
  match s.minLabel v with
  | none => s
  | some lo => { s with maxLabel := fun w => if w = v then some (t - lo) else s.maxLabel w }

theorem assignMax_sum (s : State V) (t lo : Nat) (v : V)
    (h : s.minLabel v = some lo) (hle : lo ≤ t) :
    ∃ hi, (assignMax s t v).maxLabel v = some hi ∧ lo + hi = t := by
  refine ⟨t - lo, ?_, by omega⟩
  simp [assignMax, h]

end Search
end MaximumMatching

end Min

section MinLevelEdges

/-! Relating minimum alternating-path levels to directed prop edges.
The extension theorem below has no tenacity or BFS-honesty hypothesis. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V}

theorem minlevel_witness (M : Matching G) (v : V) (k : Nat)
    (hk : minlevel M v = some k) :
    ∃ p : AltPath M, p.last = v ∧ p.length = k := by
  unfold minlevel at hk
  cases he : evenlevel M v with
  | none =>
    simp only [he, levelMin] at hk
    obtain ⟨p, hp, hl, _⟩ := ((level_eq_some_iff M 1 v k).1 hk).1
    exact ⟨p, hp, hl⟩
  | some a =>
    cases ho : oddlevel M v with
    | none =>
      simp only [he, ho, levelMin, Option.some.injEq] at hk
      obtain ⟨p, hp, hl, _⟩ := ((level_eq_some_iff M 0 v a).1 he).1
      exact ⟨p, hp, hl.trans hk⟩
    | some b =>
      simp only [he, ho, levelMin, Option.some.injEq] at hk
      by_cases hab : a ≤ b
      · have ha : a = k := by omega
        obtain ⟨p, hp, hl, _⟩ := ((level_eq_some_iff M 0 v a).1 he).1
        exact ⟨p, hp, hl.trans ha⟩
      · have hb : b = k := by omega
        obtain ⟨p, hp, hl, _⟩ := ((level_eq_some_iff M 1 v b).1 ho).1
        exact ⟨p, hp, hl.trans hb⟩

theorem minlevel_le_path (M : Matching G) (v : V) (k : Nat)
    (hk : minlevel M v = some k) (p : AltPath M) (hp : p.last = v) :
    k ≤ p.length := by
  have hw : HasPathLength M (p.length % 2) v p.length := ⟨p, hp, rfl, rfl⟩
  have hf : ∃ l, level M (p.length % 2) v = some l ∧ l ≤ p.length := by
    cases he : level M (p.length % 2) v with
    | none => exact False.elim ((level_eq_none_iff M _ v).1 he ⟨p.length, hw⟩)
    | some l => exact ⟨l, rfl, ((level_eq_some_iff M _ v l).1 he).2 _ hw⟩
  obtain ⟨l, hl, hle⟩ := hf
  unfold minlevel at hk
  have hpar : p.length % 2 = 0 ∨ p.length % 2 = 1 := by omega
  rcases hpar with hpar | hpar
  · rw [hpar] at hl
    change evenlevel M v = some l at hl
    rw [hl] at hk
    cases ho : oddlevel M v <;> simp only [ho, levelMin, Option.some.injEq] at hk <;> omega
  · rw [hpar] at hl
    change oddlevel M v = some l at hl
    rw [hl] at hk
    cases he : evenlevel M v <;> simp only [he, levelMin, Option.some.injEq] at hk <;> omega

/-- A predecessor has strictly smaller minimum level whenever both are finite.
The prefix need not itself attain its minimum level. -/
theorem predecessor_minlevel_lt (M : Matching G) (u v : V) (i j : Nat)
    (hpred : Predecessor M u v)
    (hu : minlevel M u = some i) (hv : minlevel M v = some j) : i < j := by
  obtain ⟨p, hp, hmin, hpos, hend⟩ := hpred
  have hlen : p.length = j := Option.some.inj (hmin.symm.trans hv)
  have hb := minlevel_le_path M u i hu (p.take (p.length - 1) (by omega)) hend
  simp only [AltPath.take_length] at hb
  omega

theorem not_propEdge_of_minlevel_eq (M : Matching G) (u v : V) (k : Nat)
    (hu : minlevel M u = some k) (hv : minlevel M v = some k) :
    ¬ PropEdge M u v := by
  rintro (h | h)
  · have := predecessor_minlevel_lt M u v k k h hu hv
    omega
  · have := predecessor_minlevel_lt M v u k k h hv hu
    omega

/-- Consecutive minimum levels, adjacency, and the required matching parity
suffice for the edge to be an oriented prop. Freshness follows from minimality. -/
theorem predecessor_of_consecutive_minlevels (M : Matching G) (u v : V) (k : Nat)
    (hu : minlevel M u = some k) (hv : minlevel M v = some (k + 1))
    (hadj : G.Adj u v) (hpar : (M.mate u = some v) ↔ k % 2 = 1) :
    Predecessor M u v := by
  obtain ⟨p, hp, hl⟩ := minlevel_witness M u k hu
  have hfresh : ∀ i, p.vertex i ≠ v := by
    intro i hi
    have hb := minlevel_le_path M v (k + 1) hv (p.take i.val (by omega))
      (by simpa only [AltPath.take_last] using hi)
    simp only [AltPath.take_length] at hb
    omega
  have ha : G.Adj p.last v := hp ▸ hadj
  have hpa : (M.mate p.last = some v) ↔ p.length % 2 = 1 := by
    simpa only [hp, hl] using hpar
  let q := p.append v hfresh ha hpa
  refine ⟨q, p.append_last v hfresh ha hpa, ?_, ?_⟩
  · simpa only [q, AltPath.append_length, hl] using hv
  · refine ⟨by change 0 < p.length + 1; omega, ?_⟩
    change (if h : p.length + 1 - 1 ≤ p.length then
      p.vertex ⟨p.length + 1 - 1, by omega⟩ else v) = u
    simpa only [Nat.add_sub_cancel, Nat.le_refl, dite_true] using (show p.vertex ⟨p.length, by omega⟩ = u from hp)

end MaximumMatching

end MinLevelEdges

section MinCorrectness

/-! Semantic facts for MIN, including the predecessor-honesty argument in
Theorem 8.3, Task 1 (source p.38). These results do not assume the structural
base/bridge induction or correctness of MAX. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

theorem minlevel_le_of_level (v : V) (i : Nat)
    (hi : level M (i % 2) v = some i) :
    ∃ k, minlevel M v = some k ∧ k ≤ i := by
  by_cases he : i % 2 = 0
  · have hv : evenlevel M v = some i := by simpa only [he] using hi
    unfold minlevel
    rw [hv]
    cases ho : oddlevel M v with
    | none => exact ⟨i, rfl, Nat.le_refl _⟩
    | some o => exact ⟨min i o, rfl, Nat.min_le_left _ _⟩
  · have ho : i % 2 = 1 := by omega
    have hv : oddlevel M v = some i := by simpa only [ho] using hi
    unfold minlevel
    rw [hv]
    cases he : evenlevel M v with
    | none => exact ⟨i, rfl, Nat.le_refl _⟩
    | some e => exact ⟨min e i, rfl, Nat.min_le_right _ _⟩

theorem minlevel_finite_of_path (p : AltPath M) :
    ∃ k, minlevel M p.last = some k ∧ k ≤ p.length := by
  obtain ⟨i, hi, hip⟩ := p.prefix_level_bound ⟨p.length, by omega⟩
  have hpar := level_parity M (p.length % 2) p.last i hi
  obtain ⟨k, hk, hki⟩ := minlevel_le_of_level p.last i (by rw [hpar]; exact hi)
  exact ⟨k, hk, by omega⟩

namespace AltPath

/-- The last predecessor of a minlevel path is honest, even when earlier
prefixes are dishonest and the endpoint has infinite tenacity. -/
theorem minlevel_last_predecessor_honest (p : AltPath M)
    (hmin : minlevel M p.last = some p.length) (hpos : 0 < p.length) :
    p.BFSHonest ⟨p.length - 1, by omega⟩ := by
  let i : Fin (p.length + 1) := ⟨p.length - 1, by omega⟩
  apply (p.honest_iff_level i).2
  obtain ⟨k, hk, hki⟩ := p.prefix_level_bound i
  have hkeq : k = i.val := by
    apply Nat.le_antisymm hki
    apply Nat.le_of_not_lt
    intro hlt
    obtain ⟨q, hqend, hqlen, hqpar⟩ := ((level_eq_some_iff M (i.val % 2) (p.vertex i) k).1 hk).1
    have hfresh : ∀ j, q.vertex j ≠ p.last := by
      intro j hj
      have hb := minlevel_le_path M p.last p.length hmin (q.take j.val (by omega)) hj
      simp only [take_length] at hb
      have := j.isLt
      dsimp [i] at hlt
      omega
    have ha : G.Adj q.last p.last := by
      rw [hqend]
      have h := p.adjacent ⟨p.length - 1, by omega⟩
      simpa only [i, AltPath.last, show p.length - 1 + 1 = p.length by omega] using h
    have hpar : (M.mate q.last = some p.last) ↔ q.length % 2 = 1 := by
      rw [hqend, hqlen, hqpar]
      have h := p.alternating ⟨p.length - 1, by omega⟩
      simpa only [i, AltPath.last, show p.length - 1 + 1 = p.length by omega] using h
    let r := q.append p.last hfresh ha hpar
    have hb := minlevel_le_path M p.last p.length hmin r (append_last _ _ _ _ _)
    change p.length ≤ q.length + 1 at hb
    dsimp [i] at hlt
    omega
  simpa only [hkeq] using hk

end AltPath

/-- Exact semantic guard for an oriented prop at target minlevel `i+1`.
The source may be scanned at its maxlevel: requiring its minlevel to be `i`
would incorrectly exclude these predecessors. -/
theorem predecessor_iff_level_guard (u v : V) (i : Nat)
    (hv : minlevel M v = some (i + 1)) :
    Predecessor M u v ↔ G.Adj u v ∧ level M (i % 2) u = some i ∧
      ((M.mate u = some v) ↔ i % 2 = 1) := by
  constructor
  · rintro ⟨p, hp, hmin, hpos, hu⟩
    have hl : p.length = i + 1 := Option.some.inj (hmin.symm.trans hv)
    have hpred : p.vertex ⟨i, by omega⟩ = u := by simpa only [hl, Nat.add_sub_cancel] using hu
    have hlast : p.vertex ⟨i + 1, by omega⟩ = v := by
      simpa only [AltPath.last, hl] using hp
    have hhon := (p.honest_iff_level ⟨p.length - 1, by omega⟩).1
      (p.minlevel_last_predecessor_honest (by rw [hp]; exact hmin) hpos)
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hpred, hlast] using p.adjacent ⟨i, by omega⟩
    · simpa only [hl, Nat.add_sub_cancel, hpred] using hhon
    · simpa only [hpred, hlast] using p.alternating ⟨i, by omega⟩
  · rintro ⟨hadj, hlevel, hpar⟩
    obtain ⟨p, hp, hl, _⟩ := ((level_eq_some_iff M (i % 2) u i).1 hlevel).1
    have hfresh : ∀ j, p.vertex j ≠ v := by
      intro j hj
      have hb := minlevel_le_path M v (i + 1) hv (p.take j.val (by omega)) hj
      simp only [AltPath.take_length] at hb
      have := j.isLt
      omega
    have ha : G.Adj p.last v := by rw [hp]; exact hadj
    have hpa : (M.mate p.last = some v) ↔ p.length % 2 = 1 := by
      simpa only [hp, hl] using hpar
    refine ⟨p.append v hfresh ha hpa, AltPath.append_last _ _ _ _ _, ?_, ?_⟩
    · simpa only [AltPath.append_length, hl] using hv
    · refine ⟨by simp only [AltPath.append_length]; omega, ?_⟩
      change (if h : p.length + 1 - 1 ≤ p.length then
        p.vertex ⟨p.length + 1 - 1, by omega⟩ else v) = u
      simpa only [Nat.add_sub_cancel, Nat.le_refl, dite_true, AltPath.last] using hp

/-- Scanning from an actual parity level cannot create a spurious minlevel.
The lower-bound premise expresses that all earlier minlevels were found. -/
theorem minlevel_of_scan_guard (u v : V) (i : Nat)
    (hu : level M (i % 2) u = some i) (hadj : G.Adj u v)
    (hpar : (M.mate u = some v) ↔ i % 2 = 1)
    (hlower : levelLE (some (i + 1)) (minlevel M v)) :
    minlevel M v = some (i + 1) ∧ Predecessor M u v := by
  obtain ⟨p, hp, hl, _⟩ := ((level_eq_some_iff M (i % 2) u i).1 hu).1
  have lower (q : AltPath M) (hq : q.last = v) : i + 1 ≤ q.length := by
    obtain ⟨k, hk, hkq⟩ := minlevel_finite_of_path q
    rw [hq] at hk
    rw [hk] at hlower
    change i + 1 ≤ k at hlower
    omega
  have hfresh : ∀ j, p.vertex j ≠ v := by
    intro j hj
    have hb := lower (p.take j.val (by omega)) hj
    simp only [AltPath.take_length] at hb
    have := j.isLt
    omega
  have ha : G.Adj p.last v := by rw [hp]; exact hadj
  have hpa : (M.mate p.last = some v) ↔ p.length % 2 = 1 := by
    simpa only [hp, hl] using hpar
  let q := p.append v hfresh ha hpa
  obtain ⟨k, hk, hkq⟩ := minlevel_finite_of_path q
  have hqend : q.last = v := AltPath.append_last _ _ _ _ _
  rw [hqend] at hk
  have hlow := hlower
  rw [hk] at hlow
  change i + 1 ≤ k at hlow
  change k ≤ p.length + 1 at hkq
  have hkeq : k = i + 1 := by omega
  have hv : minlevel M v = some (i + 1) := by simpa only [hkeq] using hk
  exact ⟨hv, (predecessor_iff_level_guard u v i hv).2 ⟨hadj, hu, hpar⟩⟩

end MaximumMatching

namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- An appropriate edge from a finite parity level reaches a vertex of
minlevel at most one larger. The proof retains simple paths, handling an
already-occurring destination by taking a prefix rather than appending a walk. -/
theorem minlevel_neighbor_bound (u v : V) (i : Nat)
    (hu : level M (i % 2) u = some i) (hadj : G.Adj u v)
    (hpar : (M.mate u = some v) ↔ i % 2 = 1) :
    ∃ k, minlevel M v = some k ∧ k ≤ i + 1 := by
  classical
  obtain ⟨p, hp, hl, _⟩ := ((level_eq_some_iff M (i % 2) u i).1 hu).1
  by_cases hhit : ∃ j, p.vertex j = v
  · obtain ⟨j, hj⟩ := hhit
    obtain ⟨k, hk, hkj⟩ := minlevel_finite_of_path (p.take j.val (by omega))
    rw [AltPath.take_last, hj] at hk
    simp only [AltPath.take_length] at hkj
    exact ⟨k, hk, by have := j.isLt; omega⟩
  · have hfresh : ∀ j, p.vertex j ≠ v := by
      intro j hj
      exact hhit ⟨j, hj⟩
    have ha : G.Adj p.last v := by rw [hp]; exact hadj
    have hpa : (M.mate p.last = some v) ↔ p.length % 2 = 1 := by
      simpa only [hp, hl] using hpar
    obtain ⟨k, hk, hkp⟩ := minlevel_finite_of_path (p.append v hfresh ha hpa)
    rw [AltPath.append_last] at hk
    simp only [AltPath.append_length, hl] at hkp
    exact ⟨k, hk, hkp⟩

end MaximumMatching

end MinCorrectness

section MinScan

/-! Semantic preservation for the executable MIN scan. The hypotheses express
the induction invariant at the start of search level `i`; establishing it for
the synchronized MIN/MAX phase remains a separate obligation. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

theorem level_of_minlevel (v : V) (k : Nat) (hk : minlevel M v = some k) :
    level M (k % 2) v = some k := by
  obtain ⟨p, hp, hl⟩ := minlevel_witness M v k hk
  apply (level_eq_some_iff M (k % 2) v k).2
  refine ⟨⟨p, hp, hl, rfl⟩, ?_⟩
  rintro l ⟨q, hq, hql, _⟩
  have h := minlevel_le_path M v k hk q hq
  omega

theorem level_of_maxlevel (v : V) (k : Nat) (hk : maxlevel M v = some k) :
    level M (k % 2) v = some k := by
  unfold maxlevel at hk
  cases he : evenlevel M v with
  | none => simp only [he, levelMax] at hk; contradiction
  | some e =>
    cases ho : oddlevel M v with
    | none => simp only [he, ho, levelMax] at hk; contradiction
    | some o =>
      have hep := level_parity M 0 v e he
      have hop := level_parity M 1 v o ho
      have hmax : max e o = k := by simpa only [he, ho, levelMax, Option.some.injEq] using hk
      by_cases hke : k % 2 = 0
      · have hek : e = k := by omega
        simpa only [hke, hek] using he
      · have hko : k % 2 = 1 := by omega
        have hok : o = k := by omega
        simpa only [hko, hok] using ho

namespace Search
variable [DecidableEq V]

/-- Every assigned label is the corresponding semantic minlevel or maxlevel.
Unknown labels are allowed; completeness is a separate predicate. -/
def LabelsSound (M : Matching G) (s : State V) : Prop :=
  (∀ v k, s.minLabel v = some k → minlevel M v = some k) ∧
  (∀ v k, s.maxLabel v = some k → maxlevel M v = some k)

def MinCompleteBelow (M : Matching G) (i : Nat) (s : State V) : Prop :=
  ∀ v k, minlevel M v = some k → k ≤ i → s.minLabel v = some k

/-- Every earlier oriented prop has already been scanned, in either direction. -/
def EarlierPropsSeen (M : Matching G) (i : Nat) (s : State V) : Prop :=
  ∀ u v k, Predecessor M u v → minlevel M v = some k → k ≤ i → seen s u v = true

omit [DecidableEq V] in
theorem parityLabel_sound (s : State V) (hs : LabelsSound M s)
    (v : V) (parity k : Nat) (h : parityLabel s v parity = some k) :
    level M parity v = some k := by
  unfold parityLabel at h
  cases hlo : s.minLabel v with
  | none => simp [hlo] at h
  | some lo =>
    simp only [hlo] at h
    dsimp at h
    split at h
    next hp =>
      have heq := Option.some.inj h
      have hl := level_of_minlevel v lo (hs.1 v lo hlo)
      rw [hp, heq] at hl
      exact hl
    next hp =>
      cases hhi : s.maxLabel v with
      | none => simp [hhi] at h
      | some hi =>
        simp only [hhi] at h
        dsimp at h
        split at h
        next hpar =>
          have heq := Option.some.inj h
          have hl := level_of_maxlevel v hi (hs.2 v hi hhi)
          rw [hpar, heq] at hl
          exact hl
        next _ => contradiction

omit [DecidableEq V] in
/-- Completeness at earlier levels makes MIN's operational admission test a
valid lower bound on the destination's true minimum level. -/
theorem admits_semantic_lower_bound (s : State V) (i : Nat)
    (hc : MinCompleteBelow M i s) (v : V)
    (ha : admits (s.minLabel v) (i + 1) = true) :
    levelLE (some (i + 1)) (minlevel M v) := by
  cases hm : minlevel M v with
  | none => trivial
  | some k =>
    change i + 1 ≤ k
    by_cases hki : k ≤ i
    · have hlabel := hc v k hm hki
      simp only [hlabel, admits, decide_eq_true_eq] at ha
      omega
    · omega

/-- An admitted fresh scan assigns the true minimum level and records an
actual oriented predecessor. This connects `scan` to its semantic guard. -/
theorem scan_assigns_semantic (s : State V) (i : Nat) (u v : V)
    (hc : MinCompleteBelow M i s)
    (hu : level M (i % 2) u = some i) (hadj : G.Adj u v)
    (hpar : (M.mate u = some v) ↔ i % 2 = 1)
    (hseen : seen s u v = false) (ha : admits (s.minLabel v) (i + 1) = true) :
    minlevel M v = some (i + 1) ∧ Predecessor M u v ∧
      (scan M i u v s).minLabel v = some (i + 1) ∧
      (scan M i u v s).predecessors v = u :: s.predecessors v := by
  obtain ⟨hmin, hpred⟩ := minlevel_of_scan_guard u v i hu hadj hpar
    (admits_semantic_lower_bound s i hc v ha)
  have hs := scan_assigns M i u v s hseen ha
  exact ⟨hmin, hpred, hs.1, hs.2.1⟩

/-- Rejection on an unseen edge really classifies a bridge, provided all
earlier props have been scanned. Both orientations of a possible prop are
excluded, including a source scanned at its maxlevel. -/
theorem scan_rejects_bridge (s : State V) (i : Nat) (u v : V)
    (hs : LabelsSound M s) (hearlier : EarlierPropsSeen M i s)
    (hu : level M (i % 2) u = some i) (hadj : G.Adj u v)
    (hseen : seen s u v = false) (ha : admits (s.minLabel v) (i + 1) = false) :
    Bridge M u v := by
  have htarget : ∃ k, minlevel M v = some k ∧ k ≤ i := by
    cases hv : s.minLabel v with
    | none => simp only [hv, admits] at ha; contradiction
    | some k =>
      have hki : ¬i + 1 ≤ k := by simpa only [hv, admits, decide_eq_false_iff_not] using ha
      exact ⟨k, hs.1 v k hv, by omega⟩
  obtain ⟨kv, hkv, hkvi⟩ := htarget
  obtain ⟨ku, hku, hkui⟩ := minlevel_le_of_level u i hu
  refine ⟨hadj, ?_⟩
  rintro (hp | hp)
  · have h := hearlier u v kv hp hkv hkvi
    rw [hseen] at h
    contradiction
  · have h := hearlier v u ku hp hku hkui
    rw [seen_comm, hseen] at h
    contradiction

/-- Every guarded scan preserves semantic label soundness. MIN does not need
to know whether its source label is a minlevel or a maxlevel. -/
theorem scanCandidate_labelsSound [DecidableRel G.Adj] (s : State V) (i : Nat) (u v : V)
    (hs : LabelsSound M s) (hc : MinCompleteBelow M i s) :
    LabelsSound M (scanCandidate M i u v s) := by
  unfold scanCandidate
  split
  next hguard =>
    have hu := parityLabel_sound s hs u (i % 2) i hguard.2.1
    unfold scan
    split
    · exact hs
    · split
      next ha =>
        have htrue : admits (s.minLabel v) (i + 1) = true := ha
        have hmin := (minlevel_of_scan_guard u v i hu hguard.1 hguard.2.2
          (admits_semantic_lower_bound s i hc v htrue)).1
        constructor
        · intro w k hw
          change (if w = v then some (i + 1) else s.minLabel w) = some k at hw
          split at hw
          next heq =>
            have hik := Option.some.inj hw
            simpa only [heq, hik] using hmin
          next _ => exact hs.1 w k hw
        · exact hs.2
      next _ =>
        unfold enqueue
        split <;> exact hs
  next _ => exact hs

/-- Labels at completed lower levels survive every scan at the current level. -/
theorem scan_minCompleteBelow (s : State V) (i : Nat) (u v : V)
    (hc : MinCompleteBelow M i s) : MinCompleteBelow M i (scan M i u v s) := by
  intro w k hw hki
  have hlabel := hc w k hw hki
  unfold scan
  split
  · exact hlabel
  · split
    next ha =>
      change (if w = v then some (i + 1) else s.minLabel w) = some k
      by_cases heq : w = v
      · have hvlabel : s.minLabel v = some k := by simpa only [heq] using hlabel
        simp only [hvlabel, admits, decide_eq_true_eq] at ha
        omega
      · simp only [heq, ite_false, hlabel]
    next _ =>
      unfold enqueue
      split <;> exact hlabel

theorem scanCandidate_minCompleteBelow [DecidableRel G.Adj]
    (s : State V) (i : Nat) (u v : V) (hc : MinCompleteBelow M i s) :
    MinCompleteBelow M i (scanCandidate M i u v s) := by
  unfold scanCandidate
  split
  · exact scan_minCompleteBelow s i u v hc
  · exact hc

/-- A complete fold of executable MIN candidates preserves semantic label
soundness and all lower-level assignments, for every candidate order. -/
theorem scanCandidates_preserves [DecidableRel G.Adj]
    (candidates : List (V × V)) (s : State V) (i : Nat)
    (hs : LabelsSound M s) (hc : MinCompleteBelow M i s) :
    LabelsSound M (scanCandidates M i candidates s) ∧
      MinCompleteBelow M i (scanCandidates M i candidates s) := by
  induction candidates generalizing s with
  | nil => exact ⟨hs, hc⟩
  | cons e es ih =>
    exact ih (scanCandidate M i e.1 e.2 s)
      (scanCandidate_labelsSound s i e.1 e.2 hs hc)
      (scanCandidate_minCompleteBelow s i e.1 e.2 hc)

end Search

/-- Semantic level zero is exactly the set of free vertices. -/
theorem minlevel_zero_iff_free (v : V) : minlevel M v = some 0 ↔ M.Free v := by
  constructor
  · intro h
    exact (evenlevel_zero_iff_free M v).1 (level_of_minlevel v 0 h)
  · intro h
    have he := (evenlevel_zero_iff_free M v).2 h
    unfold minlevel
    rw [he]
    cases ho : oddlevel M v <;> simp [levelMin]

namespace Search
variable [DecidableEq V]

omit [DecidableEq V] in
theorem initial_labelsSound (M : Matching G) : LabelsSound M (initial M) := by
  constructor
  · intro v k h
    dsimp only [initial] at h
    split at h
    next hv =>
      have hk : k = 0 := (Option.some.inj h).symm
      subst k
      exact (minlevel_zero_iff_free v).2 hv
    next _ => contradiction
  · intro v k h
    change none = some k at h
    contradiction

omit [DecidableEq V] in
theorem initial_minCompleteBelow (M : Matching G) : MinCompleteBelow M 0 (initial M) := by
  intro v k hk hk0
  have hk' : k = 0 := by omega
  subst k
  exact (initial_free_iff M v).2 ((minlevel_zero_iff_free v).1 hk)

/-- Every candidate enumeration in the initial MIN level assigns only correct
labels, without any completeness hypothesis about the enumeration. -/
theorem initial_scanCandidates_labelsSound [DecidableRel G.Adj]
    (M : Matching G) (candidates : List (V × V)) :
    LabelsSound M (scanCandidates M 0 candidates (initial M)) :=
  (scanCandidates_preserves candidates (initial M) 0
    (initial_labelsSound M) (initial_minCompleteBelow M)).1

end Search
end MaximumMatching

end MinScan
