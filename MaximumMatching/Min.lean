import MaximumMatching.Basic

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
