import MaximumMatching.BridgeSchedule

/-! MAX registers and queues finite-known incident nonprops, including edges
not previously scanned by MIN. The nonprop test uses actual predecessor lists;
its correctness follows from completed MIN levels and assigned-label bounds. -/
namespace MaximumMatching.Search
variable {V : Type} {G : Graph V} {M : Matching G}
variable [DecidableEq V]

def MinLabelsBound (k : Nat) (s : State V) : Prop :=
  ∀ v lo, s.minLabel v = some lo → lo ≤ k

def knownProp (s : State V) (u v : V) : Bool :=
  decide (u ∈ s.predecessors v ∨ v ∈ s.predecessors u)

omit [DecidableEq V] in
theorem parityLabel_has_minLabel (s : State V) (v : V) (parity k : Nat)
    (h : parityLabel s v parity = some k) : ∃ lo, s.minLabel v = some lo := by
  cases hm : s.minLabel v with
  | none => simp [parityLabel, hm] at h
  | some lo => exact ⟨lo, rfl⟩

theorem edgeTenacity_has_minLabels (s : State V) (u v : V) (t : Nat)
    (ht : edgeTenacity M s u v = some t) :
    (∃ lo, s.minLabel u = some lo) ∧ (∃ lo, s.minLabel v = some lo) := by
  let parity := if M.mate u = some v then 1 else 0
  have hh : (do let x ← parityLabel s u parity; let y ← parityLabel s v parity; some (x + y + 1)) = some t := ht
  cases hu : parityLabel s u parity with
  | none => simp [hu] at hh
  | some a =>
    cases hv : parityLabel s v parity with
    | none => simp [hu, hv] at hh
    | some b => exact ⟨parityLabel_has_minLabel s u parity a hu, parityLabel_has_minLabel s v parity b hv⟩

theorem knownProp_sound (s : State V) (hs : PredecessorsSound M s) (u v : V)
    (h : knownProp s u v = true) : PropEdge M u v := by
  have hh : u ∈ s.predecessors v ∨ v ∈ s.predecessors u := by
    simpa only [knownProp, decide_eq_true_eq] using h
  exact hh.elim (fun h => Or.inl (hs u v h)) (fun h => Or.inr (hs v u h))

/-- Finite operational edge tenacity supplies assigned minlabels at both
endpoints. Their bound makes both possible prop orientations already recorded. -/
theorem knownProp_complete_of_finite_edge (s : State V) (k : Nat) (u v : V) (t : Nat)
    (hi : MinInvariant M k s) (hb : MinLabelsBound k s)
    (ht : edgeTenacity M s u v = some t) (hp : PropEdge M u v) : knownProp s u v = true := by
  obtain ⟨⟨a, ha⟩, ⟨b, hv⟩⟩ := edgeTenacity_has_minLabels s u v t ht
  apply decide_eq_true
  rcases hp with hp | hp
  · have hmin := hi.1.1 v b hv
    have hseen := hi.2.2.1 u v b hp hmin (hb v b hv)
    exact Or.inl (hi.2.2.2.1 u v hseen hp).1
  · have hmin := hi.1.1 u a ha
    have hseen := hi.2.2.1 v u a hp hmin (hb u a ha)
    exact Or.inr (hi.2.2.2.1 v u hseen hp).1

/-- The executable MAX check registers a finite-known incident nonprop even
when MIN has not yet scanned it. No semantic Bridge predicate is used as a
runtime guard. -/
def refreshKnownEdge [DecidableRel G.Adj] (M : Matching G) (u v : V) (s : State V) : State V :=
  if G.Adj u v ∧ knownProp s u v = false then
    match edgeTenacity M s u v with
    | none => s
    | some t => enqueue { s with bridges := (u, v) :: s.bridges } u v (some t)
  else s

theorem refreshKnownEdge_minInvariant [DecidableRel G.Adj]
    (s : State V) (k : Nat) (u v : V) (hi : MinInvariant M k s) :
    MinInvariant M k (refreshKnownEdge M u v s) := by
  unfold refreshKnownEdge
  split
  · split <;> exact hi
  · exact hi

theorem refreshKnownEdge_minLabelsBound [DecidableRel G.Adj]
    (s : State V) (k : Nat) (u v : V) (hb : MinLabelsBound k s) :
    MinLabelsBound k (refreshKnownEdge M u v s) := by
  unfold refreshKnownEdge
  split
  · split <;> exact hb
  · exact hb

theorem refreshKnownEdge_edgeTenacity [DecidableRel G.Adj]
    (s : State V) (a b u v : V) :
    edgeTenacity M (refreshKnownEdge M a b s) u v = edgeTenacity M s u v := by
  unfold refreshKnownEdge
  split
  · split <;> rfl
  · rfl

/-- Registration and enqueueing are sound under the completed MIN invariant;
in particular, absence from a predecessor list is not treated as a semantic
nonprop fact without a completeness argument. -/
theorem refreshKnownEdge_classificationSound [DecidableRel G.Adj]
    (s : State V) (k : Nat) (u v : V)
    (hi : MinInvariant M k s) (hb : MinLabelsBound k s) (hc : ClassificationSound M s) :
    ClassificationSound M (refreshKnownEdge M u v s) := by
  unfold refreshKnownEdge
  split
  next hg =>
    split
    · exact hc
    next t ht =>
      have hbridge : Bridge M u v := ⟨hg.1, by
        intro hp
        have hknown := knownProp_complete_of_finite_edge s k u v t hi hb ht hp
        rw [hg.2] at hknown
        contradiction⟩
      refine ⟨hc.1, ?_, enqueue_bucketsSound { s with bridges := (u, v) :: s.bridges }
        hc.2.2 u v hbridge (some t) (fun j hj => ?_)⟩
      · intro a b hmem
        rcases List.mem_cons.mp hmem with he | hold
        · have he' := Prod.mk.inj he
          simpa only [he'.1, he'.2] using hbridge
        · exact hc.2.1 a b hold
      · have he : t = j := Option.some.inj hj
        simpa only [he] using edgeTenacity_sound s hi.1 u v t ht
  next _ => exact hc

theorem refreshKnownEdge_bucket_mono [DecidableRel G.Adj]
    (s : State V) (a b u v : V) (t : Nat) (h : (u, v) ∈ s.bucket t) :
    (u, v) ∈ (refreshKnownEdge M a b s).bucket t := by
  unfold refreshKnownEdge
  split
  · split
    · exact h
    · exact enqueue_bucket_mono _ a b u v _ t h
  · exact h

/-- Any actual finite-known bridge is now queued, without a prior registry
membership or a prior MIN scan assumption. -/
theorem refreshKnownEdge_complete [DecidableRel G.Adj]
    (s : State V) (u v : V) (t : Nat) (hp : PredecessorsSound M s)
    (hb : Bridge M u v) (ht : edgeTenacity M s u v = some t) :
    (u, v) ∈ (refreshKnownEdge M u v s).bucket t := by
  have hk : knownProp s u v = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact hb.2 (knownProp_sound s hp u v h)
  simp [refreshKnownEdge, hb.1, hk, ht, enqueue]

def refreshKnownEdges [DecidableRel G.Adj] (M : Matching G)
    (edges : List (V × V)) (s : State V) : State V :=
  edges.foldl (fun state e => refreshKnownEdge M e.1 e.2 state) s

theorem refreshKnownEdges_minInvariant [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (k : Nat) (hi : MinInvariant M k s) :
    MinInvariant M k (refreshKnownEdges M xs s) := by
  induction xs generalizing s with
  | nil => exact hi
  | cons e es ih => exact ih _ (refreshKnownEdge_minInvariant s k e.1 e.2 hi)

theorem refreshKnownEdges_sound [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (k : Nat)
    (hi : MinInvariant M k s) (hb : MinLabelsBound k s) (hc : ClassificationSound M s) :
    ClassificationSound M (refreshKnownEdges M xs s) := by
  induction xs generalizing s with
  | nil => exact hc
  | cons e es ih =>
    exact ih _ (refreshKnownEdge_minInvariant s k e.1 e.2 hi)
      (refreshKnownEdge_minLabelsBound s k e.1 e.2 hb)
      (refreshKnownEdge_classificationSound s k e.1 e.2 hi hb hc)

theorem refreshKnownEdges_bucket_mono [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (u v : V) (t : Nat) (h : (u, v) ∈ s.bucket t) :
    (u, v) ∈ (refreshKnownEdges M xs s).bucket t := by
  induction xs generalizing s with
  | nil => exact h
  | cons e es ih => exact ih _ (refreshKnownEdge_bucket_mono s e.1 e.2 u v t h)

theorem refreshKnownEdges_complete [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (k : Nat) (u v : V) (t : Nat)
    (hi : MinInvariant M k s) (hb : Bridge M u v) (hmem : (u, v) ∈ xs)
    (ht : edgeTenacity M s u v = some t) :
    (u, v) ∈ (refreshKnownEdges M xs s).bucket t := by
  induction xs generalizing s with
  | nil => simp at hmem
  | cons e es ih =>
    rcases List.mem_cons.mp hmem with he | he
    · subst e
      exact refreshKnownEdges_bucket_mono es (refreshKnownEdge M u v s) u v t
        (refreshKnownEdge_complete s u v t hi.2.2.2.2 hb ht)
    · exact ih _ (refreshKnownEdge_minInvariant s k e.1 e.2 hi) he
        ((refreshKnownEdge_edgeTenacity s e.1 e.2 u v).trans ht)

/-- Enumerate incident vertex pairs and refresh their known bridge labels
for the MAX step. -/
def refreshIncidentAll {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (w : Fin n) (s : State (Fin n)) : State (Fin n) :=
  refreshKnownEdges M ((allCandidates n).filter fun e => decide (e.1 = w ∨ e.2 = w)) s

theorem refreshIncidentAll_sound {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (w : Fin n) (s : State (Fin n)) (k : Nat)
    (hi : MinInvariant M k s) (hb : MinLabelsBound k s) (hc : ClassificationSound M s) :
    ClassificationSound M (refreshIncidentAll M w s) :=
  refreshKnownEdges_sound _ s k hi hb hc

theorem refreshIncidentAll_complete {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (w u v : Fin n) (s : State (Fin n)) (k t : Nat)
    (hi : MinInvariant M k s) (hb : Bridge M u v) (hincident : u = w ∨ v = w)
    (ht : edgeTenacity M s u v = some t) :
    (u, v) ∈ (refreshIncidentAll M w s).bucket t := by
  apply refreshKnownEdges_complete _ s k u v t hi hb
  · exact List.mem_filter.mpr ⟨mem_allCandidates u v, by simpa only [decide_eq_true_eq] using hincident⟩
  · exact ht

omit [DecidableEq V] in
theorem initial_minLabelsBound (M : Matching G) : MinLabelsBound 0 (initial M) := by
  intro v lo h
  change (if M.mate v = none then some 0 else none) = some lo at h
  split at h
  · have he := Option.some.inj h
    omega
  · contradiction

theorem scan_minLabelsBound (s : State V) (i : Nat) (u v : V)
    (h : MinLabelsBound (i + 1) s) : MinLabelsBound (i + 1) (scan M i u v s) := by
  unfold scan
  split
  · exact h
  · split
    · intro w lo hw
      change (if w = v then some (i + 1) else s.minLabel w) = some lo at hw
      split at hw
      · have he := Option.some.inj hw; omega
      · exact h w lo hw
    · unfold enqueue; split <;> exact h

theorem scanCandidate_minLabelsBound [DecidableRel G.Adj] (s : State V) (i : Nat) (u v : V)
    (h : MinLabelsBound (i + 1) s) : MinLabelsBound (i + 1) (scanCandidate M i u v s) := by
  unfold scanCandidate
  split
  · exact scan_minLabelsBound s i u v h
  · exact h

theorem scanCandidates_minLabelsBound [DecidableRel G.Adj] (xs : List (V × V)) (s : State V)
    (i : Nat) (h : MinLabelsBound (i + 1) s) :
    MinLabelsBound (i + 1) (scanCandidates M i xs s) := by
  induction xs generalizing s with
  | nil => exact h
  | cons e es ih => exact ih _ (scanCandidate_minLabelsBound s i e.1 e.2 h)

theorem assignMax_minLabelsBound (s : State V) (k t : Nat) (v : V) (h : MinLabelsBound k s) :
    MinLabelsBound k (assignMax s t v) := by
  unfold assignMax
  split <;> exact h

theorem assignMax_classificationSound (s : State V) (t : Nat) (v : V) (h : ClassificationSound M s) :
    ClassificationSound M (assignMax s t v) := by
  unfold assignMax
  split <;> exact h

theorem refreshKnownEdge_labels [DecidableRel G.Adj] (s : State V) (u v w : V) :
    (refreshKnownEdge M u v s).minLabel w = s.minLabel w ∧
      (refreshKnownEdge M u v s).maxLabel w = s.maxLabel w := by
  unfold refreshKnownEdge
  split
  · split <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem refreshKnownEdges_labels [DecidableRel G.Adj] (xs : List (V × V)) (s : State V) (w : V) :
    (refreshKnownEdges M xs s).minLabel w = s.minLabel w ∧
      (refreshKnownEdges M xs s).maxLabel w = s.maxLabel w := by
  induction xs generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons e es ih =>
    have hh := ih (refreshKnownEdge M e.1 e.2 s)
    have he := refreshKnownEdge_labels (M := M) s e.1 e.2 w
    exact ⟨hh.1.trans he.1, hh.2.trans he.2⟩

/-- The source MAX vertex step: assign maxlevel, then reconsider all incident
finite-known nonprops exactly when the assigned minlevel has odd parity. -/
def maxProcessVertex {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (v : Fin n) (s : State (Fin n)) : State (Fin n) :=
  let assigned := assignMax s (2 * i + 1) v
  match assigned.minLabel v with
  | none => assigned
  | some lo => if lo % 2 = 1 then refreshIncidentAll M v assigned else assigned

theorem maxProcessVertex_correct {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (v : Fin n) (s : State (Fin n))
    (hi : MinInvariant M (i + 1) s) (hb : MinLabelsBound (i + 1) s)
    (hc : ClassificationSound M s) (ht : tenacity M v = some (2 * i + 1)) :
    MinInvariant M (i + 1) (maxProcessVertex M i v s) ∧
      MinLabelsBound (i + 1) (maxProcessVertex M i v s) ∧
      ClassificationSound M (maxProcessVertex M i v s) ∧
      (maxProcessVertex M i v s).maxLabel v = maxlevel M v := by
  let assigned := assignMax s (2 * i + 1) v
  have hia : MinInvariant M (i + 1) assigned := assignMax_minInvariant s (i + 1) (2 * i + 1) v hi ht
  have hba : MinLabelsBound (i + 1) assigned := assignMax_minLabelsBound s (i + 1) (2 * i + 1) v hb
  have hca : ClassificationSound M assigned := assignMax_classificationSound s (2 * i + 1) v hc
  have hset : assigned.maxLabel v = maxlevel M v :=
    assignMax_correct s i v (fun w k hw hk => hi.2.1 w k hw (by omega)) ht
  let P : State (Fin n) → Prop := fun state =>
    MinInvariant M (i + 1) state ∧ MinLabelsBound (i + 1) state ∧
      ClassificationSound M state ∧ state.maxLabel v = maxlevel M v
  change P (match assigned.minLabel v with
    | none => assigned
    | some lo => if lo % 2 = 1 then refreshIncidentAll M v assigned else assigned)
  cases hlo : assigned.minLabel v with
  | none => exact ⟨hia, hba, hca, hset⟩
  | some lo =>
    by_cases hp : lo % 2 = 1
    · simp only [hp, ite_true]
      have hlabels := refreshKnownEdges_labels (M := M)
        ((allCandidates n).filter fun e => decide (e.1 = v ∨ e.2 = v)) assigned
      refine ⟨refreshKnownEdges_minInvariant _ assigned (i + 1) hia, ?_,
        refreshIncidentAll_sound M v assigned (i + 1) hia hba hca, (hlabels v).2.trans hset⟩
      intro w k hw
      apply hba w k
      exact (hlabels w).1.symm.trans hw
    · simp only [hp, ite_false]
      exact ⟨hia, hba, hca, hset⟩

/-- A real inner support vertex activates the incident refresh, so any bridge
whose tenacity becomes known at this assignment is enqueued immediately. -/
theorem maxProcessVertex_queues_incident {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (w u v : Fin n) (s : State (Fin n)) (t : Nat)
    (hi : MinInvariant M (i + 1) s) (hw : Inner M w)
    (hwt : tenacity M w = some (2 * i + 1)) (hbridge : Bridge M u v)
    (hincident : u = w ∨ v = w)
    (ht : edgeTenacity M (assignMax s (2 * i + 1) w) u v = some t) :
    (u, v) ∈ (maxProcessVertex M i w s).bucket t := by
  obtain ⟨e, o, he, ho, _, hop, _⟩ := finite_levels_of_tenacity w (2 * i + 1) hwt
  obtain ⟨j, hj, _, hmin⟩ := inner_oddlevel_lt_evenlevel w e he hw
  have hjo : j = o := Option.some.inj (hj.symm.trans ho)
  have hjbound : j ≤ i := by
    obtain ⟨k, hk, hki⟩ := minlevel_le_half_tenacity w i hwt
    have hkj := Option.some.inj (hk.symm.trans hmin)
    omega
  have hlabel : s.minLabel w = some j := hi.2.1 w j hmin (by omega)
  have hpar : j % 2 = 1 := by omega
  have hassigned : (assignMax s (2 * i + 1) w).minLabel w = some j := by
    simp [assignMax, hlabel]
  simp only [maxProcessVertex, hassigned, hpar, ite_true]
  exact refreshIncidentAll_complete M w u v _ (i + 1) t
    (assignMax_minInvariant s (i + 1) (2 * i + 1) w hi hwt) hbridge hincident ht

end MaximumMatching.Search
