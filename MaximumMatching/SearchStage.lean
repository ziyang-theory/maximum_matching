import MaximumMatching.BridgeComplete

/-! Initialized MIN/MAX stage invariants for the concrete local operations.
The complete vertex list at the current tenacity remains a support-discovery
obligation. Given that list, its labels and all bridge-refresh events are
executed and verified here; no current-stage label correctness is assumed. -/
namespace MaximumMatching.Search
variable {V : Type} {G : Graph V} {M : Matching G}
variable [DecidableEq V]

structure StageState (M : Matching G) (level cutoff : Nat) (s : State V) : Prop where
  min : MinInvariant M level s
  minBound : MinLabelsBound level s
  scanned : ScannedBefore M level s
  classification : ClassificationSound M s
  maxHasMin : MaxLabelsHaveMin s
  pending : UnmatchedPending M level s
  maxComplete : MaxCompleteBelowTenacity M cutoff s

/-- Before search level i, all smaller eligible tenacities have been handled. -/
def StageInvariant (M : Matching G) (i : Nat) (s : State V) : Prop :=
  StageState M i (2 * i + 1) s

theorem initial_stageInvariant (M : Matching G) : StageInvariant M 0 (initial M) := by
  refine ⟨initial_minInvariant M, initial_minLabelsBound M, initial_scannedBefore M,
    initial_classificationSound M, initial_maxLabelsHaveMin M, initial_unmatchedPending M, ?_⟩
  intro v t ht hlt
  have hp := tenacity_odd M v t ht
  omega

theorem scanCandidates_maxLabel [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (i : Nat) (v : V) :
    (scanCandidates M i xs s).maxLabel v = s.maxLabel v := by
  induction xs generalizing s with
  | nil => rfl
  | cons e es ih => exact (ih _).trans (scanCandidate_preserves_maxLabel s i e.1 e.2 v)

theorem scanCandidates_maxLabelsHaveMin [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (i : Nat) (hi : MinInvariant M i s) (hm : MaxLabelsHaveMin s) :
    MaxLabelsHaveMin (scanCandidates M i xs s) := by
  induction xs generalizing s with
  | nil => exact hm
  | cons e es ih =>
    exact ih _ (scanCandidate_minInvariant s i e.1 e.2 hi)
      (scanCandidate_maxLabelsHaveMin s i e.1 e.2 hi hm)

/-- Actual exhaustive MIN advances all minlevel, predecessor, classification,
scan-provenance, and pending-bridge invariants to the next boundary. -/
theorem scanLevel_stageState {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (s : State (Fin n)) (h : StageInvariant M i s) :
    StageState M (i + 1) (2 * i + 1) (scanLevel M i s) := by
  have hf := frontierAvailable_of_prior_levels s i h.min.2.1 h.maxComplete
  refine ⟨(scanLevel_complete M i s h.min hf).1,
    scanCandidates_minLabelsBound (allCandidates n) s i (fun v k hk => Nat.le_trans (h.minBound v k hk) (by omega)),
    scanLevel_scannedBefore M s i h.min h.scanned,
    scanCandidates_classificationSound (allCandidates n) s i h.min h.classification,
    scanCandidates_maxLabelsHaveMin (allCandidates n) s i h.min h.maxHasMin,
    scanLevel_unmatchedPending M s i h.min hf h.maxHasMin h.scanned h.pending, ?_⟩
  intro v t ht hlt
  exact (scanCandidates_maxLabel (allCandidates n) s i v).trans (h.maxComplete v t ht hlt)

/-- Task 2 at the explicit stage boundary, including all matched, outer,
inner, and mixed bridge cases. -/
theorem scanLevel_stage_bucket_complete {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (s : State (Fin n)) (h : StageInvariant M i s)
    (u v : Fin n) (hb : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (2 * i + 1)) :
    EdgeInBucket (scanLevel M i s) (2 * i + 1) u v :=
  scanLevel_current_bucket_complete M s i h.min h.maxComplete h.maxHasMin h.scanned h.pending u v hb ht

theorem assignMax_maxLabelsHaveMin (s : State V) (t : Nat) (u : V) (h : MaxLabelsHaveMin s) :
    MaxLabelsHaveMin (assignMax s t u) := by
  unfold assignMax
  split
  · exact h
  next lo hlo =>
    intro v k hv
    change (if v = u then some (t - lo) else s.maxLabel v) = some k at hv
    split at hv
    next he => exact ⟨lo, by simpa only [he] using hlo⟩
    next _ => exact h v k hv

theorem maxProcessVertex_labels {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (u v : Fin n) (s : State (Fin n)) :
    (maxProcessVertex M i u s).minLabel v = s.minLabel v ∧
      (maxProcessVertex M i u s).maxLabel v = (assignMax s (2 * i + 1) u).maxLabel v := by
  have hmin := assignMax_minLabel s (2 * i + 1) u v
  unfold maxProcessVertex
  dsimp only
  split
  · exact ⟨hmin, rfl⟩
  · split
    · have hh := refreshKnownEdges_labels (M := M)
        ((allCandidates n).filter fun e => decide (e.1 = u ∨ e.2 = u)) (assignMax s (2 * i + 1) u) v
      exact ⟨hh.1.trans hmin, hh.2⟩
    · exact ⟨hmin, rfl⟩

theorem refreshKnownEdges_scanned [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) : (refreshKnownEdges M xs s).scanned = s.scanned := by
  induction xs generalizing s with
  | nil => rfl
  | cons e es ih =>
    apply Eq.trans (ih _)
    unfold refreshKnownEdge
    dsimp only
    split
    · split <;> rfl
    · rfl

theorem maxProcessVertex_scanned {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (u : Fin n) (s : State (Fin n)) :
    (maxProcessVertex M i u s).scanned = s.scanned := by
  have ha : (assignMax s (2 * i + 1) u).scanned = s.scanned := by
    unfold assignMax; split <;> rfl
  unfold maxProcessVertex
  dsimp only
  split
  · exact ha
  · split
    · exact (refreshKnownEdges_scanned _ _).trans ha
    · exact ha

theorem maxProcessVertex_preserves_known_maxLabel {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (u v : Fin n) (s : State (Fin n)) (k : Nat)
    (hs : LabelsSound M s) (ht : tenacity M u = some (2 * i + 1)) (hv : s.maxLabel v = some k) :
    (maxProcessVertex M i u s).maxLabel v = some k :=
  (maxProcessVertex_labels M i u v s).2.trans
    (assignMax_preserves_known_maxLabel s (2 * i + 1) u v k hs ht hv)

omit [DecidableEq V] in
/-- A genuine finite-tenacity vertex has a finite maximum level. -/
theorem finite_maxlevel (v : V) (t : Nat) (ht : tenacity M v = some t) :
    ∃ k, maxlevel M v = some k := by
  obtain ⟨e, o, he, ho, _, _, _⟩ := finite_levels_of_tenacity v t ht
  exact ⟨max e o, by simp [maxlevel, he, ho, levelMax]⟩

/-- One actual MAX vertex step preserves every stage boundary invariant and
all earlier maxlevel assignments, while completing the current vertex. -/
theorem maxProcessVertex_stageState {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i cutoff : Nat) (u : Fin n) (s : State (Fin n))
    (h : StageState M (i + 1) cutoff s) (ht : tenacity M u = some (2 * i + 1)) :
    StageState M (i + 1) cutoff (maxProcessVertex M i u s) := by
  obtain ⟨hmin, hbound, hclass, _⟩ := maxProcessVertex_correct M i u s h.min h.minBound h.classification ht
  refine ⟨hmin, hbound, ?_, hclass, ?_,
    maxProcessVertex_unmatchedPending M s i (i + 1) u h.min ht h.pending, ?_⟩
  · intro a b hmem
    rw [maxProcessVertex_scanned] at hmem
    exact h.scanned a b hmem
  · intro v k hv
    have hlabels := maxProcessVertex_labels M i u v s
    have ha : (assignMax s (2 * i + 1) u).maxLabel v = some k := hlabels.2.symm.trans hv
    obtain ⟨lo, hlo⟩ := assignMax_maxLabelsHaveMin s (2 * i + 1) u h.maxHasMin v k ha
    exact ⟨lo, hlabels.1.trans ((assignMax_minLabel s (2 * i + 1) u v).symm.trans hlo)⟩
  · intro v t hvt hlt
    obtain ⟨k, hk⟩ := finite_maxlevel v t hvt
    exact (maxProcessVertex_preserves_known_maxLabel M i u v s k h.min.1 ht
      ((h.maxComplete v t hvt hlt).trans hk)).trans hk.symm

/-- Execute the concrete MAX label/incident-refresh step on a finite list. -/
def maxProcessVertices {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (vs : List (Fin n)) (s : State (Fin n)) : State (Fin n) :=
  vs.foldl (fun state v => maxProcessVertex M i v state) s

theorem maxProcessVertices_stageState {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i cutoff : Nat) (vs : List (Fin n)) (s : State (Fin n))
    (h : StageState M (i + 1) cutoff s) (ht : ∀ v ∈ vs, tenacity M v = some (2 * i + 1)) :
    StageState M (i + 1) cutoff (maxProcessVertices M i vs s) := by
  induction vs generalizing s with
  | nil => exact h
  | cons v vs ih =>
    exact ih _ (maxProcessVertex_stageState M i cutoff v s h (ht v (by simp)))
      (fun w hw => ht w (List.mem_cons_of_mem _ hw))

theorem maxProcessVertices_preserves_known_maxLabel {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i cutoff : Nat) (vs : List (Fin n)) (s : State (Fin n))
    (h : StageState M (i + 1) cutoff s) (ht : ∀ v ∈ vs, tenacity M v = some (2 * i + 1))
    (v : Fin n) (k : Nat) (hv : s.maxLabel v = some k) :
    (maxProcessVertices M i vs s).maxLabel v = some k := by
  induction vs generalizing s with
  | nil => exact hv
  | cons u us ih =>
    exact ih _ (maxProcessVertex_stageState M i cutoff u s h (ht u (by simp)))
      (fun w hw => ht w (List.mem_cons_of_mem _ hw))
      (maxProcessVertex_preserves_known_maxLabel M i u v s k h.min.1 (ht u (by simp)) hv)

/-- Every listed vertex receives its correct maxlevel, including after later
assignments and queue refreshes; duplicate support-list entries are allowed. -/
theorem maxProcessVertices_member_correct {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i cutoff : Nat) (vs : List (Fin n)) (s : State (Fin n))
    (h : StageState M (i + 1) cutoff s) (ht : ∀ v ∈ vs, tenacity M v = some (2 * i + 1))
    (v : Fin n) (hv : v ∈ vs) :
    (maxProcessVertices M i vs s).maxLabel v = maxlevel M v := by
  induction vs generalizing s with
  | nil => simp at hv
  | cons u us ih =>
    have hut := ht u (by simp)
    have hs := maxProcessVertex_stageState M i cutoff u s h hut
    rcases List.mem_cons.mp hv with he | he
    · subst u
      obtain ⟨k, hk⟩ := finite_maxlevel v (2 * i + 1) hut
      have hset := (maxProcessVertex_correct M i v s h.min h.minBound h.classification hut).2.2.2
      exact (maxProcessVertices_preserves_known_maxLabel M i cutoff us _ hs
        (fun w hw => ht w (List.mem_cons_of_mem _ hw)) v k (hset.trans hk)).trans hk.symm
    · exact ih _ hs (fun w hw => ht w (List.mem_cons_of_mem _ hw)) he

/-- A complete current-tenacity vertex list advances the stage induction.
The list is an explicit input: concrete DDFS support discovery must construct
it. This theorem executes MIN, assignments, and all incident refreshes itself. -/
theorem searchLevel_stageInvariant {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (i : Nat) (vs : List (Fin n)) (s : State (Fin n))
    (h : StageInvariant M i s)
    (hsound : ∀ v ∈ vs, tenacity M v = some (2 * i + 1))
    (hcover : ∀ v, tenacity M v = some (2 * i + 1) → v ∈ vs) :
    StageInvariant M (i + 1) (maxProcessVertices M i vs (scanLevel M i s)) := by
  have hmin := scanLevel_stageState M i s h
  have hout := maxProcessVertices_stageState M i (2 * i + 1) vs _ hmin hsound
  refine ⟨hout.min, hout.minBound, hout.scanned, hout.classification, hout.maxHasMin, hout.pending, ?_⟩
  intro v t ht hlt
  by_cases hprev : t < 2 * i + 1
  · exact hout.maxComplete v t ht hprev
  · have hodd := tenacity_odd M v t ht
    have heq : t = 2 * i + 1 := by omega
    subst t
    exact maxProcessVertices_member_correct M i (2 * i + 1) vs _ hmin hsound v (hcover v ht)

end MaximumMatching.Search
