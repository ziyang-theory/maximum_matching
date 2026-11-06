import MaximumMatching.DDFSPaths

/-! Recursive removal of dead nonbottom vertices in the finite layered
predecessor graph. This is the predecessor-pruning operation of source §4.5.2:
vertices removed by a recovered augmentation are omitted from the input live
list, and each subsequent removal has no live predecessor. The implementation
uses finite list scans; no linear-time representation cost is asserted. -/
namespace MaximumMatching.DDFS.RecursiveRemoval
variable {n : Nat} (H : LayeredGraph (Fin n)) [DecidableRel H.Edge]

/-- A nonbottom live vertex can be removed exactly when it has no live
outgoing predecessor. Bottom vertices are retained by this operation. -/
def Dead (live : List (Fin n)) (v : Fin n) : Prop :=
  H.level v ≠ 0 ∧ ∀ w, w ∈ live → ¬ H.Edge v w

instance (live : List (Fin n)) (v : Fin n) : Decidable (Dead H live v) :=
  inferInstanceAs (Decidable (_ ∧ _))

def eraseVertex (live : List (Fin n)) (v : Fin n) : List (Fin n) :=
  live.filter fun w => decide (w ≠ v)

/-- Repeatedly remove the first dead vertex. Filtering also handles repeated
input vertices; termination counts the strictly decreasing live list. -/
def prune (live : List (Fin n)) : List (Fin n) :=
  match _hfind : live.find? (fun v => decide (Dead H live v)) with
  | none => live
  | some v => prune (eraseVertex live v)
termination_by live.length
decreasing_by
  first | unfold eraseVertex | skip
  apply List.length_filter_lt_length_iff_exists.mpr
  refine ⟨_, List.mem_of_find?_eq_some (by assumption), ?_⟩
  simp

theorem prune_subset (live : List (Fin n)) (v : Fin n) (hv : v ∈ prune H live) : v ∈ live := by
  rw [prune] at hv
  split at hv
  · exact hv
  · exact (List.mem_filter.mp (show v ∈ (live.filter fun w => decide (w ≠ _)) from prune_subset _ v hv)).1
termination_by live.length
decreasing_by
  first | unfold eraseVertex | skip
  apply List.length_filter_lt_length_iff_exists.mpr
  refine ⟨_, List.mem_of_find?_eq_some (by assumption), ?_⟩
  simp

/-- The returned graph has no nonbottom dead end. -/
theorem prune_stable (live : List (Fin n)) (v : Fin n) (hv : v ∈ prune H live) :
    ¬ Dead H (prune H live) v := by
  rw [prune] at hv ⊢
  split at *
  · rename_i hfind
    have hh := (List.find?_eq_none.mp hfind) v hv
    simpa only [decide_eq_true_eq] using hh
  · exact prune_stable _ v hv
termination_by live.length
decreasing_by
  first | unfold eraseVertex | skip
  apply List.length_filter_lt_length_iff_exists.mpr
  refine ⟨_, List.mem_of_find?_eq_some (by assumption), ?_⟩
  simp

omit [DecidableRel H.Edge] in
/-- Removing a dead vertex cannot hit a live path reaching bottom. -/
theorem dead_not_on_bottom_path (live : List (Fin n)) (v : Fin n)
    (hdead : Dead H live v) (p : Path H) (hbottom : H.level p.last = 0)
    (hlive : ∀ j, p.vertex j ∈ live) : ¬ p.Contains v := by
  rintro ⟨j, hj⟩
  by_cases hlast : j.val = p.length
  · have he : j = ⟨p.length, by omega⟩ := Fin.ext hlast
    have hv : p.last = v := by simpa only [he, Path.last] using hj
    exact hdead.1 (hv ▸ hbottom)
  · have hjlt : j.val < p.length := by have := j.isLt; omega
    exact hdead.2 (p.vertex ⟨j.val + 1, by omega⟩) (hlive _) (by
      rw [← hj]
      exact p.adjacent ⟨j.val, hjlt⟩)

/-- Every initial path avoiding the supplied removals survives all recursive
pruning, with every one of its original vertices retained. -/
theorem prune_preserves_bottom_path (live : List (Fin n)) (p : Path H)
    (hbottom : H.level p.last = 0) (hlive : ∀ j, p.vertex j ∈ live) :
    ∀ j, p.vertex j ∈ prune H live := by
  rw [prune]
  split
  · exact hlive
  · rename_i v hfind
    have hdead : Dead H live v := by simpa only [decide_eq_true_eq] using List.find?_some hfind
    apply prune_preserves_bottom_path _ p hbottom
    intro j
    apply List.mem_filter.mpr
    refine ⟨hlive j, ?_⟩
    simp only [decide_eq_true_eq]
    intro he
    exact dead_not_on_bottom_path H live v hdead p hbottom hlive ⟨j, he⟩
termination_by live.length
decreasing_by
  first | unfold eraseVertex | skip
  apply List.length_filter_lt_length_iff_exists.mpr
  refine ⟨_, List.mem_of_find?_eq_some (by assumption), ?_⟩
  simp

/-- Strict layer descent and the returned successor invariant construct a
bottom path from each surviving vertex, entirely within the returned list. -/
theorem prune_reaches_bottom (live : List (Fin n)) (v : Fin n) (hv : v ∈ prune H live) :
    ∃ p : Path H, p.first = v ∧ H.level p.last = 0 ∧ ∀ j, p.vertex j ∈ prune H live := by
  classical
  generalize hlevel : H.level v = k
  induction k using Nat.strongRecOn generalizing v with
  | ind k ih =>
    by_cases hz : H.level v = 0
    · exact ⟨Path.trivial H v, rfl, hz, fun _ => hv⟩
    · have hex : ∃ w, w ∈ prune H live ∧ H.Edge v w := by
        apply Classical.byContradiction
        intro hn
        apply prune_stable H live v hv
        exact ⟨hz, fun w hw he => hn ⟨w, hw, he⟩⟩
      obtain ⟨w, hw, he⟩ := hex
      obtain ⟨p, hpf, hpb, hplive⟩ := ih (H.level w) (by have := H.decreases he; omega) w hw rfl
      have hedge : H.Edge v p.first := by rw [hpf]; exact he
      refine ⟨p.prepend v hedge, rfl, ?_, ?_⟩
      · simpa only [Path.prepend_last] using hpb
      · intro j
        rcases (Path.contains_prepend_iff v p hedge ((p.prepend v hedge).vertex j)).1 ⟨j, rfl⟩ with hj | hj
        · rw [hj]; exact hv
        · obtain ⟨a, ha⟩ := hj
          rw [← ha]
          exact hplive a

/-- The computed survivors are exactly the vertices that can reach bottom
without passing through an initially removed vertex. -/
theorem mem_prune_iff (live : List (Fin n)) (v : Fin n) :
    v ∈ prune H live ↔ ∃ p : Path H, p.first = v ∧ H.level p.last = 0 ∧
      ∀ j, p.vertex j ∈ live := by
  constructor
  · intro hv
    obtain ⟨p, hpf, hpb, hplive⟩ := prune_reaches_bottom H live v hv
    exact ⟨p, hpf, hpb, fun j => prune_subset H live _ (hplive j)⟩
  · rintro ⟨p, hpf, hpb, hplive⟩
    have hh := prune_preserves_bottom_path H live p hpb hplive ⟨0, by omega⟩
    change p.first ∈ prune H live at hh
    rwa [hpf] at hh

/-- Restrict edges to live vertices. Removed vertices are isolated at layer
zero; searches beginning at live vertices stay in the genuine live subgraph. -/
def restricted (live : List (Fin n)) : LayeredGraph (Fin n) where
  Edge u v := u ∈ live ∧ v ∈ live ∧ H.Edge u v
  level v := if v ∈ live then H.level v else 0
  decreases := by
    intro u v he
    simpa only [ite_eq_left he.1, ite_eq_left he.2.1] using H.decreases he.2.2

instance (live : List (Fin n)) : DecidableRel (restricted H live).Edge :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Retain the original vertices of a live path in the restricted graph. -/
def restrictPath (live : List (Fin n)) (p : Path H) (hlive : ∀ j, p.vertex j ∈ live) :
    Path (restricted H live) where
  length := p.length
  vertex := p.vertex
  adjacent j := ⟨hlive _, hlive _, p.adjacent j⟩

omit [DecidableRel H.Edge] in
/-- Every path started at a live vertex remains live; the artificial isolated
bottom vertices cannot appear in any such search. -/
theorem restricted_path_live (live : List (Fin n)) (p : Path (restricted H live))
    (hfirst : p.first ∈ live) (j : Fin (p.length + 1)) : p.vertex j ∈ live := by
  by_cases hj : j.val = 0
  · have he : j = ⟨0, by omega⟩ := Fin.ext hj
    simpa only [he, Path.first] using hfirst
  · have hh := (p.adjacent ⟨j.val - 1, by omega⟩).2.1
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j.val), Fin.eta] using hh

/-- The actual pruned graph meets DDFS's bottom-reachability requirement. -/
theorem prune_reachBottom (live : List (Fin n)) : ReachBottom (restricted H (prune H live)) := by
  intro v
  by_cases hv : v ∈ prune H live
  · obtain ⟨p, hpf, hpb, hplive⟩ := prune_reaches_bottom H live v hv
    refine ⟨restrictPath H (prune H live) p hplive, hpf, ?_⟩
    change (if p.last ∈ prune H live then H.level p.last else 0) = 0
    have hl : p.last ∈ prune H live := hplive ⟨p.length, by omega⟩
    rw [ite_eq_left hl]
    exact hpb
  · refine ⟨Path.trivial (restricted H (prune H live)) v, rfl, ?_⟩
    change (if v ∈ prune H live then H.level v else 0) = 0
    exact ite_eq_right hv

/-- Remove the supplied path vertices, then perform the recursive predecessor
cleanup. The input may already omit vertices removed by earlier paths. -/
def remove (live forbidden : List (Fin n)) : List (Fin n) :=
  prune H (live.filter fun v => decide (v ∉ forbidden))

theorem remove_avoids (live forbidden : List (Fin n)) (v : Fin n)
    (hv : v ∈ remove H live forbidden) : v ∈ live ∧ v ∉ forbidden := by
  have hh := prune_subset H _ v hv
  simpa only [List.mem_filter, decide_eq_true_eq] using hh

/-- Recursive cleanup preserves any original bottom path disjoint from all
explicitly removed vertices. This is the local safety property used when
continuing DDFS after a recovered augmenting path is deleted. -/
theorem remove_preserves_bottom_path (live forbidden : List (Fin n)) (p : Path H)
    (hbottom : H.level p.last = 0) (hlive : ∀ j, p.vertex j ∈ live)
    (havoid : ∀ j, p.vertex j ∉ forbidden) :
    ∀ j, p.vertex j ∈ remove H live forbidden := by
  apply prune_preserves_bottom_path H _ p hbottom
  intro j
  exact List.mem_filter.mpr ⟨hlive j, by simpa only [decide_eq_true_eq] using havoid j⟩

theorem remove_reachBottom (live forbidden : List (Fin n)) :
    ReachBottom (restricted H (remove H live forbidden)) :=
  prune_reachBottom H _

end MaximumMatching.DDFS.RecursiveRemoval
