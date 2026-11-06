import MaximumMatching.DDFSBud
import MaximumMatching.DDFSGeometry
import MaximumMatching.PetalRecord

section PetalPathTransport

/-! Transport actual old root paths through a recorded petal contraction.
Bottleneck semantics proves the region is closed under edges except at its
boundary. Mapping roots then collapses only zero steps and preserves all images. -/
namespace MaximumMatching.Search.PetalRecord
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

/-- Any outgoing edge from a selected non-bottleneck vertex stays selected.
This follows from the actual all-path bottleneck, not a closure certificate. -/
theorem selected_edge_closed (R : PetalRecord M) {v w : Fin n}
    (hv : R.selected v) (hne : v ≠ R.bottleneck)
    (he : (predecessorGraph R.prior R.forest R.invariant).Edge v w) : R.selected w := by
  have hlevel := DDFS.onRootTo_level_gt ((R.region v).1 hv) hne
  obtain ⟨p, hp, hpb, i, hiv⟩ := (R.region v).1 hv
  let a := p.take i.val (by omega)
  have haf : a.first = p.first := rfl
  have hal : a.last = v := hiv
  obtain ⟨z, hzf, hz0⟩ := R.invariant.reachBottom w
  have hze : (predecessorGraph R.prior R.forest R.invariant).Edge v z.first := by
    rw [hzf]
    exact he
  let q := z.prepend v hze
  have hjoin : a.last = q.first := hal
  have hfull : (a.append q hjoin).ToBottom (R.forest.root R.left) ∨
      (a.append q hjoin).ToBottom (R.forest.root R.right) := by
    rcases hp with hp | hp
    · exact Or.inl ⟨(a.append_first q hjoin).trans (haf.trans hp),
        by rw [a.append_last]; exact hz0⟩
    · exact Or.inr ⟨(a.append_first q hjoin).trans (haf.trans hp),
        by rw [a.append_last]; exact hz0⟩
  have hbfull := R.highest.1 (a.append q hjoin) hfull
  have hbq : q.Contains R.bottleneck := by
    rcases (a.contains_append_iff q hjoin R.bottleneck).1 hbfull with hba | hbq
    · have hlow := a.last_level_le hba
      rw [hal] at hlow
      omega
    · exact hbq
  have hbz : z.Contains R.bottleneck := by
    rcases (z.contains_prepend_iff v hze R.bottleneck).1 hbq with hb | hbz
    · exact False.elim (hne hb.symm)
    · exact hbz
  obtain ⟨j, hj⟩ := hbz
  let tail := z.take j.val (by omega)
  have hte : (predecessorGraph R.prior R.forest R.invariant).Edge v tail.first := hze
  let branch := tail.prepend v hte
  have hjn : a.last = branch.first := hal
  apply (R.region w).2
  refine ⟨a.append branch hjn, ?_, ?_, ?_⟩
  · rw [a.append_first]
    exact hp
  · rw [a.append_last]
    exact (tail.prepend_last v hte).trans hj
  · apply (a.contains_append_iff branch hjn w).2
    right
    apply (tail.contains_prepend_iff v hte w).2
    right
    exact hzf ▸ tail.contains_first

/-- An original predecessor edge continues to point to the new root of its
old target. The source here is the unchanged original vertex. -/
theorem after_edge_target (R : PetalRecord M) {v w : Fin n}
    (he : (predecessorGraph R.prior R.forest R.invariant).Edge v w) :
    (predecessorGraph R.prior R.after R.after_invariant).Edge v (R.after.root w) := by
  obtain ⟨u, hu, huw⟩ := List.mem_map.mp he.2
  refine ⟨he.1, List.mem_map.mpr ⟨u, hu, ?_⟩⟩
  exact R.forest.mergeManyInto_root_congr R.trees.vertices R.bottleneck u w
    (by rw [← huw]; exact (R.forest.root_idempotent u).symm)

/-- An old fixed-root edge either collapses into one new class or remains an
actual edge between its new endpoint roots. -/
theorem after_edge_eq_or_edge (R : PetalRecord M) {v w : Fin n}
    (he : (predecessorGraph R.prior R.forest R.invariant).Edge v w)
    (hvfix : R.forest.root v = v) :
    R.after.root v = R.after.root w ∨
      (predecessorGraph R.prior R.after R.after_invariant).Edge (R.after.root v) (R.after.root w) := by
  by_cases hv : R.selected v
  · by_cases hvb : v = R.bottleneck
    · right
      have hvafter : R.after.root v = v := by
        rw [R.after_selected v (by change R.selected (R.forest.root v); rw [hvfix]; exact hv)]
        exact hvb.symm
      rw [hvafter]
      exact R.after_edge_target he
    · left
      have hw := R.selected_edge_closed hv hvb he
      have hwfix := R.forest.root_of_fixed w (R.selected_fixed w hw)
      rw [R.after_selected v (by change R.selected (R.forest.root v); rw [hvfix]; exact hv),
        R.after_selected w (by change R.selected (R.forest.root w); rw [hwfix]; exact hw)]
  · right
    have hvafter : R.after.root v = v := (R.after_outside v (by change ¬ R.selected (R.forest.root v); rwa [hvfix])).trans hvfix
    rw [hvafter]
    exact R.after_edge_target he

/-- Every actual old root path survives a recorded contraction. The new path
contains exactly the new roots of its original vertices; no disjointness is
asserted, since contracting distinct old paths may make them meet. -/
theorem transport_path (R : PetalRecord M)
    (p : DDFS.Path (predecessorGraph R.prior R.forest R.invariant))
    (hfix : ∀ v, p.Contains v → R.forest.root v = v) :
    ∃ q : DDFS.Path (predecessorGraph R.prior R.after R.after_invariant),
      q.first = R.after.root p.first ∧ q.last = R.after.root p.last ∧
      q.length ≤ p.length ∧
      ∀ w, q.Contains w ↔ ∃ v, p.Contains v ∧ R.after.root v = w := by
  exact p.map_eq_or_edge R.after.root (fun v w he hv _ => R.after_edge_eq_or_edge he (hfix v hv))

end MaximumMatching.Search.PetalRecord

end PetalPathTransport

section PetalDisjointTransport

/-! Contraction preserves disjoint root arms while their target remains
outside the selected petal or equals its bottleneck. Any new intersection would force both
original paths through the old bottleneck. -/
namespace MaximumMatching.Search.PetalRecord
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

theorem selected_path_contains_bottleneck (R : PetalRecord M)
    (p : DDFS.Path (predecessorGraph R.prior R.forest R.invariant))
    (v : Fin n) (hv : p.Contains v) (hsel : R.selected v)
    (hlast : p.last = R.bottleneck ∨ ¬ R.selected p.last) : p.Contains R.bottleneck := by
  apply Classical.byContradiction
  intro havoid
  obtain ⟨i, hi⟩ := hv
  let q := p.drop i.val (by omega)
  have hqf : R.selected q.first := by rw [p.drop_first, hi]; exact hsel
  have hqavoid : ¬ q.Contains R.bottleneck := fun hb => havoid (p.contains_drop _ _ hb)
  have hall := q.stays_in_closed_except R.selected R.bottleneck
    (fun _ _ hw hne he => R.selected_edge_closed hw hne he) hqf hqavoid
  have hslast : R.selected p.last := by
    have hh := hall ⟨q.length, by omega⟩
    change R.selected q.last at hh
    rwa [p.drop_last] at hh
  rcases hlast with he | hn
  · exact havoid (he ▸ p.contains_last)
  · exact hn hslast

theorem selected_bottom_path_contains_bottleneck (R : PetalRecord M)
    (p : DDFS.Path (predecessorGraph R.prior R.forest R.invariant))
    (v : Fin n) (hv : p.Contains v) (hsel : R.selected v)
    (hbottom : (predecessorGraph R.prior R.forest R.invariant).level p.last = 0) :
    p.Contains R.bottleneck := by
  apply R.selected_path_contains_bottleneck p v hv hsel
  by_cases hs : R.selected p.last
  · left
    by_cases he : p.last = R.bottleneck
    · exact he
    · have hh := DDFS.onRootTo_level_gt ((R.region p.last).1 hs) he
      rw [hbottom] at hh
      omega
  · exact Or.inr hs

/-- New equal roots identify precisely equal old fixed roots or two vertices
of the actual selected region. -/
theorem after_root_eq_fixed_iff (R : PetalRecord M) (u v : Fin n)
    (hu : R.forest.root u = u) (hv : R.forest.root v = v) :
    R.after.root u = R.after.root v ↔ u = v ∨ (R.selected u ∧ R.selected v) := by
  have hselected (w : Fin n) (hw : R.forest.root w = w) (hs : R.selected w) :
      R.after.root w = R.bottleneck :=
    R.after_selected w (by change R.selected (R.forest.root w); rwa [hw])
  have houtside (w : Fin n) (hw : R.forest.root w = w) (hs : ¬ R.selected w) :
      R.after.root w = w :=
    (R.after_outside w (by change ¬ R.selected (R.forest.root w); rwa [hw])).trans hw
  constructor
  · intro he
    by_cases hsu : R.selected u
    · by_cases hsv : R.selected v
      · exact Or.inr ⟨hsu, hsv⟩
      · have hbv : R.bottleneck = v := (hselected u hu hsu).symm.trans (he.trans (houtside v hv hsv))
        exact False.elim (hsv (hbv ▸ R.trees.bottleneck_mem))
    · by_cases hsv : R.selected v
      · have hub : u = R.bottleneck := (houtside u hu hsu).symm.trans (he.trans (hselected v hv hsv))
        exact False.elim (hsu (hub.symm ▸ R.trees.bottleneck_mem))
      · exact Or.inl ((houtside u hu hsu).symm.trans (he.trans (houtside v hv hsv)))
  · rintro (rfl | ⟨hsu, hsv⟩)
    · rfl
    · exact (hselected u hu hsu).trans (hselected v hv hsv).symm

/-- Disjointness survives while the first arm's target is outside the petal
or is its surviving bottleneck, and the second arm reaches the bottom. Both
resulting paths retain their endpoints and exact vertex-image sets. -/
theorem transport_disjoint_paths_of_surviving_target (R : PetalRecord M)
    (p q : DDFS.Path (predecessorGraph R.prior R.forest R.invariant))
    (hpfix : ∀ v, p.Contains v → R.forest.root v = v)
    (hqfix : ∀ v, q.Contains v → R.forest.root v = v)
    (hdis : p.Disjoint q) (hpend : p.last = R.bottleneck ∨ ¬ R.selected p.last)
    (hqbottom : (predecessorGraph R.prior R.forest R.invariant).level q.last = 0) :
    ∃ a b : DDFS.Path (predecessorGraph R.prior R.after R.after_invariant),
      a.first = R.after.root p.first ∧ a.last = p.last ∧
      b.first = R.after.root q.first ∧ b.last = q.last ∧ a.Disjoint b ∧
      (∀ v, a.Contains v ↔ ∃ u, p.Contains u ∧ R.after.root u = v) ∧
      (∀ v, b.Contains v ↔ ∃ u, q.Contains u ∧ R.after.root u = v) := by
  obtain ⟨a, haf, hal, _, ha⟩ := R.transport_path p hpfix
  obtain ⟨b, hbf, hbl, _, hb⟩ := R.transport_path q hqfix
  have hplast : R.after.root p.last = p.last := by
    have hf := hpfix p.last p.contains_last
    rcases hpend with he | hn
    · exact (R.after_selected p.last (by
        change R.selected (R.forest.root p.last)
        rw [hf, he]
        exact R.trees.bottleneck_mem)).trans he.symm
    · exact (R.after_outside p.last (by
        change ¬ R.selected (R.forest.root p.last)
        rwa [hf])).trans hf
  have hqlast : R.after.root q.last = q.last := by
    have hf := hqfix q.last q.contains_last
    by_cases hs : R.selected q.last
    · have he : q.last = R.bottleneck := by
        by_cases he : q.last = R.bottleneck
        · exact he
        · have hl := DDFS.onRootTo_level_gt ((R.region q.last).1 hs) he
          rw [hqbottom] at hl
          omega
      exact (R.after_selected q.last (by change R.selected (R.forest.root q.last); rwa [hf])).trans he.symm
    · exact (R.after_outside q.last (by change ¬ R.selected (R.forest.root q.last); rwa [hf])).trans hf
  refine ⟨a, b, haf, hal.trans hplast, hbf, hbl.trans hqlast, ?_, ha, hb⟩
  intro z haz hbz
  obtain ⟨u, hpu, huz⟩ := (ha z).1 haz
  obtain ⟨v, hqv, hvz⟩ := (hb z).1 hbz
  rcases (R.after_root_eq_fixed_iff u v (hpfix u hpu) (hqfix v hqv)).1
      (huz.trans hvz.symm) with he | ⟨hsu, hsv⟩
  · exact hdis v (he ▸ hpu) hqv
  · exact hdis R.bottleneck
      (R.selected_path_contains_bottleneck p u hpu hsu hpend)
      (R.selected_bottom_path_contains_bottleneck q v hqv hsv hqbottom)

/-- The outside-target specialization of surviving-target path transport. -/
theorem transport_disjoint_paths (R : PetalRecord M)
    (p q : DDFS.Path (predecessorGraph R.prior R.forest R.invariant))
    (hpfix : ∀ v, p.Contains v → R.forest.root v = v)
    (hqfix : ∀ v, q.Contains v → R.forest.root v = v)
    (hdis : p.Disjoint q) (hpend : ¬ R.selected p.last)
    (hqbottom : (predecessorGraph R.prior R.forest R.invariant).level q.last = 0) :
    ∃ a b : DDFS.Path (predecessorGraph R.prior R.after R.after_invariant),
      a.first = R.after.root p.first ∧ a.last = p.last ∧
      b.first = R.after.root q.first ∧ b.last = q.last ∧ a.Disjoint b ∧
      (∀ v, a.Contains v ↔ ∃ u, p.Contains u ∧ R.after.root u = v) ∧
      (∀ v, b.Contains v ↔ ∃ u, q.Contains u ∧ R.after.root u = v) :=
  R.transport_disjoint_paths_of_surviving_target p q hpfix hqfix hdis (Or.inr hpend) hqbottom

end MaximumMatching.Search.PetalRecord

end PetalDisjointTransport

section MatchingPathRecoveryTrees

/-! Executable recovery from recorded DDFS parent maps. The recursion follows
exactly those parents; proofs of spanning and strict layer descent certify
termination but do not choose paths at runtime. -/
namespace MaximumMatching.DDFS
variable {V : Type} {H : LayeredGraph V}

namespace RootedTree
variable {r : V} {S : V → Prop}

theorem level_le_root (T : RootedTree H r S) (v : V) (hv : S v) :
    H.level v ≤ H.level r := by
  have hr := T.spanning v hv
  induction hr with
  | root => exact Nat.le_refl _
  | @step u v _ hp ih =>
    exact Nat.le_trans (Nat.le_of_lt (H.decreases (T.edge u v hp).2.2))
      (ih (T.edge u v hp).1)

theorem parent_none_eq_root (T : RootedTree H r S) (v : V) (hv : S v)
    (hp : T.parent v = none) : v = r := by
  cases T.spanning v hv with
  | root => rfl
  | step _ he => rw [hp] at he; contradiction

variable [DecidableEq V]

/-- Recover the unique stored-parent path to a tree vertex. This executable
function neither searches the original graph nor extracts a witness by choice. -/
def recover (T : RootedTree H r S) (v : V) (hv : S v) :
    { p : Path H // p.first = r ∧ p.last = v ∧
      (∀ w, p.Contains w → S w) ∧
      ∀ j : Fin p.length, T.parent (p.vertex ⟨j.val + 1, by omega⟩) =
        some (p.vertex ⟨j.val, by omega⟩) } :=
  if hroot : v = r then
    ⟨Path.trivial H r, rfl, hroot.symm,
      (by rintro w ⟨j, hj⟩; change r = w at hj; rw [← hj, ← hroot]; exact hv),
      (fun j => Fin.elim0 j)⟩
  else
    match hp : T.parent v with
    | none => False.elim (hroot (T.parent_none_eq_root v hv hp))
    | some u =>
      let q := T.recover u (T.edge u v hp).1
      have he : H.Edge q.val.last v := q.property.2.1.symm ▸ (T.edge u v hp).2.2
      ⟨q.val.snoc v he, (q.val.snoc_first v he).trans q.property.1,
        q.val.snoc_last v he, (by
          intro w hw
          rcases (q.val.snoc_contains_iff v he w).1 hw with hw | hw
          · exact q.property.2.2.1 w hw
          · exact hw.symm ▸ hv), (by
          intro j
          by_cases hj : j.val < q.val.length
          · simpa only [Path.snoc, dite_eq_left (show j.val ≤ q.val.length by omega),
              dite_eq_left (show j.val + 1 ≤ q.val.length by omega)] using q.property.2.2.2 ⟨j.val, hj⟩
          · have hje : j.val = q.val.length := by
              have hjbound := j.isLt
              change j.val < q.val.length + 1 at hjbound
              omega
            simp only [Path.snoc, hje, Nat.le_refl, dite_true,
              show ¬q.val.length + 1 ≤ q.val.length by omega, dite_false]
            change T.parent v = some q.val.last
            rw [q.property.2.1]
            exact hp)⟩
termination_by H.level r - H.level v
decreasing_by
  have hparent := (T.edge u v hp).1
  have hle := T.level_le_root u hparent
  have hlt := H.decreases (T.edge u v hp).2.2
  omega


/-- Compute disjoint paths in two stored trees whose domains meet only at the
bottleneck. The returned paths are the actual parent-map recoveries. -/
def recoverLinkage {g b v : V} {T : V → Prop}
    (A : RootedTree H r S) (B : RootedTree H g T)
    (hv : S v) (hb : T b) (hoverlap : ∀ w, S w → T w → w = b)
    (hlevel : H.level b < H.level v) :
    { pq : Path H × Path H // pq.1.first = r ∧ pq.1.last = v ∧
      pq.2.first = g ∧ pq.2.last = b ∧ pq.1.Disjoint pq.2 } :=
  let p := A.recover v hv
  let q := B.recover b hb
  ⟨(p.val, q.val), p.property.1, p.property.2.1, q.property.1, q.property.2.1, by
    intro w hp hq
    have hw := hoverlap w (p.property.2.2.1 w hp) (q.property.2.2.1 w hq)
    have hl := p.val.last_level_le hp
    rw [p.property.2.1, hw] at hl
    omega⟩

end RootedTree

namespace ColoredTrees
variable {n : Nat} {H : LayeredGraph (Fin n)} {S : Fin n → Prop} {r g b : Fin n}

/-- The stored color determines which two stored parent maps recover the
linkage for a newly selected vertex. No existential path is executed. -/
def recoverLinkage (T : ColoredTrees H S r g b) (v : Fin n)
    (hv : S v) (hlevel : H.level b < H.level v) :
    { pq : Path H × Path H // pq.1.last = v ∧ pq.2.last = b ∧ pq.1.Disjoint pq.2 ∧
      ((pq.1.first = r ∧ pq.2.first = g ∧ T.color v = some false) ∨
        (pq.1.first = g ∧ pq.2.first = r ∧ T.color v = some true)) } :=
  match hc : T.color v with
  | none => False.elim (by
      have hne : v ≠ b := by intro he; rw [he] at hlevel; omega
      obtain ⟨c, hcolor⟩ := (T.domain v).2 ⟨hv, hne⟩
      rw [hc] at hcolor
      contradiction)
  | some false =>
    let pq := T.red.recoverLinkage T.green (Or.inr hc) (Or.inl rfl)
      (fun w hw hw' => (T.overlap w).1 ⟨hw, hw'⟩) hlevel
    ⟨pq.val, pq.property.2.1, pq.property.2.2.2.1, pq.property.2.2.2.2,
      Or.inl ⟨pq.property.1, pq.property.2.2.1, rfl⟩⟩
  | some true =>
    let pq := T.green.recoverLinkage T.red (Or.inr hc) (Or.inl rfl)
      (fun w hw hw' => (T.overlap w).1 ⟨hw', hw⟩) hlevel
    ⟨pq.val, pq.property.2.1, pq.property.2.2.2.1, pq.property.2.2.2.2,
      Or.inr ⟨pq.property.1, pq.property.2.2.1, rfl⟩⟩

end ColoredTrees
end MaximumMatching.DDFS

end MatchingPathRecoveryTrees

section MatchingPathRecoveryPredecessors

/-! Recover original predecessor witnesses and descending petal tails from
stored MIN lists. Each choice scans only a concrete predecessor list; no
matching path is obtained from a semantic existential witness. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

namespace BudGraphInvariant
variable {cap : Nat} {s : State V} {F : BudForest V}

/-- Select the first stored predecessor realizing an actual contracted edge. -/
def recoverEdgePredecessor (h : BudGraphInvariant M cap s F) (v w : V)
    (he : (predecessorGraph s F h).Edge v w) :
    { u : V // u ∈ s.predecessors v ∧ F.root u = w } :=
  match hp : (s.predecessors v).find? (fun u => decide (F.root u = w)) with
  | some u => ⟨u, List.mem_of_find?_eq_some hp,
      of_decide_eq_true (List.find?_some (p := fun x => decide (F.root x = w)) hp)⟩
  | none => False.elim (by
      obtain ⟨u, hu, huw⟩ := List.mem_map.mp he.2
      have hn := List.find?_eq_none.mp hp u hu
      simp only [huw, decide_true] at hn
      contradiction)

/-- Choose the head of a nonempty stored predecessor list. Positive layer
and the MIN invariant prove that the empty-list case cannot occur. -/
def firstPredecessor (h : BudGraphInvariant M cap s F) (v : V)
    (hpos : 0 < (s.minLabel v).getD 0) :
    { u : V // u ∈ s.predecessors v ∧
      (predecessorGraph s F h).Edge v (F.root u) } :=
  match hl : s.predecessors v with
  | [] => False.elim (by
      obtain ⟨w, hw⟩ := h.outgoing v hpos
      obtain ⟨u, hu, _⟩ := List.mem_map.mp hw.2
      rw [hl] at hu
      exact List.not_mem_nil hu)
  | u :: us => ⟨u, List.mem_cons_self, (by
      have ha : (s.minLabel v).isSome = true := by
        cases hlabel : s.minLabel v with
        | none => simp only [hlabel, Option.getD_none] at hpos; omega
        | some k => rfl
      exact ⟨ha, List.mem_map.mpr ⟨u, by rw [hl]; exact List.mem_cons_self, rfl⟩⟩)⟩

end BudGraphInvariant

namespace PetalRecord
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

/-- Recover an actual descending path from a selected vertex to the recorded
bottleneck by following stored predecessors. Region closure ensures that every
step stays in this petal, and the recorded layer strictly decreases. -/
def recoverTail (R : PetalRecord M) (v : Fin n) (hv : R.selected v) :
    { p : DDFS.Path (predecessorGraph R.prior R.forest R.invariant) //
      p.first = v ∧ p.last = R.bottleneck ∧ ∀ w, p.Contains w → R.selected w } :=
  if he : v = R.bottleneck then
    ⟨DDFS.Path.trivial _ v, rfl, he, by
      rintro w ⟨j, hj⟩
      change v = w at hj
      exact hj ▸ hv⟩
  else
    have hpos : 0 < (R.prior.minLabel v).getD 0 :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) (DDFS.onRootTo_level_gt ((R.region v).1 hv) he)
    let u := R.invariant.firstPredecessor v hpos
    let q := R.recoverTail (R.forest.root u.val) (R.selected_edge_closed hv he u.property.2)
    have hedge : (predecessorGraph R.prior R.forest R.invariant).Edge v q.val.first :=
      q.property.1.symm ▸ u.property.2
    ⟨q.val.prepend v hedge, rfl, (q.val.prepend_last v hedge).trans q.property.2.1, by
      intro w hw
      rcases (q.val.contains_prepend_iff v hedge w).1 hw with hw | hw
      · exact hw.symm ▸ hv
      · exact q.property.2.2 w hw⟩
termination_by (R.prior.minLabel v).getD 0
decreasing_by exact R.invariant.edge_decreases u.property.2

end PetalRecord
end MaximumMatching.Search

end MatchingPathRecoveryPredecessors
