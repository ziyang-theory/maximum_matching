import MaximumMatching.ActivePetalRecord
import MaximumMatching.MatchingPathRecoveryPredecessors

/-! Computed tails in the live petal region. Every successor is selected from
an actual live edge, so removal cannot invalidate the recovered tail. -/
namespace MaximumMatching.Search.ActivePetalRecord
variable {n i cut : Nat} {G : Graph (Fin n)} {M : Matching G}

theorem selected_edge_closed (R : ActivePetalRecord M i cut) {v w : Fin n}
    (hv : R.selected v) (hne : v ≠ R.bottleneck)
    (he : R.graph.Edge v w) : R.selected w := by
  have hlevel := DDFS.onRootTo_level_gt ((R.region v).1 hv) hne
  obtain ⟨p, hp, hpb, i, hiv⟩ := (R.region v).1 hv
  let a := p.take i.val (by omega)
  have haf : a.first = p.first := rfl
  have hal : a.last = v := hiv
  obtain ⟨z, hzf, hz0⟩ := R.input.reach w
  have hze : R.graph.Edge v z.first := by
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
  have hte : R.graph.Edge v tail.first := hze
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

/-- Select the first live outgoing edge; bottom reachability excludes an
empty scan at every positive layer. -/
def firstSuccessor (R : ActivePetalRecord M i cut) (v : Fin n)
    (hpos : 0 < R.graph.level v) : { w : Fin n // R.graph.Edge v w } :=
  match hh : R.input.live.find? (fun w => decide (R.graph.Edge v w)) with
  | some w => ⟨w, of_decide_eq_true (List.find?_some (p := fun w => decide (R.graph.Edge v w)) hh)⟩
  | none => False.elim (by
      obtain ⟨p, hpf, hpb⟩ := R.input.reach v
      change R.graph.level p.last = 0 at hpb
      have hlen : 0 < p.length := by
        by_cases hl : p.length = 0
        · have hfl : p.first = p.last := congrArg p.vertex (Fin.ext (by exact hl.symm))
          rw [← hfl, hpf] at hpb
          omega
        · omega
      have he := p.adjacent ⟨0, hlen⟩
      change R.graph.Edge p.first (p.vertex ⟨1, by omega⟩) at he
      rw [hpf] at he
      have hn := List.find?_eq_none.mp hh _ he.2.1
      simp only [decide_eq_true_eq] at hn
      exact hn he)

/-- Recover the actual descending live path from a selected root to its
recorded bottleneck, scanning only live outgoing edges. -/
def recoverTail (R : ActivePetalRecord M i cut) (v : Fin n) (hv : R.selected v) :
    { p : DDFS.Path R.graph //
      p.first = v ∧ p.last = R.bottleneck ∧ ∀ w, p.Contains w → R.selected w } :=
  if he : v = R.bottleneck then
    ⟨DDFS.Path.trivial _ v, rfl, he, by
      rintro w ⟨j, hj⟩
      change v = w at hj
      exact hj ▸ hv⟩
  else
    have hpos : 0 < R.graph.level v :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) (DDFS.onRootTo_level_gt ((R.region v).1 hv) he)
    let u := R.firstSuccessor v hpos
    let q := R.recoverTail u.val (R.selected_edge_closed hv he u.property)
    have hedge : R.graph.Edge v q.val.first := q.property.1.symm ▸ u.property
    ⟨q.val.prepend v hedge, rfl, (q.val.prepend_last v hedge).trans q.property.2.1, by
      intro w hw
      rcases (q.val.contains_prepend_iff v hedge w).1 hw with hw | hw
      · exact hw.symm ▸ hv
      · exact q.property.2.2 w hw⟩
termination_by R.graph.level v
decreasing_by exact R.graph.decreases u.property

end MaximumMatching.Search.ActivePetalRecord
