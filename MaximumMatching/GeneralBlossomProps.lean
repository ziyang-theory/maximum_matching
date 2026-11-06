import MaximumMatching.GeneralBaseReroute

/-! Prop edges cannot leave an established boundary blossom for a different
low-tenacity component. The proof uses actual minlevel paths and their honest
last predecessors, together with lower-cutoff confinement and coverage. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Every predecessor of a blossom member is either its boundary or a member
of the same blossom, under confinement at that cutoff. -/
theorem blossom_predecessor_mem (t : Nat) (b u v : V)
    (hv : Blossom M t b v) (hb : levelLT (some t) (tenacity M b))
    (hconf : ∀ (c w : V), Blossom M t c w → levelLT (some t) (tenacity M c) →
      ∀ q : AltSegment M, q.Shortest → q.first = c → q.last = w →
        ∀ z, q.Contains z → z = c ∨ Blossom M t c z)
    (hpred : Predecessor M u v) : u = b ∨ Blossom M t b u := by
  obtain ⟨p, hpv, hpmin, hpos, hpu⟩ := hpred
  have hp := p.shortest_of_minlevel (by rw [hpv]; exact hpmin)
  obtain ⟨i, hi, _, hilast, _, _⟩ := blossom_on_shortest t b v hv p hpv hp
  by_cases he : i.val = p.length - 1
  · exact Or.inl (hpu.symm.trans ((congrArg p.vertex (Fin.ext he)).symm.trans hi))
  · have hmem := p.blossom_suffix_mem t b v hv hb hconf hpv hp i
      ⟨p.length - 1, by omega⟩ hi (by change i.val < p.length - 1; omega)
    exact Or.inr (hpu ▸ hmem)

/-- A prop from a blossom member to another low vertex keeps the destination
inside that blossom. Coverage identifies its boundary from the honest
predecessor prefix; confinement is not needed in this direction. -/
theorem blossom_low_successor_mem (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b)
    (b u v : V) (hu : Blossom M t b u) (hb : levelLT (some t) (tenacity M b))
    (hv : levelLE (tenacity M v) (some t)) (hpred : Predecessor M u v) :
    Blossom M t b v := by
  obtain ⟨p, hpv, hpmin, hpos, hpu⟩ := hpred
  have hp := p.shortest_of_minlevel (by rw [hpv]; exact hpmin)
  let q := p.take (p.length - 1) (by omega)
  have hq : q.Shortest := p.minlevel_last_predecessor_honest (by rw [hpv]; exact hpmin) hpos
  have hqb := blossom_baseOnPath t b u hu hb q hpu hq
  have hvs : ∃ s, tenacity M v = some s ∧ s ≤ t := by
    cases hs : tenacity M v with
    | none => simp only [hs, levelLE] at hv
    | some s => exact ⟨s, rfl, by simpa only [hs, levelLE] using hv⟩
  obtain ⟨s, hs, hst⟩ := hvs
  obtain ⟨c, hc, hcv⟩ := blossom_cover_of_base_existence t ht hexists v s hs hst
  have hpcb := blossom_baseOnPath t c v hcv hc p hpv hp
  have hpb : p.BaseOnPath t b := by
    apply (q.baseOnPath_initial_iff p (by change p.length - 1 ≤ p.length; omega)
      (by intro i; rfl) t ?_ b).1 hqb
    intro j hj
    have hje : j.val = p.length := by change p.length - 1 < j.val at hj; omega
    have hj' : j = ⟨p.length, by omega⟩ := Fin.ext hje
    rw [hj']
    change ¬levelLT (some t) (tenacity M p.last)
    rw [hpv, hs]
    change ¬t < s
    omega
  have hcb := p.baseOnPath_unique t c b hpcb hpb
  exact hcb ▸ hcv

/-- An edge from a low vertex outside a boundary blossom to one of its members
is a bridge. Both possible orientations of a prop are excluded. -/
theorem blossom_low_crossing_bridge (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b)
    (hconf : ∀ (c w : V), Blossom M t c w → levelLT (some t) (tenacity M c) →
      ∀ q : AltSegment M, q.Shortest → q.first = c → q.last = w →
        ∀ z, q.Contains z → z = c ∨ Blossom M t c z)
    (b u v : V) (hb : levelLT (some t) (tenacity M b))
    (hv : Blossom M t b v) (hu : levelLE (tenacity M u) (some t))
    (houtside : ¬Blossom M t b u) (hadj : G.Adj u v) : Bridge M u v := by
  refine ⟨hadj, ?_⟩
  rintro (hpred | hpred)
  · rcases blossom_predecessor_mem t b u v hv hb hconf hpred with h | h
    · rw [h] at hu
      cases he : tenacity M b with
      | none => simp only [he, levelLE] at hu
      | some s =>
        have hst : s ≤ t := by simpa only [he, levelLE] using hu
        have hts : t < s := by simpa only [he, levelLT] using hb
        omega
    · exact houtside h
  · exact houtside (blossom_low_successor_mem t ht hexists b v u hv hb hu hpred)

end MaximumMatching
