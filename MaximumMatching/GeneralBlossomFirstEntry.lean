import MaximumMatching.GeneralBlossomJoin

/-! Confinement after the first entry into an established blossom on a
shortest path ending at its boundary. Replacing the reversed tail by an
arbitrary shortest relative path proves the actual tail shortest. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Reverse the suffix of an odd path. Its first edge is unmatched, regardless
of the parity of the cut index. -/
def reverseOddTail (p : AltPath M) (hpo : p.length % 2 = 1)
    (D : Fin (p.length + 1)) : AltSegment M where
  length := p.length - D.val
  vertex i := p.vertex ⟨p.length - i.val, by omega⟩
  injective := by
    intro i j he
    have hh := congrArg Fin.val (p.injective _ _ he)
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    change p.length - i.val = p.length - j.val at hh
    omega
  adjacent := by
    intro i
    have hh := G.symm (p.adjacent ⟨p.length - (i.val + 1), by omega⟩)
    simpa only [show p.length - (i.val + 1) + 1 = p.length - i.val by omega] using hh
  alternating := by
    intro i
    have hh := p.alternating ⟨p.length - (i.val + 1), by omega⟩
    have hindex : p.length - (i.val + 1) + 1 = p.length - i.val := by omega
    have hpar : (p.length - (i.val + 1)) % 2 = i.val % 2 := by omega
    constructor
    · intro hm
      have hm' := M.symm hm
      have ha := hh.1 (by simpa only [hindex] using hm')
      simpa only [hpar] using ha
    · intro hi
      have hm := M.symm (hh.2 (by simpa only [hpar] using hi))
      simpa only [hindex] using hm

@[simp] theorem reverseOddTail_first (p : AltPath M) (hpo) (D) :
    (p.reverseOddTail hpo D).first = p.last := by
  simp only [reverseOddTail, AltSegment.first, Nat.sub_zero]
  rfl

@[simp] theorem reverseOddTail_last (p : AltPath M) (hpo) (D) :
    (p.reverseOddTail hpo D).last = p.vertex D := by
  change p.vertex ⟨p.length - (p.length - D.val), _⟩ = p.vertex D
  congr 1
  apply Fin.ext
  have := D.isLt
  change p.length - (p.length - D.val) = D.val
  omega

/-- The first entry into an established blossom occurs across an unmatched
edge, hence at an odd path index. Matching closure excludes an even entry. -/
theorem first_blossom_entry_odd (p : AltPath M) (t : Nat) (b : V)
    (D : Fin (p.length + 1)) (hDmem : Blossom M t b (p.vertex D))
    (hfirst : ∀ a : Fin (p.length + 1), a.val < D.val → ¬Blossom M t b (p.vertex a)) :
    D.val % 2 = 1 := by
  have hDpos : 0 < D.val := by
    by_cases hz : D.val = 0
    · have hD : D = ⟨0, by omega⟩ := Fin.ext hz
      let q := AltPath.trivial M p.first p.start_free
      have hq : q.Shortest := by
        change IsShortest M 0 p.first 0
        exact ⟨⟨q, rfl, rfl, rfl⟩, fun _ _ => Nat.zero_le _⟩
      have hmem : Blossom M t b q.last := by
        change Blossom M t b p.first
        simpa only [hD, first] using hDmem
      obtain ⟨i, _, _, hi, _, _⟩ := blossom_on_shortest t b q.last hmem q rfl hq
      change i.val < 0 at hi
      omega
    · omega
  by_cases he : D.val % 2 = 0
  · have hm := p.mate_previous D.val (by omega) hDpos he
    have hprev := (matched_blossom_iff hm t b).1 hDmem
    exact False.elim (hfirst ⟨D.val - 1, by omega⟩ (by change D.val - 1 < D.val; omega) hprev)
  · omega

/-- At the first blossom entry, the actual reversed tail is a shortest relative
path. Consequently every original tail vertex lies in the blossom or is its
boundary. The lower confinement premise is used only for already-established
shortest relative paths. -/
theorem first_entry_reverse_tail_shortest (p : AltPath M) (hp : p.Shortest)
    (hpo : p.length % 2 = 1) (t : Nat)
    (hc : levelLT (some t) (tenacity M p.last))
    (hconf : ∀ (v : V), Blossom M t p.last v →
      ∀ q : AltSegment M, q.Shortest → q.first = p.last → q.last = v →
        ∀ w, q.Contains w → w = p.last ∨ Blossom M t p.last w)
    (D : Fin (p.length + 1)) (hDo : D.val % 2 = 1)
    (hDmem : Blossom M t p.last (p.vertex D))
    (hfirst : ∀ a : Fin (p.length + 1), a.val < D.val → ¬Blossom M t p.last (p.vertex a)) :
    (p.reverseOddTail hpo D).Shortest ∧
      ∀ j : Fin (p.length + 1), D.val ≤ j.val →
        p.vertex j = p.last ∨ Blossom M t p.last (p.vertex j) := by
  have hDlt : D.val < p.length := by
    by_cases he : D.val = p.length
    · have hD : D = ⟨p.length, by omega⟩ := Fin.ext he
      rw [hD] at hDmem
      exact False.elim (blossom_excludes_base t p.last hc hDmem)
    · have := D.isLt
      omega
  obtain ⟨s, hvs, _⟩ := blossom_tenacity_bound t p.last (p.vertex D) hDmem
  obtain ⟨r, hrD, hr, hre⟩ := finite_tenacity_shortest_parity (p.vertex D) s 0 hvs
  obtain ⟨i, hie, hi, _, hq⟩ := blossom_shortest_relative t p.last (p.vertex D) hDmem hc r hrD hr
  let q := r.segment i.val (by omega) hie
  have hqf : q.first = p.last := (r.segment_first _ _ _).trans hi
  have hql : q.last = p.vertex D := (r.segment_last _ _ _).trans hrD
  have hqe : q.length % 2 = 0 := by
    change (r.length - i.val) % 2 = 0
    omega
  have hdis : (p.take D.val (by omega)).SegmentReverseDisjoint q 0 q.length := by
    intro a j _ hj he
    have haved : a.val ≤ D.val := by have := a.isLt; change a.val < D.val + 1 at this; omega
    change p.vertex ⟨a.val, _⟩ = q.vertex j at he
    by_cases had : a.val = D.val
    · have ha : (⟨a.val, by omega⟩ : Fin (p.length + 1)) = D := Fin.ext had
      rw [ha, ← hql] at he
      have hje := congrArg Fin.val (q.injective ⟨q.length, by omega⟩ j he)
      change q.length = j.val at hje
      omega
    · rcases hconf (p.vertex D) hDmem q hq hqf hql (q.vertex j) ⟨j, rfl⟩ with hcj | hmem
      · rw [hcj] at he
        have hae := congrArg Fin.val (p.injective ⟨a.val, by omega⟩ ⟨p.length, by omega⟩ he)
        change a.val = p.length at hae
        omega
      · exact hfirst ⟨a.val, by omega⟩ (by change a.val < D.val; omega) (he ▸ hmem)
  let z := (p.take D.val (by omega)).spliceReverseSegment q 0 q.length
    (by omega) (Nat.le_refl _) hql.symm hDo hqe hdis
  have hzlast : z.last = p.last := (spliceReverseSegment_last _ _ _ _ _ _ _ _ _ _).trans hqf
  have hzlen : z.length = D.val + q.length := by
    change D.val + (q.length - 0) = _
    omega
  have hbound : p.length ≤ z.length := hp.2 z.length ⟨z, hzlast, rfl, by rw [hzlen]; omega⟩
  let a := p.reverseOddTail hpo D
  have haf : a.first = p.last := p.reverseOddTail_first hpo D
  have hal : a.last = p.vertex D := p.reverseOddTail_last hpo D
  have hae : a.length % 2 = 0 := by change (p.length - D.val) % 2 = 0; omega
  have hqa : q.length ≤ a.length := hq a (haf.trans hqf.symm) (hal.trans hql.symm) (hae.trans hqe.symm)
  have hlen : a.length = q.length := by
    change p.length - D.val = q.length
    change q.length ≤ p.length - D.val at hqa
    rw [hzlen] at hbound
    omega
  have hashort : a.Shortest := by
    intro s hsf hsl hspar
    rw [hlen]
    exact hq s (hsf.trans (haf.trans hqf.symm)) (hsl.trans (hal.trans hql.symm))
      (hspar.trans (hae.trans hqe.symm))
  refine ⟨hashort, ?_⟩
  intro j hDj
  apply hconf (p.vertex D) hDmem a hashort haf hal (p.vertex j)
  refine ⟨⟨p.length - j.val, by change p.length - j.val < p.length - D.val + 1; omega⟩, ?_⟩
  change p.vertex ⟨p.length - (p.length - j.val), _⟩ = p.vertex j
  congr 1
  apply Fin.ext
  have := j.isLt
  change p.length - (p.length - j.val) = j.val
  omega

private theorem least_member_index (P : Nat → Prop) (h : ∃ k, P k) :
    ∃ k, P k ∧ ∀ l, l < k → ¬P l := by
  classical
  obtain ⟨k, hk⟩ := h
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hs : ∃ l, l < k ∧ P l
    · obtain ⟨l, hl, hp⟩ := hs
      exact ih l hl hp
    · exact ⟨k, hk, fun l hl hp => hs ⟨l, hl, hp⟩⟩

/-- Select the first actual blossom entry and derive its odd parity. -/
theorem first_blossom_entry (p : AltPath M) (t : Nat) (b : V)
    (hmem : ∃ i : Fin (p.length + 1), Blossom M t b (p.vertex i)) :
    ∃ D : Fin (p.length + 1), D.val % 2 = 1 ∧ Blossom M t b (p.vertex D) ∧
      ∀ a : Fin (p.length + 1), a.val < D.val → ¬Blossom M t b (p.vertex a) := by
  let P := fun k => ∃ i : Fin (p.length + 1), i.val = k ∧ Blossom M t b (p.vertex i)
  obtain ⟨i, hi⟩ := hmem
  obtain ⟨k, ⟨D, hD, hmem⟩, hleast⟩ := least_member_index P ⟨i.val, i, rfl, hi⟩
  have hfirst : ∀ a : Fin (p.length + 1), a.val < D.val → ¬Blossom M t b (p.vertex a) := by
    intro a ha hmem
    exact hleast a.val (by omega) ⟨a, rfl, hmem⟩
  exact ⟨D, p.first_blossom_entry_odd t b D hmem hfirst, hmem, hfirst⟩

/-- Any actual blossom visit on an odd shortest path ending at the boundary
supplies a concrete first index and a confined actual suffix. -/
theorem exists_first_entry_confined_tail (p : AltPath M) (hp : p.Shortest)
    (hpo : p.length % 2 = 1) (t : Nat)
    (hc : levelLT (some t) (tenacity M p.last))
    (hconf : ∀ (v : V), Blossom M t p.last v →
      ∀ q : AltSegment M, q.Shortest → q.first = p.last → q.last = v →
        ∀ w, q.Contains w → w = p.last ∨ Blossom M t p.last w)
    (hmem : ∃ i : Fin (p.length + 1), Blossom M t p.last (p.vertex i)) :
    ∃ D : Fin (p.length + 1), D.val % 2 = 1 ∧ Blossom M t p.last (p.vertex D) ∧
      (∀ a : Fin (p.length + 1), a.val < D.val → ¬Blossom M t p.last (p.vertex a)) ∧
      (p.reverseOddTail hpo D).Shortest ∧
      ∀ j : Fin (p.length + 1), D.val ≤ j.val →
        p.vertex j = p.last ∨ Blossom M t p.last (p.vertex j) := by
  obtain ⟨D, hDo, hDmem, hfirst⟩ := p.first_blossom_entry t p.last hmem
  obtain ⟨hshort, htail⟩ := p.first_entry_reverse_tail_shortest hp hpo t hc hconf D hDo hDmem hfirst
  exact ⟨D, hDo, hDmem, hfirst, hshort, htail⟩

/-- The first entry's evenlevel is exactly the boundary's minimum level plus
the length of the actual reversed tail. No path-index honesty is assumed. -/
theorem first_entry_evenlevel (p : AltPath M) (hpo : p.length % 2 = 1)
    (t C : Nat) (hc : levelLT (some t) (tenacity M p.last))
    (hcmin : minlevel M p.last = some C)
    (D : Fin (p.length + 1)) (hDo : D.val % 2 = 1)
    (hDmem : Blossom M t p.last (p.vertex D))
    (hshort : (p.reverseOddTail hpo D).Shortest) :
    evenlevel M (p.vertex D) = some (C + (p.length - D.val)) := by
  have hce : evenlevel M p.last = some C :=
    (minlevel_eq_even_of_outer p.last (blossom_outer t p.last (p.vertex D) hDmem)).symm.trans hcmin
  obtain ⟨q, hqc, hqC, hqe⟩ := ((level_eq_some_iff M 0 p.last C).1 hce).1
  have hqshort : q.Shortest := by
    simpa only [Shortest, hqc, hqC, hqe] using (level_eq_some_iff M 0 p.last C).1 hce
  obtain ⟨s, hds, _⟩ := blossom_tenacity_bound t p.last (p.vertex D) hDmem
  let r := p.reverseOddTail hpo D
  have hrf : r.first = p.last := p.reverseOddTail_first hpo D
  have hrl : r.last = p.vertex D := p.reverseOddTail_last hpo D
  have hre : r.length % 2 = 0 := by change (p.length - D.val) % 2 = 0; omega
  have hl := (blossom_relative_length_formula t p.last (p.vertex D) hDmem hc
    q hqshort (by omega) hqc r hshort hrf hrl s hds).1
  rw [hre, hqC] at hl
  change IsShortest M 0 (p.vertex D) (C + (p.length - D.val)) at hl
  exact (level_eq_some_iff M 0 (p.vertex D) (C + (p.length - D.val))).2
    hl

end MaximumMatching.AltPath
