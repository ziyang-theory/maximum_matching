import MaximumMatching.GeneralShortConfinement

/-! Actual even shortest candidates for the reverse-order base argument. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A bounded path to a matched blossom member on an even path supplies an
even shortest candidate, possibly at that member's matched neighbor. -/
theorem even_shortest_blossom_candidate (p : AltPath M) (hpe : p.length % 2 = 0)
    (t : Nat) (d w x : V) (K : Nat) (hmem : Blossom M t d w)
    (hm : M.mate w = some x) (hon : ∃ a, p.vertex a = w)
    (hw : HasPathLength M (K % 2) w K) :
    ∃ s : AltPath M, s.Shortest ∧ s.length % 2 = 0 ∧
      Blossom M t d s.last ∧ (∃ a, p.vertex a = s.last) ∧ s.length ≤ K + 1 := by
  obtain ⟨a, ha⟩ := hon
  have hapos : 0 < a.val := by
    by_cases hz : a.val = 0
    · have ha0 : a = ⟨0, by omega⟩ := Fin.ext hz
      have hmf : M.mate p.first = some x := by rw [← ha, ha0] at hm; exact hm
      change M.mate (p.vertex ⟨0, by omega⟩) = some x at hmf
      rw [p.start_free] at hmf
      contradiction
    · omega
  obtain ⟨b, _, hmb⟩ := p.even_suffix_matched_closed hpe 1 (by decide) a (by omega)
  have hbx : p.vertex b = x := M.mate_unique (by simpa only [ha] using hmb) hm
  have hex : ∃ y L, Blossom M t d y ∧ (∃ a, p.vertex a = y) ∧ HasPathLength M 0 y L ∧ L ≤ K + 1 := by
    by_cases hK : K % 2 = 0
    · exact ⟨w, K, hmem, ⟨a, ha⟩, by simpa only [hK] using hw, by omega⟩
    · obtain ⟨r, hrw, hrlen, hrpar⟩ := hw
      have hro : r.length % 2 = 1 := by omega
      have hm' : M.mate r.last = some x := by rw [hrw]; exact hm
      let z := r.appendMatched hro hm'
      refine ⟨x, K + 1, (matched_blossom_iff hm t d).mp hmem, ⟨b, hbx⟩,
        ⟨z, r.appendMatched_last hro hm', ?_, ?_⟩, Nat.le_refl _⟩
      · change r.length + 1 = K + 1
        omega
      · omega
  obtain ⟨y, L, hymem, hyon, hyw, hLK⟩ := hex
  have hfinite : ∃ n, evenlevel M y = some n := by
    cases he : evenlevel M y with
    | none => exact False.elim ((level_eq_none_iff M 0 y).1 he ⟨L, hyw⟩)
    | some n => exact ⟨n, rfl⟩
  obtain ⟨n, hn⟩ := hfinite
  have hshort := (level_eq_some_iff M 0 y n).mp hn
  obtain ⟨s, hsy, hsn, hspar⟩ := hshort.1
  have hs : s.Shortest := by simpa only [Shortest, hsy, hsn, hspar] using hshort
  exact ⟨s, hs, by omega, hsy.symm ▸ hymem, hsy.symm ▸ hyon,
    by have := hshort.2 L hyw; omega⟩

/-- The two original paths supply a bounded even candidate in the short path's
base blossom, even when that base is absent from the long path. -/
theorem initial_even_blossom_candidate (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (d : V) (D : Fin (q.length + 1)) (hD : q.vertex D = d) (hDe : D.val % 2 = 0)
    (hdhigh : levelLT (some (p.length + q.length)) (tenacity M d))
    (hdabsent : ∀ a, p.vertex a ≠ d)
    (hmember : Blossom M (p.length + q.length) d (q.vertex ⟨q.length - 1, by omega⟩))
    (hclosed : ∀ r : AltPath M, r.Shortest → Blossom M (p.length + q.length) d r.last →
      r.length < q.length → ∀ (i j : Fin (r.length + 1)), r.vertex i = d → i.val < j.val →
        Blossom M (p.length + q.length) d (r.vertex j)) :
    ∃ r : AltPath M, r.Shortest ∧ r.length % 2 = 0 ∧ r.length < q.length ∧
      Blossom M (p.length + q.length) d r.last ∧ ∃ a, p.vertex a = r.last := by
  let x := p.vertex ⟨p.length - 1, by omega⟩
  have hpm : M.mate p.last = some x := p.mate_previous p.length (Nat.le_refl _) (by omega) hpe
  have hqm : M.mate q.last = some x := by rw [hend]; exact hpm
  let Q := q.appendMatched hqo hqm
  let P := p.take (p.length - 1) (by omega)
  have hQe : Q.length % 2 = 0 := by change (q.length + 1) % 2 = 0; omega
  have hQshort : Q.Shortest := by
    have hh := (matched_shortest_iff M hqm q.length).mpr (by simpa only [Shortest, hqo] using hq)
    change IsShortest M (Q.length % 2) Q.last Q.length
    rw [hQe]
    simpa only [Q, appendMatched_length, appendMatched_last] using hh
  have hQD (j : Fin (q.length + 1)) : Q.vertex ⟨j.val, by change j.val < q.length + 1 + 1; omega⟩ = q.vertex j := by
    simp only [Q, appendMatched, append, dite_eq_left (show j.val ≤ q.length by omega)]
  let DQ : Fin (Q.length + 1) := ⟨D.val, by change D.val < q.length + 1 + 1; omega⟩
  have hDQ : Q.vertex DQ = d := (hQD D).trans hD
  obtain ⟨g⟩ := firstHit_exists P Q (DQ.val + 1)
    ⟨⟨P.length, by omega⟩, ⟨Q.length, by omega⟩,
      by change D.val + 1 ≤ q.length + 1; omega,
      by change P.last = Q.last; rw [q.appendMatched_last hqo hqm]; rfl⟩
  have hg := Q.first_high_suffix_hit_le_of_length_le P hQshort hQe DQ hDe
    (p.length + q.length) (by change q.length + 1 + (p.length - 1) ≤ p.length + q.length; omega)
    (by rw [hDQ]; exact hdhigh) (by
      intro a he
      exact hdabsent ⟨a.val, by have := a.isLt; change a.val < p.length - 1 + 1 at this; omega⟩ (he.trans hDQ)) g
  have hglt : g.pi.val < q.length := by
    have hgb := g.pi.isLt
    change g.pi.val < q.length + 1 + 1 at hgb
    have hgle : g.pi.val ≤ q.length := by omega
    by_cases he : g.pi.val = q.length
    · have hqend : Q.vertex g.pi = q.last := by
        have heq : g.pi = ⟨q.length, by change q.length < q.length + 1 + 1; omega⟩ := Fin.ext he
        rw [heq]
        exact hQD ⟨q.length, by omega⟩
      have hh : p.vertex ⟨g.qi.val, by have := g.qi.isLt; change g.qi.val < p.length - 1 + 1 at this; omega⟩ = p.last :=
        g.hit.trans (hqend.trans hend)
      have hi := congrArg Fin.val (p.injective _ ⟨p.length, by omega⟩ hh)
      have hib := g.qi.isLt
      change g.qi.val < p.length - 1 + 1 at hib
      change g.qi.val = p.length at hi
      omega
    · omega
  let j : Fin (q.length + 1) := ⟨g.pi.val, by omega⟩
  have hjval : j.val = g.pi.val := rfl
  have hhit : p.vertex ⟨g.qi.val, by have := g.qi.isLt; change g.qi.val < p.length - 1 + 1 at this; omega⟩ = q.vertex j :=
    g.hit.trans (hQD j)
  have hDlt : D.val < j.val := by have := g.in_suffix; exact Nat.lt_of_succ_le this
  have hqeven : evenlevel M q.last = some p.length := by
    rw [hend]
    exact (level_eq_some_iff M 0 p.last p.length).mpr (by simpa only [Shortest, hpe] using hp)
  have hqodd : oddlevel M q.last = some q.length :=
    (level_eq_some_iff M 1 q.last q.length).mpr (by simpa only [Shortest, hqo] using hq)
  have hqmin : minlevel M q.last = some q.length := by
    simp only [minlevel, hqeven, hqodd, levelMin]
    exact congrArg some (Nat.min_eq_right (by omega))
  let q₀ := q.take (q.length - 1) (by omega)
  have hq₀ : q₀.Shortest := q.minlevel_last_predecessor_honest hqmin (by omega)
  have hjmem := hclosed q₀ hq₀ hmember (by change q.length - 1 < q.length; omega)
    ⟨D.val, by change D.val < q.length - 1 + 1; omega⟩
    ⟨j.val, by change j.val < q.length - 1 + 1; omega⟩ hD hDlt
  have hm : M.mate (q.vertex j) = some (q.vertex ⟨j.val + 1, by omega⟩) :=
    q.mate_next j.val hglt hg.2.1
  obtain ⟨r, hr, hre, hrmem, hron, hrlen⟩ := p.even_shortest_blossom_candidate hpe
    (p.length + q.length) d (q.vertex j) (q.vertex ⟨j.val + 1, by omega⟩) j.val hjmem hm
    ⟨_, hhit⟩ (q.prefix_witness j)
  exact ⟨r, hr, hre, by change r.length ≤ g.pi.val + 1 at hrlen; omega, hrmem, hron⟩

end MaximumMatching.AltPath
