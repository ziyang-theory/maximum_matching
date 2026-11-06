import MaximumMatching.BaseRerouting
import MaximumMatching.GeneralConfinementSteps

section GeneralStructureCandidate

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

end GeneralStructureCandidate

section GeneralStructureMinimize

/-! Minimal shortest-path candidates rule out visits from an established lower
blossom to a later high suffix. All membership and path simplicity statements
are derived from actual paths and lower confinement. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

private theorem least_candidate_length (P : Nat → Prop) (h : ∃ k, P k) :
    ∃ k, P k ∧ ∀ l, P l → k ≤ l := by
  classical
  obtain ⟨k, hk⟩ := h
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hs : ∃ l, l < k ∧ P l
    · obtain ⟨l, hl, hp⟩ := hs
      exact ih l hl hp
    · exact ⟨k, hk, fun l hl => Nat.le_of_not_lt (fun hlt => hs ⟨l, hlt, hl⟩)⟩

/-- Minimize over shortest paths to members of one lower blossom. If such a
path first reaches the high suffix, replacing its dishonest prefix by a shortest
path would give a smaller candidate. At the minimum, the original high-suffix
prefix is shortest to a lower member, contradicting its established boundary. -/
theorem lower_blossom_avoids_high_suffix (p : AltPath M) (hp : p.Shortest)
    (hpe : p.length % 2 = 0) (O : Nat)
    (c : V) (C : Nat)
    (hchigh : levelLT (some (p.length + O - 2)) (tenacity M c))
    (hcmin : minlevel M c = some C)
    (hconf : ∀ (b v : V), Blossom M (p.length + O - 2) b v →
      levelLT (some (p.length + O - 2)) (tenacity M b) →
      ∀ r : AltSegment M, r.Shortest → r.first = b → r.last = v →
        ∀ w, r.Contains w → w = b ∨ Blossom M (p.length + O - 2) b w)
    (B : Fin (p.length + 1)) (hBe : B.val % 2 = 0)
    (hBhigh : levelLT (some (p.length + O)) (tenacity M (p.vertex B)))
    (hBmin : minlevel M (p.vertex B) = some B.val)
    (hCB : C ≤ B.val) (hcB : c ≠ p.vertex B)
    (r₀ : AltPath M) (hr₀ : r₀.Shortest)
    (hmem₀ : Blossom M (p.length + O - 2) c r₀.last) (hlen₀ : r₀.length < O) :
    ∀ (a : Fin (p.length + 1)) (j : Fin (r₀.length + 1)),
      B.val < a.val → p.vertex a ≠ r₀.vertex j := by
  intro a j hBa heq
  let P := fun n => ∃ r : AltPath M, r.length = n ∧ r.Shortest ∧
    Blossom M (p.length + O - 2) c r.last ∧
    ∃ (a : Fin (p.length + 1)) (j : Fin (r.length + 1)), B.val < a.val ∧ p.vertex a = r.vertex j
  have hr₀P : P r₀.length := ⟨r₀, rfl, hr₀, hmem₀, a, j, hBa, heq⟩
  obtain ⟨N, ⟨r, hrN, hr, hmem, a', j', hBa', heq'⟩, hleast⟩ :=
    least_candidate_length P ⟨r₀.length, hr₀P⟩
  have hNlt : N < O := by have := hleast r₀.length hr₀P; omega
  obtain ⟨h⟩ := firstHit_exists r p (B.val + 1)
    ⟨j', a', by omega, heq'.symm⟩
  have hBlo : levelLT (some (p.length + O - 2)) (tenacity M (p.vertex B)) := by
    cases hb : tenacity M (p.vertex B) with
    | none => trivial
    | some s =>
      have hs : p.length + O < s := by simpa only [hb, levelLT] using hBhigh
      change p.length + O - 2 < s
      omega
  have habsent := high_vertex_absent_of_lower_blossom
    (p.length + O - 2) c (p.vertex B) C B.val hcmin hBmin hCB hcB hchigh hBlo r hr hmem
  have hh := p.first_high_suffix_hit_le_of_length_le r hp hpe B hBe (p.length + O)
    (by omega) hBhigh habsent h
  obtain ⟨k, hk, _, _, hkmin, _⟩ := blossom_on_shortest
    (p.length + O - 2) c r.last hmem r rfl hr
  have hkC : k.val = C := Option.some.inj (hkmin.symm.trans hcmin)
  have hkJ : k.val < h.qi.val := by have := h.in_suffix; omega
  have hhitmem := r.blossom_suffix_mem (p.length + O - 2) c r.last hmem hchigh hconf
    rfl hr k h.qi hk hkJ
  have hprefix : HasPathLength M 1 (r.vertex h.qi) h.qi.val := by
    simpa only [hh.1] using r.prefix_witness h.qi
  have hfinite : ∃ L, oddlevel M (r.vertex h.qi) = some L := by
    cases he : oddlevel M (r.vertex h.qi) with
    | none => exact False.elim ((level_eq_none_iff M 1 (r.vertex h.qi)).1 he ⟨_, hprefix⟩)
    | some L => exact ⟨L, rfl⟩
  obtain ⟨L, hL⟩ := hfinite
  have hshort := (level_eq_some_iff M 1 (r.vertex h.qi) L).1 hL
  have hLJ := hshort.2 h.qi.val hprefix
  obtain ⟨s, hslast, hslen, hspar⟩ := hshort.1
  have hsshort : s.Shortest := by simpa only [Shortest, hslen, hspar, hslast] using hshort
  have hsP : P L := by
    refine ⟨s, hslen, hsshort, ?_, h.pi, ⟨s.length, by omega⟩, ?_, ?_⟩
    · rw [hslast]
      exact hhitmem
    · have := h.in_suffix
      omega
    · change p.vertex h.pi = s.last
      exact h.hit.symm.trans hslast.symm
  have hNL := hleast L hsP
  have hJbound := h.qi.isLt
  have hJN : h.qi.val = N := by omega
  have hLN : L = N := by omega
  have hpiw : HasPathLength M 1 (r.vertex h.qi) h.pi.val := by
    rw [h.hit]
    simpa only [hh.2.1] using p.prefix_witness h.pi
  have hLI := hshort.2 h.pi.val hpiw
  have hIL : h.pi.val = L := by omega
  let z := p.take h.pi.val (by omega)
  have hzlast : z.last = r.vertex h.qi := h.hit.symm
  have hzlen : z.length = L := hIL
  have hzshort : z.Shortest := by simpa only [Shortest, hzlen, hspar, hzlast] using hshort
  have hzmem : Blossom M (p.length + O - 2) c z.last := by rw [hzlast]; exact hhitmem
  have hzabsent := high_vertex_absent_of_lower_blossom
    (p.length + O - 2) c (p.vertex B) C B.val hcmin hBmin hCB hcB hchigh hBlo z hzshort hzmem
  exact hzabsent ⟨B.val, by change B.val < h.pi.val + 1; have := h.in_suffix; omega⟩ rfl


/-- A lower predecessor blossom whose boundary is no later than a high even
vertex must have that high vertex as its boundary. This includes the formerly
problematic case where the lower boundary already occurs on the even path. -/
theorem lower_boundary_before_high_eq (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (hconf : ∀ (b v : V), Blossom M (p.length + q.length - 2) b v →
      levelLT (some (p.length + q.length - 2)) (tenacity M b) →
      ∀ r : AltSegment M, r.Shortest → r.first = b → r.last = v →
        ∀ w, r.Contains w → w = b ∨ Blossom M (p.length + q.length - 2) b w)
    (c : V) (hc : Blossom M (p.length + q.length - 2) c
      (q.vertex ⟨q.length - 1, by omega⟩))
    (hchigh : levelLT (some (p.length + q.length - 2)) (tenacity M c))
    (i : Fin (q.length + 1)) (hci : q.vertex i = c)
    (B : Fin (p.length + 1)) (hBe : B.val % 2 = 0)
    (hBhigh : levelLT (some (p.length + q.length)) (tenacity M (p.vertex B)))
    (hiB : i.val ≤ B.val) : c = p.vertex B := by
  apply Classical.byContradiction
  intro hcB
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hBmin := (p.limited_bfs_honesty hp B (by rw [hten]; exact levelLT_le hBhigh)).2
    (by rw [hten]; exact hBhigh)
  have hBlo : levelLT (some (p.length + q.length - 2)) (tenacity M (p.vertex B)) := by
    cases hb : tenacity M (p.vertex B) with
    | none => trivial
    | some s =>
      have hs : p.length + q.length < s := by simpa only [hb, levelLT] using hBhigh
      change p.length + q.length - 2 < s
      omega
  let q₀ := q.take (q.length - 1) (by omega)
  have hqeven : evenlevel M q.last = some p.length := by
    rw [hend]
    exact (level_eq_some_iff M 0 p.last p.length).2
      (by simpa only [Shortest, hpe] using hp)
  have hqodd : oddlevel M q.last = some q.length :=
    (level_eq_some_iff M 1 q.last q.length).2 (by simpa only [Shortest, hqo] using hq)
  have hqmin : minlevel M q.last = some q.length := by
    simp only [minlevel, hqeven, hqodd, levelMin]
    exact congrArg some (Nat.min_eq_right (by omega))
  have hq₀ : q₀.Shortest := q.minlevel_last_predecessor_honest hqmin (by omega)
  obtain ⟨k, hk, _, hklt, hkmin, _⟩ :=
    blossom_on_shortest (p.length + q.length - 2) c q₀.last hc q₀ rfl hq₀
  have hki : k.val = i.val := congrArg Fin.val
    (q.injective ⟨k.val, by have := k.isLt; change k.val < q.length - 1 + 1 at this; omega⟩ i
      (hk.trans hci.symm))
  have hcmin : minlevel M c = some i.val := by simpa only [hki] using hkmin
  have hBabs₀ := high_vertex_absent_of_lower_blossom (p.length + q.length - 2)
    c (p.vertex B) i.val B.val hcmin hBmin hiB hcB hchigh hBlo q₀ hq₀ hc
  have hBneqv : p.last ≠ p.vertex B := by
    intro he
    rw [← he, hten] at hBhigh
    change p.length + q.length < p.length + q.length at hBhigh
    omega
  have hBabs : ∀ a, q.vertex a ≠ p.vertex B := by
    intro a he
    by_cases ha : a.val < q.length
    · exact hBabs₀ ⟨a.val, by change a.val < q.length - 1 + 1; omega⟩ he
    · have ha' : a = ⟨q.length, by omega⟩ := Fin.ext (by change a.val = q.length; omega)
      have hh : q.vertex a = p.last := by rw [ha']; exact hend
      exact hBneqv (hh.symm.trans he)
  have hBE : B.val < p.length := by
    by_cases he : B.val = p.length
    · have he' : B = ⟨p.length, by omega⟩ := Fin.ext he
      exact False.elim (hBneqv ((congrArg p.vertex he').symm))
    · omega
  obtain ⟨g⟩ := firstHit_exists q p (B.val + 1)
    ⟨⟨q.length, by omega⟩, ⟨p.length, by omega⟩, by change B.val + 1 ≤ p.length; omega, hend⟩
  have hg := p.first_high_suffix_hit_le_of_length_le q hp hpe B hBe (p.length + q.length)
    (Nat.le_refl _) hBhigh hBabs g
  have hgq : g.qi.val < q.length := by
    by_cases he : g.qi.val = q.length
    · have he' : g.qi = ⟨q.length, by omega⟩ := Fin.ext he
      have hh : p.vertex g.pi = p.last := by rw [← g.hit, he']; exact hend
      have hpidx := congrArg Fin.val (p.injective g.pi ⟨p.length, by omega⟩ hh)
      change g.pi.val = p.length at hpidx
      omega
    · have := g.qi.isLt
      omega
  have havoid := p.lower_blossom_avoids_high_suffix hp hpe q.length c i.val hchigh hcmin hconf
    B hBe hBhigh hBmin hiB hcB q₀ hq₀ hc (by change q.length - 1 < q.length; omega)
  exact havoid g.pi ⟨g.qi.val, by change g.qi.val < q.length - 1 + 1; omega⟩
    (by have := g.in_suffix; omega) g.hit.symm

/-- A generic minimum-length argument for a blossom whose short shortest paths
are closed after its boundary. If such a
path first reaches the high suffix, replacing its dishonest prefix by a shortest
path would give a smaller candidate. At the minimum, the original high-suffix
prefix is shortest to a lower member, contradicting its established boundary. The closure premise is a precise
local path property used by the current-threshold induction. -/
theorem short_closed_blossom_avoids_high_suffix (p : AltPath M) (hp : p.Shortest)
    (hpe : p.length % 2 = 0) (O : Nat)
    (c : V) (C : Nat)
    (hchigh : levelLT (some (p.length + O)) (tenacity M c))
    (hcmin : minlevel M c = some C)
    (hclosed : ∀ r : AltPath M, r.Shortest → Blossom M (p.length + O) c r.last →
      r.length < O → ∀ (i j : Fin (r.length + 1)), r.vertex i = c → i.val < j.val →
        Blossom M (p.length + O) c (r.vertex j))
    (B : Fin (p.length + 1)) (hBe : B.val % 2 = 0)
    (hBhigh : levelLT (some (p.length + O)) (tenacity M (p.vertex B)))
    (hBmin : minlevel M (p.vertex B) = some B.val)
    (hCB : C ≤ B.val) (hcB : c ≠ p.vertex B)
    (r₀ : AltPath M) (hr₀ : r₀.Shortest)
    (hmem₀ : Blossom M (p.length + O) c r₀.last) (hlen₀ : r₀.length < O) :
    ∀ (a : Fin (p.length + 1)) (j : Fin (r₀.length + 1)),
      B.val < a.val → p.vertex a ≠ r₀.vertex j := by
  intro a j hBa heq
  let P := fun n => ∃ r : AltPath M, r.length = n ∧ r.Shortest ∧
    Blossom M (p.length + O) c r.last ∧
    ∃ (a : Fin (p.length + 1)) (j : Fin (r.length + 1)), B.val < a.val ∧ p.vertex a = r.vertex j
  have hr₀P : P r₀.length := ⟨r₀, rfl, hr₀, hmem₀, a, j, hBa, heq⟩
  obtain ⟨N, ⟨r, hrN, hr, hmem, a', j', hBa', heq'⟩, hleast⟩ :=
    least_candidate_length P ⟨r₀.length, hr₀P⟩
  have hNlt : N < O := by have := hleast r₀.length hr₀P; omega
  obtain ⟨h⟩ := firstHit_exists r p (B.val + 1)
    ⟨j', a', by omega, heq'.symm⟩
  have habsent := high_vertex_absent_of_lower_blossom
    (p.length + O) c (p.vertex B) C B.val hcmin hBmin hCB hcB hchigh hBhigh r hr hmem
  have hh := p.first_high_suffix_hit_le_of_length_le r hp hpe B hBe (p.length + O)
    (by omega) hBhigh habsent h
  obtain ⟨k, hk, _, _, hkmin, _⟩ := blossom_on_shortest
    (p.length + O) c r.last hmem r rfl hr
  have hkC : k.val = C := Option.some.inj (hkmin.symm.trans hcmin)
  have hkJ : k.val < h.qi.val := by have := h.in_suffix; omega
  have hhitmem := hclosed r hr hmem (by omega) k h.qi hk hkJ
  have hprefix : HasPathLength M 1 (r.vertex h.qi) h.qi.val := by
    simpa only [hh.1] using r.prefix_witness h.qi
  have hfinite : ∃ L, oddlevel M (r.vertex h.qi) = some L := by
    cases he : oddlevel M (r.vertex h.qi) with
    | none => exact False.elim ((level_eq_none_iff M 1 (r.vertex h.qi)).1 he ⟨_, hprefix⟩)
    | some L => exact ⟨L, rfl⟩
  obtain ⟨L, hL⟩ := hfinite
  have hshort := (level_eq_some_iff M 1 (r.vertex h.qi) L).1 hL
  have hLJ := hshort.2 h.qi.val hprefix
  obtain ⟨s, hslast, hslen, hspar⟩ := hshort.1
  have hsshort : s.Shortest := by simpa only [Shortest, hslen, hspar, hslast] using hshort
  have hsP : P L := by
    refine ⟨s, hslen, hsshort, ?_, h.pi, ⟨s.length, by omega⟩, ?_, ?_⟩
    · rw [hslast]
      exact hhitmem
    · have := h.in_suffix
      omega
    · change p.vertex h.pi = s.last
      exact h.hit.symm.trans hslast.symm
  have hNL := hleast L hsP
  have hJbound := h.qi.isLt
  have hJN : h.qi.val = N := by omega
  have hLN : L = N := by omega
  have hpiw : HasPathLength M 1 (r.vertex h.qi) h.pi.val := by
    rw [h.hit]
    simpa only [hh.2.1] using p.prefix_witness h.pi
  have hLI := hshort.2 h.pi.val hpiw
  have hIL : h.pi.val = L := by omega
  let z := p.take h.pi.val (by omega)
  have hzlast : z.last = r.vertex h.qi := h.hit.symm
  have hzlen : z.length = L := hIL
  have hzshort : z.Shortest := by simpa only [Shortest, hzlen, hspar, hzlast] using hshort
  have hzmem : Blossom M (p.length + O) c z.last := by rw [hzlast]; exact hhitmem
  have hzabsent := high_vertex_absent_of_lower_blossom
    (p.length + O) c (p.vertex B) C B.val hcmin hBmin hCB hcB hchigh hBhigh z hzshort hzmem
  exact hzabsent ⟨B.val, by change B.val < h.pi.val + 1; have := h.in_suffix; omega⟩ rfl



/-- The predecessor's established current-threshold blossom determines every
high even vertex no earlier than its boundary, whenever short shortest paths
through that blossom satisfy the local closure property. -/
theorem short_closed_blossom_boundary_eq (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (c : V) (hc : Blossom M (p.length + q.length) c
      (q.vertex ⟨q.length - 1, by omega⟩))
    (hchigh : levelLT (some (p.length + q.length)) (tenacity M c))
    (hclosed : ∀ r : AltPath M, r.Shortest → Blossom M (p.length + q.length) c r.last →
      r.length < q.length → ∀ (i j : Fin (r.length + 1)), r.vertex i = c → i.val < j.val →
        Blossom M (p.length + q.length) c (r.vertex j))
    (i : Fin (q.length + 1)) (hci : q.vertex i = c)
    (B : Fin (p.length + 1)) (hBe : B.val % 2 = 0)
    (hBhigh : levelLT (some (p.length + q.length)) (tenacity M (p.vertex B)))
    (hiB : i.val ≤ B.val) : c = p.vertex B := by
  apply Classical.byContradiction
  intro hcB
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hBmin := (p.limited_bfs_honesty hp B (by rw [hten]; exact levelLT_le hBhigh)).2
    (by rw [hten]; exact hBhigh)
  let q₀ := q.take (q.length - 1) (by omega)
  have hqeven : evenlevel M q.last = some p.length := by
    rw [hend]
    exact (level_eq_some_iff M 0 p.last p.length).2
      (by simpa only [Shortest, hpe] using hp)
  have hqodd : oddlevel M q.last = some q.length :=
    (level_eq_some_iff M 1 q.last q.length).2 (by simpa only [Shortest, hqo] using hq)
  have hqmin : minlevel M q.last = some q.length := by
    simp only [minlevel, hqeven, hqodd, levelMin]
    exact congrArg some (Nat.min_eq_right (by omega))
  have hq₀ : q₀.Shortest := q.minlevel_last_predecessor_honest hqmin (by omega)
  obtain ⟨k, hk, _, hklt, hkmin, _⟩ :=
    blossom_on_shortest (p.length + q.length) c q₀.last hc q₀ rfl hq₀
  have hki : k.val = i.val := congrArg Fin.val
    (q.injective ⟨k.val, by have := k.isLt; change k.val < q.length - 1 + 1 at this; omega⟩ i
      (hk.trans hci.symm))
  have hcmin : minlevel M c = some i.val := by simpa only [hki] using hkmin
  have hBabs₀ := high_vertex_absent_of_lower_blossom (p.length + q.length)
    c (p.vertex B) i.val B.val hcmin hBmin hiB hcB hchigh hBhigh q₀ hq₀ hc
  have hBneqv : p.last ≠ p.vertex B := by
    intro he
    rw [← he, hten] at hBhigh
    change p.length + q.length < p.length + q.length at hBhigh
    omega
  have hBabs : ∀ a, q.vertex a ≠ p.vertex B := by
    intro a he
    by_cases ha : a.val < q.length
    · exact hBabs₀ ⟨a.val, by change a.val < q.length - 1 + 1; omega⟩ he
    · have ha' : a = ⟨q.length, by omega⟩ := Fin.ext (by change a.val = q.length; omega)
      have hh : q.vertex a = p.last := by rw [ha']; exact hend
      exact hBneqv (hh.symm.trans he)
  have hBE : B.val < p.length := by
    by_cases he : B.val = p.length
    · have he' : B = ⟨p.length, by omega⟩ := Fin.ext he
      exact False.elim (hBneqv ((congrArg p.vertex he').symm))
    · omega
  obtain ⟨g⟩ := firstHit_exists q p (B.val + 1)
    ⟨⟨q.length, by omega⟩, ⟨p.length, by omega⟩, by change B.val + 1 ≤ p.length; omega, hend⟩
  have hg := p.first_high_suffix_hit_le_of_length_le q hp hpe B hBe (p.length + q.length)
    (Nat.le_refl _) hBhigh hBabs g
  have hgq : g.qi.val < q.length := by
    by_cases he : g.qi.val = q.length
    · have he' : g.qi = ⟨q.length, by omega⟩ := Fin.ext he
      have hh : p.vertex g.pi = p.last := by rw [← g.hit, he']; exact hend
      have hpidx := congrArg Fin.val (p.injective g.pi ⟨p.length, by omega⟩ hh)
      change g.pi.val = p.length at hpidx
      omega
    · have := g.qi.isLt
      omega
  have havoid := p.short_closed_blossom_avoids_high_suffix hp hpe q.length c i.val hchigh hcmin hclosed
    B hBe hBhigh hBmin hiB hcB q₀ hq₀ hc (by change q.length - 1 < q.length; omega)
  exact havoid g.pi ⟨g.qi.val, by change g.qi.val < q.length - 1 + 1; omega⟩
    (by have := g.in_suffix; omega) g.hit.symm



/-- Instantiate the minimum-candidate boundary argument using only the lower
confinement induction and current bases at strictly smaller minimum levels. -/
theorem current_blossom_boundary_eq (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ p.length + q.length - 2 →
      ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (p.length + q.length - 2) b v →
      levelLT (some (p.length + q.length - 2)) (tenacity M b) →
      ∀ r : AltSegment M, r.Shortest → r.first = b → r.last = v →
        ∀ w, r.Contains w → w = b ∨ Blossom M (p.length + q.length - 2) b w)
    (hcurrent : ∀ (v : V) (k : Nat), minlevel M v = some k → k < q.length →
      tenacity M v = some (p.length + q.length) → ∃ b, IsBase M v b)
    (c : V) (hc : Blossom M (p.length + q.length) c
      (q.vertex ⟨q.length - 1, by omega⟩))
    (hchigh : levelLT (some (p.length + q.length)) (tenacity M c))
    (i : Fin (q.length + 1)) (hci : q.vertex i = c)
    (B : Fin (p.length + 1)) (hBe : B.val % 2 = 0)
    (hBhigh : levelLT (some (p.length + q.length)) (tenacity M (p.vertex B)))
    (hiB : i.val ≤ B.val) : c = p.vertex B := by
  apply p.short_closed_blossom_boundary_eq q hp hq hpe hqo hend hinner c hc hchigh
    ?_ i hci B hBe hBhigh hiB
  intro r hr hbl hlen a j ha haj
  exact r.short_blossom_suffix_mem hr (p.length + q.length) q.length
    (by omega) hlen (by omega) hexists hconf hcurrent c hchigh hbl a j ha haj

end MaximumMatching.AltPath

end GeneralStructureMinimize

section GeneralStructureOrdered

/-! The ordered common-base step. Lower-tenacity base existence and confinement,
plus bases at smaller current minimum levels, determine opposite path bases
whenever the odd path's base is no later than the even path's base. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- In the lower-predecessor case, actual path bases agree when their minimum
levels are ordered from the odd path to the even path. -/
theorem low_predecessor_bases_eq_of_minlevel_le (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ p.length + q.length - 2 →
      ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (p.length + q.length - 2) b v →
      levelLT (some (p.length + q.length - 2)) (tenacity M b) →
      ∀ r : AltSegment M, r.Shortest → r.first = b → r.last = v →
        ∀ w, r.Contains w → w = b ∨ Blossom M (p.length + q.length - 2) b w)
    (ih : ∀ (v : V) (k : Nat), minlevel M v = some k → k < q.length →
      tenacity M v = some (p.length + q.length) → HasUniqueBase M v (p.length + q.length))
    (s : Nat) (hs : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) = some s)
    (hst : s < p.length + q.length)
    (b d : V) (hpb : p.BaseOnPath (p.length + q.length) b)
    (hqd : q.BaseOnPath (p.length + q.length) d)
    (horder : levelLE (minlevel M d) (minlevel M b)) : b = d := by
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hqten : tenacity M q.last = some (p.length + q.length) := by rw [hend]; exact hten
  obtain ⟨B, hBb, hBe⟩ := p.baseOnPath_even (p.length + q.length) hten hpb
  obtain ⟨D, hDd, hdhigh, hdlast⟩ := hqd
  have hbhigh := hpb.choose_spec.2.1
  have hBhigh : levelLT (some (p.length + q.length)) (tenacity M (p.vertex B)) := by
    rw [hBb]
    exact hbhigh
  have hBmin : minlevel M b = some B.val := by
    have hh := (p.limited_bfs_honesty hp B (by rw [hten]; exact levelLT_le hBhigh)).2
      (by rw [hten]; exact hBhigh)
    simpa only [hBb] using hh
  have hDmin : minlevel M d = some D.val := by
    have hh := (q.limited_bfs_honesty hq D (by rw [hqten, hDd]; exact levelLT_le hdhigh)).2
      (by rw [hqten, hDd]; exact hdhigh)
    simpa only [hDd] using hh
  have hDB : D.val ≤ B.val := by simpa only [hDmin, hBmin, levelLE] using horder
  have hcurrent : ∀ (v : V) (k : Nat), minlevel M v = some k → k < q.length →
      tenacity M v = some (p.length + q.length) → ∃ a, IsBase M v a := by
    intro v k hmin hk ht
    obtain ⟨a, ha, _⟩ := ih v k hmin hk ht
    exact ⟨a, p.length + q.length, ht, ha⟩
  have hmember := p.low_predecessor_in_base_blossom q hp hq hpe hqo hend hinner
    hexists ih s hs hst d ⟨D, hDd, hdhigh, hdlast⟩
  have heq := p.current_blossom_boundary_eq q hp hq hpe hqo hend hinner
    hexists hconf hcurrent d hmember hdhigh D hDd B hBe hBhigh hDB
  exact hBb.symm.trans heq.symm

/-- All predecessor cases are included in this ordered step. The opposite
order is handled in GeneralStructureStep using the even-witness minimization. -/
theorem parity_bases_eq_of_minlevel_le (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ p.length + q.length - 2 →
      ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (p.length + q.length - 2) b v →
      levelLT (some (p.length + q.length - 2)) (tenacity M b) →
      ∀ r : AltSegment M, r.Shortest → r.first = b → r.last = v →
        ∀ w, r.Contains w → w = b ∨ Blossom M (p.length + q.length - 2) b w)
    (ih : ∀ (v : V) (k : Nat), minlevel M v = some k → k < q.length →
      tenacity M v = some (p.length + q.length) → HasUniqueBase M v (p.length + q.length))
    (b d : V) (hpb : p.BaseOnPath (p.length + q.length) b)
    (hqd : q.BaseOnPath (p.length + q.length) d)
    (horder : levelLE (minlevel M d) (minlevel M b)) : b = d := by
  by_cases hge : levelLE (some (p.length + q.length))
      (tenacity M (q.vertex ⟨q.length - 1, by omega⟩))
  · have hqb := (p.parity_bases_agree_of_predecessor_ge q hp hq hpe hqo hend hinner hge ih b).1 hpb
    exact q.baseOnPath_unique _ b d hqb hqd
  · cases hs : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) with
    | none => exact False.elim (hge (by rw [hs]; trivial))
    | some s =>
      have hst : s < p.length + q.length := by
        have hh : ¬p.length + q.length ≤ s := by simpa only [hs, levelLE] using hge
        omega
      exact p.low_predecessor_bases_eq_of_minlevel_le q hp hq hpe hqo hend hinner
        hexists hconf ih s hs hst b d hpb hqd horder

end MaximumMatching.AltPath

end GeneralStructureOrdered

section GeneralStructureEvenMinimize

namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

private theorem least_even_candidate (P : Nat → Prop) (h : ∃ k, P k) :
    ∃ k, P k ∧ ∀ l, P l → k ≤ l := by
  classical
  obtain ⟨k, hk⟩ := h
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hs : ∃ l, l < k ∧ P l
    · obtain ⟨l, hl, hp⟩ := hs
      exact ih l hl hp
    · exact ⟨k, hk, fun l hl => Nat.le_of_not_lt (fun hlt => hs ⟨l, hlt, hl⟩)⟩

/-- An absent high boundary cannot have a short even shortest path to a blossom
member on the opposite even shortest path. Minimum-length candidates force a
single final matched intersection; two reverse splices then lower its tenacity. -/
theorem no_even_candidate_at_absent_boundary (p : AltPath M) (hp : p.Shortest)
    (hpe : p.length % 2 = 0) (O : Nat) (d : V)
    (hd : levelLT (some (p.length + O)) (tenacity M d))
    (hclosed : ∀ r : AltPath M, r.Shortest → Blossom M (p.length + O) d r.last →
      r.length < O → ∀ (i j : Fin (r.length + 1)), r.vertex i = d → i.val < j.val →
        Blossom M (p.length + O) d (r.vertex j))
    (habsent : ∀ a, p.vertex a ≠ d)
    (r₀ : AltPath M) (hr₀ : r₀.Shortest) (hr₀e : r₀.length % 2 = 0)
    (hmem₀ : Blossom M (p.length + O) d r₀.last)
    (hon₀ : ∃ a, p.vertex a = r₀.last) (hlen₀ : r₀.length < O) : False := by
  let P := fun n => ∃ r : AltPath M, r.length = n ∧ r.Shortest ∧ r.length % 2 = 0 ∧
    Blossom M (p.length + O) d r.last ∧ (∃ a, p.vertex a = r.last)
  have hr₀P : P r₀.length := ⟨r₀, rfl, hr₀, hr₀e, hmem₀, hon₀⟩
  obtain ⟨N, ⟨r, hrN, hr, hre, hmem, hon⟩, hleast⟩ := least_even_candidate P ⟨_, hr₀P⟩
  have hNlt : N < O := by have := hleast r₀.length hr₀P; omega
  obtain ⟨D, hDd, hDe, hDN, _, _⟩ := blossom_on_shortest (p.length + O) d r.last hmem r rfl hr
  have havoid : ∀ (a : Fin (p.length + 1)) (j : Fin (r.length + 1)),
      D.val ≤ j.val → j.val < r.length - 1 → p.vertex a ≠ r.vertex j := by
    intro a j hDj hjN heq
    by_cases he : D.val = j.val
    · have he' : D = j := Fin.ext he
      exact habsent a (heq.trans ((congrArg r.vertex he').symm.trans hDd))
    · have hwmem := hclosed r hr hmem (by omega) D j hDd (by omega)
      obtain ⟨j', _, hm⟩ := r.even_suffix_matched_closed hre (D.val + 1) (by omega) j (by omega)
      obtain ⟨s, hs, hse, hsmem, hson, hlen⟩ := p.even_shortest_blossom_candidate hpe
        (p.length + O) d (r.vertex j) (r.vertex j') j.val hwmem hm ⟨a, heq⟩ (r.prefix_witness j)
      have hmin := hleast s.length ⟨s, rfl, hs, hse, hsmem, hson⟩
      omega
  obtain ⟨a, ha⟩ := hon
  obtain ⟨h⟩ := firstHit_exists p r (D.val + 1)
    ⟨a, ⟨r.length, by omega⟩, by change D.val + 1 ≤ r.length; omega, ha⟩
  have hd' : levelLT (some (p.length + O)) (tenacity M (r.vertex D)) := by rw [hDd]; exact hd
  have habs' : ∀ a, p.vertex a ≠ r.vertex D := by intro a; rw [hDd]; exact habsent a
  have hh := r.first_high_suffix_hit_le_of_length_le p hr hre D hDe (p.length + O)
    (by omega) hd' habs' h
  have hJ : h.pi.val = r.length - 1 := by
    by_cases hj : h.pi.val < r.length - 1
    · exact False.elim (havoid h.qi h.pi (by have := h.in_suffix; omega) hj h.hit)
    · have := h.pi.isLt
      omega
  have hjoin : p.vertex h.qi = r.vertex ⟨r.length - 1, by omega⟩ := by
    have hj : h.pi = ⟨r.length - 1, by omega⟩ := Fin.ext hJ
    simpa only [hj] using h.hit
  let r₁ := r.take (r.length - 1) (by omega)
  have hr₁len : r₁.length = r.length - 1 := rfl
  have hr₁end : r₁.last = p.vertex h.qi := hjoin.symm
  have hr₁odd : r₁.length % 2 = 1 := by omega
  have hr₁short : r₁.Shortest := by
    have hm := r.even_last_mate hre (by omega)
    have he : r.length - 1 + 1 = r.length := by omega
    have hs := (matched_shortest_iff M (M.symm hm) (r.length - 1)).1
      (by rw [he]; simpa only [Shortest, hre] using hr)
    change IsShortest M (r₁.length % 2) r₁.last r₁.length
    rw [hr₁odd]
    exact hs
  have hIstrict : r.length - 1 < h.qi.val := by
    by_cases he : h.qi.val = r.length - 1
    · let z := p.take h.qi.val (by omega)
      have hzshort : z.Shortest := by
        have hsame : z.length = r₁.length := by change h.qi.val = r.length - 1; exact he
        have hzlast : z.last = r₁.last := hr₁end.symm
        simpa only [Shortest, hsame, hzlast] using hr₁short
      have hzmem : Blossom M (p.length + O) d z.last := by
        have hzlast : z.last = r.vertex ⟨r.length - 1, by omega⟩ := hjoin
        rw [hzlast]
        exact hclosed r hr hmem (by omega) D ⟨r.length - 1, by omega⟩ hDd
          (by change D.val < r.length - 1; omega)
      obtain ⟨k, hk, _, _, _, _⟩ := blossom_on_shortest (p.length + O) d z.last hzmem z rfl hzshort
      exact False.elim (habsent ⟨k.val, by have := k.isLt; change k.val < h.qi.val + 1 at this; omega⟩ hk)
    · omega
  obtain ⟨k, j, hIj, hkj⟩ := p.shorter_prefix_intersects hp h.qi.val (by omega)
    r₁ hr₁end (by omega) (by omega)
  have hlast : p.vertex ⟨h.qi.val + 1, by omega⟩ = r.last := by
    have hpnext := p.mate_next h.qi.val (by omega) hh.1
    have hrnext := r.mate_next (r.length - 1) (by omega) (by omega)
    rw [hjoin] at hpnext
    have hm := M.mate_unique hpnext hrnext
    simpa only [show r.length - 1 + 1 = r.length by omega, last] using hm
  have hjcut : h.qi.val + 2 ≤ j.val := by
    by_cases he : j.val = h.qi.val + 1
    · have he' : j = ⟨h.qi.val + 1, by omega⟩ := Fin.ext he
      rw [he', hlast] at hkj
      have heq := congrArg Fin.val (r.injective ⟨k.val, by have := k.isLt; change k.val < r.length - 1 + 1 at this; omega⟩
        ⟨r.length, by omega⟩ hkj)
      have hkb := k.isLt
      change k.val < r.length - 1 + 1 at hkb
      change k.val = r.length at heq
      omega
    · omega
  obtain ⟨g⟩ := firstHit_exists r p (h.qi.val + 2)
    ⟨⟨k.val, by have := k.isLt; change k.val < r.length - 1 + 1 at this; omega⟩, j, hjcut, hkj⟩
  have hK : g.qi.val < D.val := by
    by_cases hg : g.qi.val < r.length - 1
    · by_cases hKD : g.qi.val < D.val
      · exact hKD
      · exact False.elim (havoid g.pi g.qi (by omega) hg g.hit.symm)
    · by_cases he : g.qi.val = r.length - 1
      · have he' : g.qi = ⟨r.length - 1, by omega⟩ := Fin.ext he
        have ghit := g.hit
        rw [he', ← hjoin] at ghit
        have hpidx := congrArg Fin.val (p.injective h.qi g.pi ghit)
        have := g.in_suffix
        omega
      · have he : g.qi = ⟨r.length, by omega⟩ := Fin.ext (by have := g.qi.isLt; change g.qi.val = r.length; omega)
        have hv : r.vertex g.qi = r.last := by rw [he]; rfl
        have hpidx := congrArg Fin.val (p.injective ⟨h.qi.val + 1, by omega⟩ g.pi
          (hlast.trans (hv.symm.trans g.hit)))
        have := g.in_suffix
        change h.qi.val + 1 = g.pi.val at hpidx
        omega
  obtain ⟨s, hs, hbound⟩ := p.double_reverse_boundary_bound_of_firstHit r hp hpe hre D hDe
    h.qi.val O (by omega) hh.1 (by omega) (by omega) hjoin havoid g hK
  rw [hs] at hd'
  change p.length + O < s at hd'
  omega

end MaximumMatching.AltPath

end GeneralStructureEvenMinimize

section GeneralStructureStep

/-! The full current-tenacity inner induction step. Lower blossoms and bases at
smaller current minimum levels imply agreement of both shortest path parities,
including every low-predecessor case and either ordering of path bases. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The odd path's actual base occurs on every opposite even shortest path,
including when its last predecessor lies in a lower-tenacity blossom. -/
theorem low_predecessor_base_occurs (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ p.length + q.length - 2 →
      ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (p.length + q.length - 2) b v →
      levelLT (some (p.length + q.length - 2)) (tenacity M b) →
      ∀ r : AltSegment M, r.Shortest → r.first = b → r.last = v →
        ∀ w, r.Contains w → w = b ∨ Blossom M (p.length + q.length - 2) b w)
    (ih : ∀ (v : V) (k : Nat), minlevel M v = some k → k < q.length →
      tenacity M v = some (p.length + q.length) → HasUniqueBase M v (p.length + q.length))
    (s : Nat) (hs : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) = some s)
    (hst : s < p.length + q.length) (d : V) (hqd : q.BaseOnPath (p.length + q.length) d) :
    ∃ a, p.vertex a = d := by
  apply Classical.byContradiction
  intro hn
  have habsent : ∀ a, p.vertex a ≠ d := by intro a ha; exact hn ⟨a, ha⟩
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hqten : tenacity M q.last = some (p.length + q.length) := by rw [hend]; exact hten
  obtain ⟨D, hD, hDe⟩ := q.baseOnPath_even (p.length + q.length) hqten hqd
  have hdhigh := hqd.choose_spec.2.1
  have hmember := p.low_predecessor_in_base_blossom q hp hq hpe hqo hend hinner
    hexists ih s hs hst d hqd
  have hcurrent : ∀ (v : V) (k : Nat), minlevel M v = some k → k < q.length →
      tenacity M v = some (p.length + q.length) → ∃ a, IsBase M v a := by
    intro v k hmin hk ht
    obtain ⟨a, ha, _⟩ := ih v k hmin hk ht
    exact ⟨a, p.length + q.length, ht, ha⟩
  have hclosed : ∀ r : AltPath M, r.Shortest → Blossom M (p.length + q.length) d r.last →
      r.length < q.length → ∀ (i j : Fin (r.length + 1)), r.vertex i = d → i.val < j.val →
        Blossom M (p.length + q.length) d (r.vertex j) := by
    intro r hr hbl hlen i j hi hij
    exact r.short_blossom_suffix_mem hr (p.length + q.length) q.length (by omega)
      hlen (by omega) hexists hconf hcurrent d hdhigh hbl i j hi hij
  obtain ⟨r, hr, hre, hlen, hbl, hon⟩ := p.initial_even_blossom_candidate q hp hq hpe hqo
    hend hinner d D hD hDe hdhigh habsent hmember hclosed
  exact p.no_even_candidate_at_absent_boundary hp hpe q.length d hdhigh hclosed habsent
    r hr hre hbl hon hlen

/-- Actual bases of opposite shortest paths agree under the lower-tenacity
outer induction and strictly smaller-minlevel inner induction hypotheses. -/
theorem general_parity_bases_eq (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ p.length + q.length - 2 →
      ∃ a, IsBase M v a)
    (hconf : ∀ (a v : V), Blossom M (p.length + q.length - 2) a v →
      levelLT (some (p.length + q.length - 2)) (tenacity M a) →
      ∀ r : AltSegment M, r.Shortest → r.first = a → r.last = v →
        ∀ w, r.Contains w → w = a ∨ Blossom M (p.length + q.length - 2) a w)
    (ih : ∀ (v : V) (k : Nat), minlevel M v = some k → k < q.length →
      tenacity M v = some (p.length + q.length) → HasUniqueBase M v (p.length + q.length))
    (b d : V) (hpb : p.BaseOnPath (p.length + q.length) b)
    (hqd : q.BaseOnPath (p.length + q.length) d) : b = d := by
  by_cases hge : levelLE (some (p.length + q.length))
      (tenacity M (q.vertex ⟨q.length - 1, by omega⟩))
  · have hqb := (p.parity_bases_agree_of_predecessor_ge q hp hq hpe hqo hend hinner hge ih b).1 hpb
    exact q.baseOnPath_unique _ b d hqb hqd
  · have hlow : ∃ s, tenacity M (q.vertex ⟨q.length - 1, by omega⟩) = some s ∧
        s < p.length + q.length := by
      cases hs : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) with
      | none => exact False.elim (hge (by rw [hs]; trivial))
      | some s =>
        have hh : ¬p.length + q.length ≤ s := by simpa only [hs, levelLE] using hge
        exact ⟨s, rfl, by omega⟩
    obtain ⟨s, hs, hst⟩ := hlow
    obtain ⟨D, hD⟩ := p.low_predecessor_base_occurs q hp hq hpe hqo hend hinner
      hexists hconf ih s hs hst d hqd
    have hdhigh := hqd.choose_spec.2.1
    obtain ⟨B, hB, hbhigh, hlast⟩ := hpb
    have hDB : D.val ≤ B.val := by
      apply Nat.le_of_not_lt
      intro hlt
      exact hlast D hlt (by rw [hD]; exact hdhigh)
    have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
    have hBmin : minlevel M b = some B.val := by
      have hh := (p.limited_bfs_honesty hp B (by rw [hten, hB]; exact levelLT_le hbhigh)).2
        (by rw [hten, hB]; exact hbhigh)
      simpa only [hB] using hh
    have hDmin : minlevel M d = some D.val := by
      have hh := (p.limited_bfs_honesty hp D (by rw [hten, hD]; exact levelLT_le hdhigh)).2
        (by rw [hten, hD]; exact hdhigh)
      simpa only [hD] using hh
    exact p.low_predecessor_bases_eq_of_minlevel_le q hp hq hpe hqo hend hinner
      hexists hconf ih s hs hst b d ⟨B, hB, hbhigh, hlast⟩ hqd
      (by rw [hDmin, hBmin]; exact hDB)

/-- The full inner induction step, expressed as equality of the actual
path-relative base predicates. Eligibility supplies a base on each path. -/
theorem general_parity_bases_agree (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (ht : EligibleTenacity M (p.length + q.length))
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ p.length + q.length - 2 →
      ∃ a, IsBase M v a)
    (hconf : ∀ (a v : V), Blossom M (p.length + q.length - 2) a v →
      levelLT (some (p.length + q.length - 2)) (tenacity M a) →
      ∀ r : AltSegment M, r.Shortest → r.first = a → r.last = v →
        ∀ w, r.Contains w → w = a ∨ Blossom M (p.length + q.length - 2) a w)
    (ih : ∀ (v : V) (k : Nat), minlevel M v = some k → k < q.length →
      tenacity M v = some (p.length + q.length) → HasUniqueBase M v (p.length + q.length))
    (b : V) : p.BaseOnPath (p.length + q.length) b ↔ q.BaseOnPath (p.length + q.length) b := by
  constructor
  · intro hpb
    obtain ⟨d, hqd⟩ := q.baseOnPath_exists_of_eligible _ ht
    have he := p.general_parity_bases_eq q hp hq hpe hqo hend hinner hexists hconf ih b d hpb hqd
    exact he.symm ▸ hqd
  · intro hqb
    obtain ⟨d, hpd⟩ := p.baseOnPath_exists_of_eligible _ ht
    have he := p.general_parity_bases_eq q hp hq hpe hqo hend hinner hexists hconf ih d b hpd hqb
    exact he ▸ hpd

end MaximumMatching.AltPath

end GeneralStructureStep

section GeneralStructureBase

/-! The general common-base theorem's complete inner induction. Only the
strictly lower outer-induction base and confinement statements remain as
premises; no current-tenacity path agreement or base existence is assumed. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V}

/-- Every current-tenacity vertex has a unique common base once the actual
lower-tenacity base and blossom-confinement statements have been established. -/
theorem general_unique_base_of_lower (M : Matching G) (t : Nat)
    (ht : EligibleTenacity M t)
    (hexists : ∀ (w : V) (s : Nat), tenacity M w = some s → s ≤ t - 2 →
      ∃ b, IsBase M w b)
    (hconf : ∀ (b w : V), Blossom M (t - 2) b w → levelLT (some (t - 2)) (tenacity M b) →
      ∀ r : AltSegment M, r.Shortest → r.first = b → r.last = w →
        ∀ x, r.Contains x → x = b ∨ Blossom M (t - 2) b x)
    (v : V) (hvt : tenacity M v = some t) : HasUniqueBase M v t := by
  apply minimum_unique_base_induction M t ht ?_ v hvt
  intro u k hku hinner hut ih
  apply unique_base_of_parity_agreement M t ht u hut
  intro p q hpv hqv hp hq hpe hqo b
  have he : evenlevel M u = some p.length := by
    apply (level_eq_some_iff M 0 u p.length).2
    simpa only [AltPath.Shortest, hpe, hpv] using hp
  have ho : oddlevel M u = some q.length := by
    apply (level_eq_some_iff M 1 u q.length).2
    simpa only [AltPath.Shortest, hqo, hqv] using hq
  have hsum : p.length + q.length = t := by
    simpa only [tenacity, he, ho, levelAdd, Option.some.injEq] using hut
  have hinner' : q.length < p.length := by
    have hn := hinner.2
    simp only [Outer, he, ho, levelLT] at hn
    omega
  have hkq : k = q.length := by
    have hh : min p.length q.length = k := by
      simpa only [minlevel, he, ho, levelMin, Option.some.injEq] using hku
    omega
  subst t
  subst k
  exact p.general_parity_bases_agree q hp hq hpe hqo
    (hqv.trans hpv.symm) hinner' ht hexists hconf ih b


end MaximumMatching

end GeneralStructureBase

section GeneralStructureInduction

/-! Strong induction on eligible tenacity closes both common-base existence and
actual relative-path blossom confinement. Every lower induction hypothesis is
instantiated from the requested eligible cutoff and an actual finite member. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V}

/-- The simultaneous general common-base and blossom-confinement theorem. -/
theorem general_base_and_confinement (M : Matching G) : ∀ t : Nat,
    EligibleTenacity M t →
      (∀ v : V, tenacity M v = some t → HasUniqueBase M v t) ∧
      (∀ (b v : V), Blossom M t b v → levelLT (some t) (tenacity M b) →
        ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
          ∀ w, q.Contains w → w = b ∨ Blossom M t b w) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro ht
    have hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 →
        ∃ b, IsBase M v b := by
      intro v s hs hst
      have hsodd := tenacity_odd M v s hs
      have hst' : s < t := by have := ht.1; omega
      have helig : EligibleTenacity M s := by
        refine ⟨hsodd, ⟨v, ?_⟩, ?_⟩
        · rw [hs]
          exact Nat.le_refl _
        · intro p hp
          have htl := ht.2.2 p hp
          omega
      obtain ⟨b, hb, _⟩ := (ih s hst' helig).1 v hs
      exact ⟨b, s, hs, hb⟩
    have hconf : ∀ (b v : V), Blossom M (t - 2) b v →
        levelLT (some (t - 2)) (tenacity M b) →
        ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
          ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w := by
      intro b v hv hb q hq hqb hqv w hw
      obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound (t - 2) b v hv
      have hsodd := tenacity_odd M v s hs
      have hlt : t - 2 < t := by have := ht.1; omega
      have helig : EligibleTenacity M (t - 2) := by
        refine ⟨by have := ht.1; omega, ⟨v, ?_⟩, ?_⟩
        · rw [hs]
          exact hst
        · intro p hp
          have htl := ht.2.2 p hp
          omega
      exact (ih (t - 2) hlt helig).2 b v hv hb q hq hqb hqv w hw
    have hbase : ∀ v : V, tenacity M v = some t → HasUniqueBase M v t :=
      fun v hv => general_unique_base_of_lower M t ht hexists hconf v hv
    have hcurrent : ∀ v : V, tenacity M v = some t → ∃ b, IsBase M v b := by
      intro v hv
      obtain ⟨b, hb, _⟩ := hbase v hv
      exact ⟨b, t, hv, hb⟩
    refine ⟨hbase, ?_⟩
    intro b v hv hb q hq hqb hqv
    exact general_blossom_relative_confined_of_current t ht.1 hexists hconf hcurrent
      b v hv hb q hq hqb hqv

/-- Every vertex of eligible tenacity has a unique common base, with no
unproved structural premise or lower-tenacity oracle. -/
theorem general_unique_base (M : Matching G) (t : Nat) (ht : EligibleTenacity M t)
    (v : V) (hvt : tenacity M v = some t) : HasUniqueBase M v t :=
  (general_base_and_confinement M t ht).1 v hvt

/-- Every shortest relative path to a blossom member stays within that blossom
and its boundary, at every eligible cutoff. -/
theorem general_blossom_relative_confined (M : Matching G) (t : Nat) (ht : EligibleTenacity M t)
    (b v : V) (hv : Blossom M t b v) (hb : levelLT (some t) (tenacity M b))
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v) :
    ∀ w, q.Contains w → w = b ∨ Blossom M t b w :=
  (general_base_and_confinement M t ht).2 b v hv hb q hq hqb hqv

end MaximumMatching

end GeneralStructureInduction
