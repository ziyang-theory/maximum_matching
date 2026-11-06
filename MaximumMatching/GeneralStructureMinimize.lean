import MaximumMatching.GeneralStructureFirstHit
import MaximumMatching.GeneralShortConfinement

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
