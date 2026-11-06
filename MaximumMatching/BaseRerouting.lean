import MaximumMatching.GeneralBaseStructure
import MaximumMatching.GeneralPathGeometry
import MaximumMatching.MinScan

section GeneralBaseReroute

/-! Actual low-blossom rerouting with simple paths and exact lengths.
Opposite first-hit arguments derive avoidance when an absent lower boundary
lies no later than an absent high vertex on the opposite path. The remaining
boundary orders and present-boundary cases are not asserted here. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Above the preceding odd threshold means at least the current odd threshold,
since every finite vertex tenacity is odd. Infinite tenacity is included. -/
theorem tenacity_ge_of_above_previous_odd (v : V) (t : Nat) (ht : t % 2 = 1)
    (hv : levelLT (some (t - 2)) (tenacity M v)) :
    levelLE (some t) (tenacity M v) := by
  cases hs : tenacity M v with
  | none => trivial
  | some s =>
    have hsodd := tenacity_odd M v s hs
    have hbound : t - 2 < s := by simpa only [hs, levelLT] using hv
    change t ≤ s
    omega

namespace AltPath

/-- If the even maxlevel path avoids the lower boundary-to-predecessor segment,
its fresh predecessor extension followed by that segment in reverse is an
actual shortest odd path to the boundary. The boundary has the current tenacity,
and all threshold-base values of the even path are retained. -/
theorem disjoint_lower_boundary_reroute (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (c : V) (hc : Blossom M (p.length + q.length - 2) c
      (q.vertex ⟨q.length - 1, by omega⟩))
    (hchigh : levelLT (some (p.length + q.length - 2)) (tenacity M c))
    (i : Fin (q.length + 1)) (hci : q.vertex i = c)
    (hdis : ∀ (a : Fin (p.length + 1)) (j : Fin (q.length + 1)),
      i.val ≤ j.val → j.val < q.length → p.vertex a ≠ q.vertex j) :
    ∃ r : AltPath M, r.last = c ∧ r.Shortest ∧ r.length % 2 = 1 ∧
      r.length = p.length + q.length - i.val ∧
      tenacity M c = some (p.length + q.length) ∧
      ∀ b, p.BaseOnPath (p.length + q.length) b ↔ r.BaseOnPath (p.length + q.length) b := by
  let u := q.vertex ⟨q.length - 1, by omega⟩
  have hqeven : evenlevel M q.last = some p.length := by
    rw [hend]
    exact (level_eq_some_iff M 0 p.last p.length).2
      (by simpa only [Shortest, hpe] using hp)
  have hqodd : oddlevel M q.last = some q.length :=
    (level_eq_some_iff M 1 q.last q.length).2 (by simpa only [Shortest, hqo] using hq)
  have hqmin : minlevel M q.last = some q.length := by
    simp only [minlevel, hqeven, hqodd, levelMin]
    exact congrArg some (Nat.min_eq_right (by omega))
  let q₀ := q.take (q.length - 1) (by omega)
  have hq₀ : q₀.Shortest := q.minlevel_last_predecessor_honest hqmin (by omega)
  obtain ⟨k, hk, hke, hklt, _, hkshort⟩ :=
    blossom_on_shortest (p.length + q.length - 2) c u hc q₀ rfl hq₀
  have hki : k.val = i.val := by
    have h := q.injective ⟨k.val, by have := k.isLt; change k.val < q.length - 1 + 1 at this; omega⟩ i
      (hk.trans hci.symm)
    exact congrArg Fin.val h
  have hie : i.val % 2 = 0 := by omega
  have hilt : i.val < q.length - 1 := by
    change k.val < q.length - 1 at hklt
    omega
  have hce : evenlevel M c = some i.val := by
    have hshort : IsShortest M 0 c k.val := by
      simpa only [Shortest, take_length, take_last, hke, hk] using hkshort
    have hh := (level_eq_some_iff M 0 c k.val).2 hshort
    simpa only [hki] using hh
  have hcge : levelLE (some (p.length + q.length)) (tenacity M c) :=
    tenacity_ge_of_above_previous_odd c _ (by omega) hchigh
  have hfresh : ∀ a, p.vertex a ≠ u := by
    intro a
    exact hdis a ⟨q.length - 1, by omega⟩ (by change i.val ≤ q.length - 1; omega)
      (by change q.length - 1 < q.length; omega)
  have hadj : G.Adj p.last u := by
    rw [← hend]
    have he : q.length - 1 + 1 = q.length := by omega
    simpa only [he, last, u] using G.symm (q.adjacent ⟨q.length - 1, by omega⟩)
  let a := p.append u hfresh hadj (p.inner_predecessor_append_parity q hpe hqo hend)
  have hao : a.length % 2 = 1 := by change (p.length + 1) % 2 = 1; omega
  have hrev : a.ReverseDisjoint q i.val (q.length - 1) := by
    intro x y hiy hy hxy
    change (if h : x.val ≤ p.length then p.vertex ⟨x.val, _⟩ else u) = q.vertex y at hxy
    split at hxy
    · exact hdis ⟨x.val, by omega⟩ y hiy (by omega) hxy
    · have he := congrArg Fin.val (q.injective ⟨q.length - 1, by omega⟩ y hxy)
      change q.length - 1 = y.val at he
      omega
  let r := a.spliceReverse q i.val (q.length - 1) (by omega) (by omega)
    (append_last _ _ _ _ _) hao (by omega) hrev
  have hrlen : r.length = p.length + 1 + (q.length - 1 - i.val) := rfl
  have hrl : r.length = p.length + q.length - i.val := by omega
  have hro : r.length % 2 = 1 := by omega
  have hrc : r.last = c := (spliceReverse_last _ _ _ _ _ _ _ _ _ _).trans hci
  have hct : tenacity M c = some (p.length + q.length) := by
    have hlev : level M (i.val % 2) c = some i.val := by simpa only [hie] using hce
    exact (levels_of_opposite_bound c i.val (p.length + q.length) hlev (by omega) hcge
      ⟨r.length, ⟨r, hrc, rfl, by omega⟩, by omega⟩).1
  have hrcshort : r.Shortest := by
    have hco : oddlevel M c = some r.length := by
      have ht := hct
      unfold tenacity at ht
      rw [hce] at ht
      cases ho : oddlevel M c with
      | none => simp only [ho, levelAdd] at ht; contradiction
      | some o =>
        have he : i.val + o = p.length + q.length := by
          simpa only [ho, levelAdd, Option.some.injEq] using ht
        exact congrArg some (by omega)
    simpa only [Shortest, hro, hrc] using (level_eq_some_iff M 1 c r.length).1 hco
  have hlow : ∀ j : Fin (q.length + 1), i.val ≤ j.val → j.val < q.length →
      ¬levelLT (some (p.length + q.length)) (tenacity M (q.vertex j)) := by
    intro j hij hj
    by_cases heq : i.val = j.val
    · have hij' : i = j := Fin.ext heq
      rw [← hij', hci, hct]
      change ¬p.length + q.length < p.length + q.length
      omega
    · obtain ⟨s, hs, hst⟩ := blossom_suffix_tenacity_bound
        (p.length + q.length - 2) c u hc hchigh q₀ rfl hq₀ k
        ⟨j.val, by change j.val < q.length - 1 + 1; omega⟩ hk (by change k.val < j.val; omega)
      change tenacity M (q.vertex ⟨j.val, _⟩) = some s at hs
      rw [hs]
      change ¬p.length + q.length < s
      omega
  refine ⟨r, hrc, hrcshort, hro, hrl, hct, ?_⟩
  intro b
  apply p.baseOnPath_initial_iff r (by omega) ?_ _ ?_ b
  · intro j
    change p.vertex j = (if h : j.val ≤ a.length then a.vertex ⟨j.val, _⟩
      else q.vertex ⟨q.length - 1 - (j.val - a.length), _⟩)
    simp only [dite_eq_left (show j.val ≤ a.length by change j.val ≤ p.length + 1; omega)]
    change p.vertex j = (if h : j.val ≤ p.length then p.vertex ⟨j.val, _⟩ else u)
    simp only [dite_eq_left (show j.val ≤ p.length by omega)]
  · intro j hj
    change ¬levelLT (some (p.length + q.length))
      (tenacity M (if h : j.val ≤ a.length then a.vertex ⟨j.val, _⟩
        else q.vertex ⟨q.length - 1 - (j.val - a.length), _⟩))
    split
    · rename_i hja
      have heq : j.val = p.length + 1 := by change j.val ≤ p.length + 1 at hja; omega
      have hav : a.vertex ⟨j.val, by omega⟩ = u := by
        change (if h : j.val ≤ p.length then p.vertex ⟨j.val, _⟩ else u) = u
        simp only [dite_eq_right (by omega : ¬j.val ≤ p.length)]
      rw [hav]
      exact hlow ⟨q.length - 1, by omega⟩ (by change i.val ≤ q.length - 1; omega)
        (by change q.length - 1 < q.length; omega)
    · apply hlow
      · have hjbound := j.isLt
        change j.val < r.length + 1 at hjbound
        change i.val ≤ q.length - 1 - (j.val - (p.length + 1))
        omega
      · change q.length - 1 - (j.val - (p.length + 1)) < q.length
        omega


/-- A first-hit reverse splice may include the preceding boundary vertex when
that vertex is absent from the replacement path. -/
theorem FirstHit.reverse_disjoint_of_absent_boundary {p q : AltPath M} {k : Nat}
    (h : FirstHit q p (k + 1)) (hk : k ≤ p.length)
    (habsent : ∀ a, q.vertex a ≠ p.vertex ⟨k, by omega⟩) :
    (q.take h.qi.val (by omega)).ReverseDisjoint p k h.pi.val := by
  intro a b hkb hbj he
  by_cases hlt : k < b.val
  · exact h.reverse_disjoint (k + 1) (by omega) a b (by omega) hbj he
  · have hbe : b = ⟨k, by omega⟩ := Fin.ext (by change b.val = k; omega)
    rw [hbe] at he
    exact habsent ⟨a.val, by have := a.isLt; change a.val < h.qi.val + 1 at this; omega⟩ he

/-- If two opposite shortest paths have different threshold bases, the base
at the greater minimum level is absent from the other path. This uses only
limited honesty and the last-above-threshold definition. -/
theorem higher_base_absent (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1) (hend : q.last = p.last)
    (b c : V) (hpb : p.BaseOnPath (p.length + q.length) b)
    (hqc : q.BaseOnPath (p.length + q.length) c)
    (i : Fin (p.length + 1)) (hi : p.vertex i = b)
    (j : Fin (q.length + 1)) (hj : q.vertex j = c)
    (horder : j.val ≤ i.val) (hne : b ≠ c) : ∀ a, q.vertex a ≠ b := by
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hqten : tenacity M q.last = some (p.length + q.length) := by rw [hend]; exact hten
  have hbhigh := hpb.choose_spec.2.1
  have hpi := (p.limited_bfs_honesty hp i (by rw [hten, hi]; exact levelLT_le hbhigh)).2
    (by rw [hten, hi]; exact hbhigh)
  rw [hi] at hpi
  obtain ⟨j₀, hj₀, _, hlast⟩ := hqc
  have hj₀j : j₀ = j := q.injective _ _ (hj₀.trans hj.symm)
  subst j₀
  intro a hab
  have hqa := (q.limited_bfs_honesty hq a (by rw [hqten, hab]; exact levelLT_le hbhigh)).2
    (by rw [hqten, hab]; exact hbhigh)
  rw [hab] at hqa
  have hai : a.val = i.val := Option.some.inj (hqa.symm.trans hpi)
  by_cases hja : j.val < a.val
  · exact hlast a hja (by rw [hab]; exact hbhigh)
  · have haj : a = j := Fin.ext (by change a.val = j.val; omega)
    exact hne (hab.symm.trans ((congrArg q.vertex haj).trans hj))

/-- In a hypothetical disagreement of bases, the shorter-base prefix avoids
the entire suffix from the higher base onward on the opposite path. A first
hit would either shorten the even path or give the higher base tenacity at
most the endpoint's. This rules out all intersections with the shorter high
prefix in a subsequent suffix-only crossing argument. -/
theorem base_prefix_avoids_opposite_suffix (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1) (hend : q.last = p.last)
    (b c : V) (hpb : p.BaseOnPath (p.length + q.length) b)
    (hqc : q.BaseOnPath (p.length + q.length) c)
    (i : Fin (p.length + 1)) (hi : p.vertex i = b)
    (j : Fin (q.length + 1)) (hj : q.vertex j = c)
    (horder : j.val ≤ i.val) (hne : b ≠ c) :
    ∀ (a : Fin (q.length + 1)) (d : Fin (p.length + 1)),
      a.val ≤ j.val → i.val ≤ d.val → q.vertex a ≠ p.vertex d := by
  have habsent := p.higher_base_absent q hp hq hpe hqo hend b c hpb hqc i hi j hj horder hne
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  obtain ⟨i₀, hi₀, hie₀⟩ := p.baseOnPath_even _ hten hpb
  have hi₀i : i₀ = i := p.injective _ _ (hi₀.trans hi.symm)
  have hie : i.val % 2 = 0 := by simpa only [hi₀i] using hie₀
  have hbhigh := hpb.choose_spec.2.1
  intro a d haj hid had
  by_cases hdi : d.val = i.val
  · have hdi' : d = i := Fin.ext hdi
    exact habsent a (had.trans ((congrArg p.vertex hdi').trans hi))
  · let r₀ := q.take j.val (by omega)
    obtain ⟨h⟩ := firstHit_exists r₀ p (i.val + 1)
      ⟨⟨a.val, by change a.val < j.val + 1; omega⟩, d, by omega, had⟩
    have hodd := h.odd hpe (by omega)
    by_cases he : h.pi.val % 2 = 0
    · have hki : i.val ≤ h.pi.val := by have := h.in_suffix; omega
      have havoidr : ∀ x, r₀.vertex x ≠ p.vertex ⟨i.val, by omega⟩ := by
        intro x heq
        exact habsent ⟨x.val, by have := x.isLt; change x.val < j.val + 1 at this; omega⟩ (heq.trans hi)
      let r := (r₀.take h.qi.val (by omega)).spliceReverse p i.val h.pi.val hki
        (by omega) h.hit hodd he (h.reverse_disjoint_of_absent_boundary (by omega) havoidr)
      have hrlen : r.length = h.qi.val + (h.pi.val - i.val) := rfl
      have hrb : r.last = b := (spliceReverse_last _ _ _ _ _ _ _ _ _ _).trans hi
      have hwe : HasPathLength M (i.val % 2) b i.val := by simpa only [hi] using p.prefix_witness i
      have hwo : HasPathLength M ((i.val + 1) % 2) b r.length :=
        ⟨r, hrb, rfl, by rw [hrlen]; omega⟩
      obtain ⟨s, hs, hsbound⟩ := tenacity_bound_of_opposite_witnesses b i.val r.length hwe hwo
      have hgt : p.length + q.length < s := by simpa only [hs, levelLT] using hbhigh
      have hqbound := h.qi.isLt
      change h.qi.val < j.val + 1 at hqbound
      have hpbound := h.pi.isLt
      omega
    · have hpo : h.pi.val % 2 = 1 := by omega
      have hbound := p.no_shorter_disjoint_prefix hp h.pi.val (by omega)
        (r₀.take h.qi.val (by omega)) h.hit
        (by simp only [take_length]; omega) h.forward_disjoint
      change h.pi.val ≤ h.qi.val at hbound
      have hqbound := h.qi.isLt
      change h.qi.val < j.val + 1 at hqbound
      have hsuffix := h.in_suffix
      omega


/-- In the remaining crossing case with an absent lower-blossom boundary,
the first hit of the even path on the boundary suffix is odd on both paths
and strictly later on the even path. Opposite parity would lower the boundary's
tenacity; equal indices would produce a shortest path to the predecessor that
omits its established blossom boundary. -/
theorem first_lower_boundary_hit_strict (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (c : V) (hc : Blossom M (p.length + q.length - 2) c
      (q.vertex ⟨q.length - 1, by omega⟩))
    (hchigh : levelLT (some (p.length + q.length - 2)) (tenacity M c))
    (i : Fin (q.length + 1)) (hci : q.vertex i = c)
    (habsent : ∀ a, p.vertex a ≠ c)
    (h : FirstHit p (q.take (q.length - 1) (by omega)) (i.val + 1)) :
    h.qi.val % 2 = 1 ∧ h.pi.val % 2 = 1 ∧ h.pi.val < h.qi.val := by
  let u := q.vertex ⟨q.length - 1, by omega⟩
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
  obtain ⟨k, hk, hke, hklt, _, _⟩ :=
    blossom_on_shortest (p.length + q.length - 2) c u hc q₀ rfl hq₀
  have hki : k.val = i.val := by
    have he := q.injective ⟨k.val, by have := k.isLt; change k.val < q.length - 1 + 1 at this; omega⟩ i
      (hk.trans hci.symm)
    exact congrArg Fin.val he
  have hie : i.val % 2 = 0 := by omega
  have hilt : i.val < q.length - 1 := by
    change k.val < q.length - 1 at hklt
    omega
  have hq₀e : q₀.length % 2 = 0 := by change (q.length - 1) % 2 = 0; omega
  have hao : h.qi.val % 2 = 1 := h.odd hq₀e (by omega)
  have hcge : levelLE (some (p.length + q.length)) (tenacity M c) :=
    tenacity_ge_of_above_previous_odd c _ (by omega) hchigh
  have hq₀end : q₀.last = u := rfl
  have hpil : h.pi.val ≤ q₀.length := by have hh : h.pi.val < q₀.length + 1 := h.pi.isLt; omega
  have hbo : h.pi.val % 2 = 1 := by
    by_cases hb : h.pi.val % 2 = 1
    · exact hb
    · have hbe : h.pi.val % 2 = 0 := by omega
      have hkj : i.val ≤ h.pi.val := by have := h.in_suffix; omega
      have havoid : ∀ a, p.vertex a ≠ q₀.vertex ⟨i.val, by change i.val < q.length - 1 + 1; omega⟩ := by
        intro a he
        exact habsent a (he.trans hci)
      let r := (p.take h.qi.val (by omega)).spliceReverse q₀ i.val h.pi.val hkj
        hpil h.hit hao hbe
        (h.reverse_disjoint_of_absent_boundary (by change i.val ≤ q.length - 1; omega) havoid)
      have hrlen : r.length = h.qi.val + (h.pi.val - i.val) := rfl
      have hrc : r.last = c := (spliceReverse_last _ _ _ _ _ _ _ _ _ _).trans hci
      have hwe : HasPathLength M (i.val % 2) c i.val := by simpa only [hci] using q.prefix_witness i
      have hwo : HasPathLength M ((i.val + 1) % 2) c r.length :=
        ⟨r, hrc, rfl, by rw [hrlen]; omega⟩
      obtain ⟨s, hs, hsb⟩ := tenacity_bound_of_opposite_witnesses c i.val r.length hwe hwo
      have hst : p.length + q.length ≤ s := by simpa only [hs, levelLE] using hcge
      have ha := h.qi.isLt
      have hb := h.pi.isLt
      change h.pi.val < q.length - 1 + 1 at hb
      omega
  have hpar : (p.take h.qi.val (by omega)).length % 2 = h.pi.val % 2 := by
    simp only [take_length, hao, hbo]
  let r := (p.take h.qi.val (by omega)).splice q₀ h.pi.val hpil
    h.hit hpar h.forward_disjoint
  have hrlen : r.length = h.qi.val + (q₀.length - h.pi.val) := rfl
  have hrend : r.last = u := splice_last _ _ _ _ _ _ _
  have hrpar : r.length % 2 = q₀.length % 2 := splice_parity _ _ _ _ _ _ _
  have hbound := hq₀.2 r.length ⟨r, hrend, rfl, hrpar⟩
  have hba : h.pi.val ≤ h.qi.val := by have := h.pi.isLt; omega
  have hne : h.pi.val ≠ h.qi.val := by
    intro heq
    have hrl : r.length = q₀.length := by have := h.pi.isLt; omega
    have hrs : r.Shortest := by
      simpa only [Shortest, hrend, hrl, hq₀end] using hq₀
    obtain ⟨j, hj, _, _, _, _⟩ :=
      blossom_on_shortest (p.length + q.length - 2) c u hc r hrend hrs
    change (if ha : j.val ≤ (p.take h.qi.val (by omega)).length then
      (p.take h.qi.val (by omega)).vertex ⟨j.val, _⟩
      else q₀.vertex ⟨j.val - (p.take h.qi.val (by omega)).length + h.pi.val, _⟩) = c at hj
    split at hj
    · rename_i hle
      change j.val ≤ h.qi.val at hle
      exact habsent ⟨j.val, by have := h.qi.isLt; omega⟩ hj
    · have hid := congrArg Fin.val (q.injective _ i (hj.trans hci.symm))
      have hin := h.in_suffix
      change j.val - h.qi.val + h.pi.val = i.val at hid
      omega
  exact ⟨hao, hbo, by omega⟩

/-- A first hit on the suffix after a high even vertex cannot occur earlier on
its replacement prefix. An opposite-parity hit would give the high vertex
finite tenacity below the sum of the two path lengths. -/
theorem first_high_suffix_hit_le (p q : AltPath M) (hp : p.Shortest)
    (hpe : p.length % 2 = 0) (hqpos : 0 < q.length)
    (i : Fin (p.length + 1)) (hie : i.val % 2 = 0)
    (hhigh : levelLT (some (p.length + q.length)) (tenacity M (p.vertex i)))
    (habsent : ∀ a, q.vertex a ≠ p.vertex i)
    (h : FirstHit (q.take (q.length - 1) (by omega)) p (i.val + 1)) :
    h.pi.val ≤ h.qi.val := by
  let q₀ := q.take (q.length - 1) (by omega)
  have hodd := h.odd hpe (by omega)
  have hqi : h.qi.val ≤ q₀.length := by
    have hh := h.qi.isLt
    change h.qi.val < q.length - 1 + 1 at hh
    change h.qi.val ≤ q.length - 1
    omega
  by_cases he : h.pi.val % 2 = 0
  · have hki : i.val ≤ h.pi.val := by have := h.in_suffix; omega
    have havoidr : ∀ x, q₀.vertex x ≠ p.vertex ⟨i.val, by omega⟩ := by
      intro x heq
      exact habsent ⟨x.val, by have := x.isLt; change x.val < q.length - 1 + 1 at this; omega⟩ heq
    let r := (q₀.take h.qi.val (by omega)).spliceReverse p i.val h.pi.val hki
      (by omega) h.hit hodd he (h.reverse_disjoint_of_absent_boundary (by omega) havoidr)
    have hrlen : r.length = h.qi.val + (h.pi.val - i.val) := rfl
    have hrb : r.last = p.vertex i := spliceReverse_last _ _ _ _ _ _ _ _ _ _
    have hwe := p.prefix_witness i
    have hwo : HasPathLength M ((i.val + 1) % 2) (p.vertex i) r.length :=
      ⟨r, hrb, rfl, by rw [hrlen]; omega⟩
    obtain ⟨s, hs, hsbound⟩ := tenacity_bound_of_opposite_witnesses
      (p.vertex i) i.val r.length hwe hwo
    have hgt : p.length + q.length < s := by simpa only [hs, levelLT] using hhigh
    have hqbound := h.qi.isLt
    change h.qi.val < q.length - 1 + 1 at hqbound
    have hpbound := h.pi.isLt
    omega
  · have hpo : h.pi.val % 2 = 1 := by omega
    exact p.no_shorter_disjoint_prefix hp h.pi.val (by omega)
      (q₀.take h.qi.val (by omega)) h.hit
      (by simp only [take_length]; omega) h.forward_disjoint

/-- Opposite first-hit minimalities rule out every lower-boundary crossing
once the early part of the even path avoids that lower blossom. The required
index ordering places the lower boundary no later than the high even vertex. -/
theorem lower_boundary_disjoint_of_early_avoidance (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (c : V) (hc : Blossom M (p.length + q.length - 2) c
      (q.vertex ⟨q.length - 1, by omega⟩))
    (hchigh : levelLT (some (p.length + q.length - 2)) (tenacity M c))
    (i : Fin (q.length + 1)) (hci : q.vertex i = c)
    (habsent : ∀ a, p.vertex a ≠ c)
    (B : Fin (p.length + 1)) (hBe : B.val % 2 = 0)
    (hBhigh : levelLT (some (p.length + q.length)) (tenacity M (p.vertex B)))
    (hBabsent : ∀ a, q.vertex a ≠ p.vertex B) (hiB : i.val ≤ B.val)
    (hearly : ∀ (a : Fin (p.length + 1)) (j : Fin (q.length + 1)),
      a.val ≤ B.val → i.val < j.val → j.val < q.length → p.vertex a ≠ q.vertex j) :
    ∀ (a : Fin (p.length + 1)) (j : Fin (q.length + 1)),
      i.val ≤ j.val → j.val < q.length → p.vertex a ≠ q.vertex j := by
  intro a j hij hj heq
  by_cases he : i.val = j.val
  · have he' : i = j := Fin.ext he
    exact habsent a (heq.trans ((congrArg q.vertex he').symm.trans hci))
  · let q₀ := q.take (q.length - 1) (by omega)
    obtain ⟨h⟩ := firstHit_exists p q₀ (i.val + 1)
      ⟨a, ⟨j.val, by change j.val < q.length - 1 + 1; omega⟩, by change i.val + 1 ≤ j.val; omega, heq⟩
    have hs := p.first_lower_boundary_hit_strict q hp hq hpe hqo hend hinner
      c hc hchigh i hci habsent h
    have hbefore : B.val < h.qi.val := by
      apply Nat.lt_of_not_ge
      intro hle
      exact hearly h.qi ⟨h.pi.val, by have := h.pi.isLt; change h.pi.val < q.length - 1 + 1 at this; omega⟩
        hle (by change i.val < h.pi.val; have := h.in_suffix; omega)
        (by change h.pi.val < q.length; have := h.pi.isLt; change h.pi.val < q.length - 1 + 1 at this; omega) h.hit
    obtain ⟨g⟩ := firstHit_exists q₀ p (B.val + 1)
      ⟨h.pi, h.qi, by omega, h.hit.symm⟩
    have hgle := p.first_high_suffix_hit_le q hp hpe (by omega) B hBe hBhigh hBabsent g
    have hgafter : i.val < g.qi.val := by have := g.in_suffix; omega
    have hpg : h.qi.val ≤ g.pi.val := by
      apply Nat.le_of_not_lt
      intro hlt
      exact h.first g.pi g.qi hlt (by omega) g.hit.symm
    have hgq : g.qi.val ≤ h.pi.val := by
      apply Nat.le_of_not_lt
      intro hlt
      exact g.first h.pi h.qi hlt (by omega) h.hit.symm
    omega

/-- Every strict suffix vertex after a lower blossom boundary on a shortest
path belongs to that blossom under the lower confinement induction hypothesis. -/
theorem blossom_suffix_mem (p : AltPath M) (t : Nat) (c v : V)
    (hc : Blossom M t c v) (hchigh : levelLT (some t) (tenacity M c))
    (hconf : ∀ (b v : V), Blossom M t b v → levelLT (some t) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M t b w)
    (hpv : p.last = v) (hp : p.Shortest)
    (i j : Fin (p.length + 1)) (hi : p.vertex i = c) (hij : i.val < j.val) :
    Blossom M t c (p.vertex j) := by
  obtain ⟨k, hke, hk, _, hrelative⟩ := blossom_shortest_relative t c v hc hchigh p hpv hp
  have hki : k = i := p.injective k i (hk.trans hi.symm)
  subst k
  let r := p.segment i.val (by omega) hke
  have hw := hconf c v hc hchigh r hrelative hi
    ((p.segment_last _ _ _).trans hpv) (p.vertex j)
    ⟨⟨j.val - i.val, by change j.val - i.val < p.length - i.val + 1; omega⟩, by
      change p.vertex ⟨i.val + (j.val - i.val), _⟩ = p.vertex j
      congr 1
      apply Fin.ext
      change i.val + (j.val - i.val) = j.val
      omega⟩
  rcases hw with hw | hw
  · have he := congrArg Fin.val (p.injective j i (hw.trans hi.symm))
    omega
  · exact hw

/-- Lower-tenacity base existence and confinement suffice to rule out all
crossings of an absent lower boundary segment when that boundary's minimum
level is at most the minimum level of a high vertex on the opposite path. -/
theorem absent_lower_boundary_disjoint (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (ht : EligibleTenacity M (p.length + q.length))
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ p.length + q.length - 2 →
      ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (p.length + q.length - 2) b v →
      levelLT (some (p.length + q.length - 2)) (tenacity M b) →
      ∀ r : AltSegment M, r.Shortest → r.first = b → r.last = v →
        ∀ w, r.Contains w → w = b ∨ Blossom M (p.length + q.length - 2) b w)
    (c : V) (hc : Blossom M (p.length + q.length - 2) c
      (q.vertex ⟨q.length - 1, by omega⟩))
    (hchigh : levelLT (some (p.length + q.length - 2)) (tenacity M c))
    (i : Fin (q.length + 1)) (hci : q.vertex i = c)
    (habsent : ∀ a, p.vertex a ≠ c)
    (B : Fin (p.length + 1)) (hBe : B.val % 2 = 0)
    (hBhigh : levelLT (some (p.length + q.length)) (tenacity M (p.vertex B)))
    (hBabsent : ∀ a, q.vertex a ≠ p.vertex B) (hiB : i.val ≤ B.val) :
    ∀ (a : Fin (p.length + 1)) (j : Fin (q.length + 1)),
      i.val ≤ j.val → j.val < q.length → p.vertex a ≠ q.vertex j := by
  have htodd : (p.length + q.length - 2) % 2 = 1 := by omega
  have hroot : levelLT (some (p.length + q.length - 2)) (tenacity M p.first) :=
    free_tenacity_above M _ p.first p.start_free (fun r hr => by have := ht.2.2 r hr; omega)
  have hBlo : levelLT (some (p.length + q.length - 2)) (tenacity M (p.vertex B)) := by
    cases hb : tenacity M (p.vertex B) with
    | none => trivial
    | some s =>
      have hs : p.length + q.length < s := by simpa only [hb, levelLT] using hBhigh
      change p.length + q.length - 2 < s
      omega
  have hBhalf : 2 * B.val < p.length + q.length := by
    by_cases hhalf : p.length + q.length < 2 * B.val
    · have he := p.high_tenacity_above_half q hp hq hpe hqo hend hinner B
        (levelLT_le hBhigh) hhalf
      rw [he] at hBhigh
      change p.length + q.length < p.length + q.length at hBhigh
      omega
    · omega
  have hhon : ∀ j : Fin (p.length + 1), j.val ≤ B.val →
      levelLT (some (p.length + q.length - 2)) (tenacity M (p.vertex j)) →
      minlevel M (p.vertex j) = some j.val := by
    intro j hj hjhigh
    have htri := p.high_minlevel_triangle q hp hq hpe hqo hend hinner j
      (tenacity_ge_of_above_previous_odd (p.vertex j) _ (by omega) hjhigh)
    simpa only [Nat.min_eq_left (by omega : j.val ≤ p.length + q.length - j.val)] using htri
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
  obtain ⟨k, hk, _, hklt, _, _⟩ :=
    blossom_on_shortest (p.length + q.length - 2) c q₀.last hc q₀ rfl hq₀
  have hki : k.val = i.val := congrArg Fin.val
    (q.injective ⟨k.val, by have := k.isLt; change k.val < q.length - 1 + 1 at this; omega⟩ i
      (hk.trans hci.symm))
  apply p.lower_boundary_disjoint_of_early_avoidance q hp hq hpe hqo hend hinner
    c hc hchigh i hci habsent B hBe hBhigh hBabsent hiB
  intro a j ha hij hj heq
  have hmem := q₀.blossom_suffix_mem (p.length + q.length - 2) c q₀.last
    hc hchigh hconf rfl hq₀ k ⟨j.val, by change j.val < q.length - 1 + 1; omega⟩ hk
    (by change k.val < j.val; omega)
  change Blossom M (p.length + q.length - 2) c (q.vertex j) at hmem
  rw [← heq] at hmem
  have halt : a.val < B.val := by
    by_cases he : a.val = B.val
    · have he' : a = B := Fin.ext he
      exact False.elim (hBabsent j (heq.symm.trans (congrArg p.vertex he')))
    · omega
  obtain ⟨l, _, hl⟩ := p.blossom_member_before_high_forces_boundary
    (p.length + q.length - 2) htodd hexists hconf a B halt hroot hBlo hhon c hchigh hmem
  exact habsent l hl


end AltPath
end MaximumMatching

end GeneralBaseReroute

section GeneralPredecessorBlossom

/-! Promote the low predecessor to the blossom of the odd path's actual
threshold base. Current-tenacity base uniqueness is invoked only at a strictly
smaller minlevel, at the already located lower-blossom boundary. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

theorem predecessor_blossom_promote (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (ih : ∀ (v : V) (k : Nat), minlevel M v = some k → k < q.length →
      tenacity M v = some (p.length + q.length) → HasUniqueBase M v (p.length + q.length))
    (c : V) (hc : Blossom M (p.length + q.length - 2) c
      (q.vertex ⟨q.length - 1, by omega⟩))
    (hchigh : levelLT (some (p.length + q.length - 2)) (tenacity M c))
    (d : V) (hqd : q.BaseOnPath (p.length + q.length) d) :
    Blossom M (p.length + q.length) d (q.vertex ⟨q.length - 1, by omega⟩) := by
  classical
  obtain ⟨r, hrc, hr, _, hmin, hlt, hpres⟩ :=
    p.predecessor_blossom_prefix q hp hq hpe hqo hend hinner c hc
  have hrd := (hpres d).1 hqd
  have htodd : (p.length + q.length) % 2 = 1 := by omega
  by_cases hct : tenacity M c = some (p.length + q.length)
  · obtain ⟨a, ha, _⟩ := ih c r.length hmin hlt hct
    have hda : d = a := r.baseOnPath_unique _ d a hrd (ha r hrc hr)
    have hbase : IsBase M c d := ⟨p.length + q.length, hct, hda ▸ ha⟩
    have hmem : Blossom M (p.length + q.length) d c :=
      blossom_of_base_le _ htodd d c hbase (by rw [hct]; exact Nat.le_refl _)
    exact (blossom_strict_nested_of_base_mem (p.length + q.length - 2)
      (p.length + q.length) htodd c d hchigh hmem).1 _ hc
  · have hhigh : levelLT (some (p.length + q.length)) (tenacity M c) := by
      have hge := tenacity_ge_of_above_previous_odd c (p.length + q.length) htodd hchigh
      cases hs : tenacity M c with
      | none => trivial
      | some s =>
        have hts : p.length + q.length ≤ s := by simpa only [hs, levelLE] using hge
        have hne : s ≠ p.length + q.length := by intro h; exact hct (hs.trans (congrArg some h))
        change p.length + q.length < s
        omega
    have hrcbase : r.BaseOnPath (p.length + q.length) c := by
      refine ⟨⟨r.length, by omega⟩, hrc, hhigh, ?_⟩
      intro j hj
      change r.length < j.val at hj
      have := j.isLt
      omega
    have hdc := r.baseOnPath_unique _ d c hrd hrcbase
    rw [hdc]
    exact blossom_mono _ _ htodd (by omega) c _ hc

/-- The lower-predecessor branch supplies an actual current-threshold blossom
member for the short-path minimization argument. No current confinement or
global current-tenacity base existence is assumed. -/
theorem low_predecessor_in_base_blossom (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ p.length + q.length - 2 →
      ∃ b, IsBase M v b)
    (ih : ∀ (v : V) (k : Nat), minlevel M v = some k → k < q.length →
      tenacity M v = some (p.length + q.length) → HasUniqueBase M v (p.length + q.length))
    (s : Nat) (hs : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) = some s)
    (hst : s < p.length + q.length) (d : V) (hqd : q.BaseOnPath (p.length + q.length) d) :
    Blossom M (p.length + q.length) d (q.vertex ⟨q.length - 1, by omega⟩) := by
  have hsodd := tenacity_odd M _ s hs
  obtain ⟨c, hc, hmem⟩ := blossom_cover_of_base_existence (p.length + q.length - 2)
    (by omega) hexists _ s hs (by omega)
  exact p.predecessor_blossom_promote q hp hq hpe hqo hend hinner ih c hmem hc d hqd

end MaximumMatching.AltPath

end GeneralPredecessorBlossom

section GeneralStructureFirstHit

/-! First-hit bounds and avoidance for shortest witnesses to members of an
established lower blossom. These facts require actual blossom membership;
no general confinement hypothesis is used. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A first hit of any sufficiently short alternating path on the suffix after
an absent high even vertex has its old-path index at most its new-path
index. An opposite-parity hit would violate the high vertex's tenacity. -/
theorem first_high_suffix_hit_le_of_length_le (p r : AltPath M) (hp : p.Shortest)
    (hpe : p.length % 2 = 0) (i : Fin (p.length + 1)) (hie : i.val % 2 = 0)
    (t : Nat) (hbound : p.length + r.length ≤ t)
    (hhigh : levelLT (some t) (tenacity M (p.vertex i)))
    (habsent : ∀ a, r.vertex a ≠ p.vertex i)
    (h : FirstHit r p (i.val + 1)) :
    h.qi.val % 2 = 1 ∧ h.pi.val % 2 = 1 ∧ h.pi.val ≤ h.qi.val := by
  have hodd := h.odd hpe (by omega)
  by_cases he : h.pi.val % 2 = 0
  · have hki : i.val ≤ h.pi.val := by have := h.in_suffix; omega
    let s := (r.take h.qi.val (by omega)).spliceReverse p i.val h.pi.val hki
      (by omega) h.hit hodd he (h.reverse_disjoint_of_absent_boundary (by omega) habsent)
    have hslen : s.length = h.qi.val + (h.pi.val - i.val) := rfl
    have hsb : s.last = p.vertex i := spliceReverse_last _ _ _ _ _ _ _ _ _ _
    have hwe := p.prefix_witness i
    have hwo : HasPathLength M ((i.val + 1) % 2) (p.vertex i) s.length :=
      ⟨s, hsb, rfl, by rw [hslen]; omega⟩
    obtain ⟨k, hk, hkbound⟩ := tenacity_bound_of_opposite_witnesses
      (p.vertex i) i.val s.length hwe hwo
    have hgt : t < k := by simpa only [hk, levelLT] using hhigh
    have hrbound := h.qi.isLt
    have hpbound := h.pi.isLt
    omega
  · have hpo : h.pi.val % 2 = 1 := by omega
    refine ⟨hodd, hpo, ?_⟩
    exact p.no_shorter_disjoint_prefix hp h.pi.val (by omega)
      (r.take h.qi.val (by omega)) h.hit
      (by simp only [take_length]; omega) h.forward_disjoint

/-- A shortest path to a member of a lower blossom avoids any distinct high
vertex whose minimum level is at least the boundary's minimum level. A high
vertex on the path would have to occur both before the boundary and at its
honest minimum-level index. -/
theorem high_vertex_absent_of_lower_blossom (t : Nat) (c b : V) (C B : Nat)
    (hcmin : minlevel M c = some C) (hbmin : minlevel M b = some B)
    (horder : C ≤ B) (hne : c ≠ b)
    (hchigh : levelLT (some t) (tenacity M c))
    (hbhigh : levelLT (some t) (tenacity M b))
    (r : AltPath M) (hr : r.Shortest) (hrbl : Blossom M t c r.last) :
    ∀ a, r.vertex a ≠ b := by
  obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound t c r.last hrbl
  obtain ⟨k, hk, _, _, hkmin, _⟩ := blossom_on_shortest t c r.last hrbl r rfl hr
  have hkC : k.val = C := Option.some.inj (hkmin.symm.trans hcmin)
  obtain ⟨j, hj, _, hjlast⟩ := blossom_baseOnPath t c r.last hrbl hchigh r rfl hr
  have hjk : j = k := r.injective j k (hj.trans hk.symm)
  subst j
  intro a ha
  have hgreater : levelLT (tenacity M r.last) (tenacity M (r.vertex a)) := by
    rw [hs, ha]
    cases hb : tenacity M b with
    | none => trivial
    | some z =>
      have hz : t < z := by simpa only [hb, levelLT] using hbhigh
      change s < z
      omega
  have hamin := (r.limited_bfs_honesty hr a (levelLT_le hgreater)).2 hgreater
  rw [ha] at hamin
  have haB : a.val = B := Option.some.inj (hamin.symm.trans hbmin)
  by_cases hka : k.val < a.val
  · exact hjlast a hka (ha.symm ▸ hbhigh)
  · have hak : a = k := Fin.ext (by change a.val = k.val; omega)
    exact hne (hk.symm.trans ((congrArg r.vertex hak).symm.trans ha))

end MaximumMatching.AltPath

end GeneralStructureFirstHit

section GeneralBlossomEdgeClosure

/-! An unmatched edge with small even-level sum cannot cross two distinct
established blossoms. The proof uses actual shortest paths, confinement, and
two opposite boundary-index inequalities. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

namespace AltPath
private theorem blossom_edge_boundary_lt (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqe : q.length % 2 = 0)
    (t : Nat) (b c : V) (hpb : Blossom M t b p.last) (hqc : Blossom M t c q.last)
    (hbhigh : levelLT (some t) (tenacity M b)) (hchigh : levelLT (some t) (tenacity M c))
    (hne : b ≠ c)
    (hconf : ∀ (a v : V), Blossom M t a v → levelLT (some t) (tenacity M a) →
      ∀ r : AltSegment M, r.Shortest → r.first = a → r.last = v →
        ∀ w, r.Contains w → w = a ∨ Blossom M t a w)
    (hadj : G.Adj p.last q.last) (hunmatched : M.mate p.last ≠ some q.last)
    (hbudget : p.length + q.length + 1 ≤ t)
    (B : Fin (p.length + 1)) (hB : p.vertex B = b)
    (C : Fin (q.length + 1)) (hC : q.vertex C = c) : C.val < B.val := by
  classical
  obtain ⟨C₀, hC₀, hCe₀, hClt₀, hCmin₀, _⟩ := blossom_on_shortest t c q.last hqc q rfl hq
  have hCC : C₀ = C := q.injective _ _ (hC₀.trans hC.symm)
  subst C₀
  have hpbase := blossom_baseOnPath t b p.last hpb hbhigh p rfl hp
  obtain ⟨B₀, hB₀, _, hBlast⟩ := hpbase
  have hBB : B₀ = B := p.injective _ _ (hB₀.trans hB.symm)
  subst B₀
  by_cases hon : ∃ a, p.vertex a = c
  · obtain ⟨a, ha⟩ := hon
    obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound t b p.last hpb
    have hstrict : levelLT (tenacity M p.last) (tenacity M (p.vertex a)) := by
      rw [hs, ha]
      cases hc : tenacity M c with
      | none => trivial
      | some k =>
        have htk : t < k := by simpa only [hc, levelLT] using hchigh
        change s < k
        omega
    have hamin := (p.limited_bfs_honesty hp a (levelLT_le hstrict)).2 hstrict
    rw [ha] at hamin
    have haC : a.val = C.val := Option.some.inj (hamin.symm.trans hCmin₀)
    have hBa : ¬B.val < a.val := by
      intro hlt
      exact hBlast a hlt (by rw [ha]; exact hchigh)
    have hneidx : a.val ≠ B.val := by
      intro he
      have he' : a = B := Fin.ext he
      exact hne (hB.symm.trans ((congrArg p.vertex he').symm.trans ha))
    omega
  · have habsent : ∀ a, p.vertex a ≠ c := by intro a ha; exact hon ⟨a, ha⟩
    by_cases hinter : ∃ (a : Fin (p.length + 1)) (j : Fin (q.length + 1)),
        C.val + 1 ≤ j.val ∧ p.vertex a = q.vertex j
    · obtain ⟨h⟩ := firstHit_exists p q (C.val + 1) hinter
      have hhigh : levelLT (some t) (tenacity M (q.vertex C)) := by rw [hC]; exact hchigh
      have hhit := q.first_high_suffix_hit_le_of_length_le p hq hqe C hCe₀ t
        (by omega) hhigh (by intro a; rw [hC]; exact habsent a) h
      have hwc := q.blossom_suffix_mem t c q.last hqc hchigh hconf rfl hq C h.pi hC
        (by have := h.in_suffix; omega)
      have hIB : h.qi.val < B.val := by
        by_cases he : h.qi.val = B.val
        · have he' : h.qi = B := Fin.ext he
          have hw : q.vertex h.pi = b := h.hit.symm.trans ((congrArg p.vertex he').trans hB)
          obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound t c (q.vertex h.pi) hwc
          rw [hw] at hs
          have hts : t < s := by simpa only [hs, levelLT] using hbhigh
          omega
        · by_cases hlt : B.val < h.qi.val
          · have hwb := p.blossom_suffix_mem t b p.last hpb hbhigh hconf rfl hp B h.qi hB hlt
            rw [h.hit] at hwb
            exact False.elim (blossoms_disjoint_same_tenacity t b c hbhigh hchigh hne
              (q.vertex h.pi) ⟨hwb, hwc⟩)
          · omega
      have := h.in_suffix
      omega
    · have havoid : ∀ (a : Fin (p.length + 1)) (j : Fin (q.length + 1)),
          C.val ≤ j.val → p.vertex a ≠ q.vertex j := by
        intro a j hCj he
        by_cases hj : C.val < j.val
        · exact hinter ⟨a, j, by omega, he⟩
        · have he' : j = C := Fin.ext (by omega)
          exact habsent a (he.trans ((congrArg q.vertex he').trans hC))
      have hfresh : ∀ a, p.vertex a ≠ q.last := by
        intro a ha
        exact havoid a ⟨q.length, by omega⟩ (by change C.val ≤ q.length; omega) ha
      have hpar : (M.mate p.last = some q.last) ↔ p.length % 2 = 1 := by
        constructor
        · intro h; exact False.elim (hunmatched h)
        · intro h; omega
      let a := p.append q.last hfresh hadj hpar
      have hao : a.length % 2 = 1 := by change (p.length + 1) % 2 = 1; omega
      have hdis : a.ReverseDisjoint q C.val q.length := by
        intro i j hCj hj hhit
        change (if h : i.val ≤ p.length then p.vertex ⟨i.val, _⟩ else q.last) = q.vertex j at hhit
        split at hhit
        · exact havoid _ j hCj hhit
        · have he := congrArg Fin.val (q.injective ⟨q.length, by omega⟩ j hhit)
          change q.length = j.val at he
          omega
      let z := a.spliceReverse q C.val q.length (by omega) (Nat.le_refl _) (append_last _ _ _ _ _)
        hao hqe hdis
      have hzlen : z.length = p.length + 1 + (q.length - C.val) := rfl
      have hzlast : z.last = c := (spliceReverse_last _ _ _ _ _ _ _ _ _ _).trans hC
      have hw₀ : HasPathLength M (C.val % 2) c C.val := by simpa only [hC] using q.prefix_witness C
      have hw₁ : HasPathLength M ((C.val + 1) % 2) c z.length :=
        ⟨z, hzlast, rfl, by rw [hzlen]; omega⟩
      obtain ⟨s, hs, hsb⟩ := tenacity_bound_of_opposite_witnesses c C.val z.length hw₀ hw₁
      have hts : t < s := by simpa only [hs, levelLT] using hchigh
      omega

end AltPath

/-- Unmatched edges whose even-level sum is at most the cutoff have both
endpoints in the same established blossom, assuming confinement at that cutoff. -/
theorem blossom_unmatched_edge_boundary_eq (t : Nat) (b c u v : V)
    (hu : Blossom M t b u) (hv : Blossom M t c v)
    (hb : levelLT (some t) (tenacity M b)) (hc : levelLT (some t) (tenacity M c))
    (hconf : ∀ (a w : V), Blossom M t a w → levelLT (some t) (tenacity M a) →
      ∀ r : AltSegment M, r.Shortest → r.first = a → r.last = w →
        ∀ x, r.Contains x → x = a ∨ Blossom M t a x)
    (hadj : G.Adj u v) (hunmatched : M.mate u ≠ some v)
    (e f : Nat) (he : evenlevel M u = some e) (hf : evenlevel M v = some f)
    (hbudget : e + f + 1 ≤ t) : b = c := by
  apply Classical.byContradiction
  intro hne
  obtain ⟨p, hpv, hplen, hpe⟩ := ((level_eq_some_iff M 0 u e).1 he).1
  obtain ⟨q, hqv, hqlen, hqe⟩ := ((level_eq_some_iff M 0 v f).1 hf).1
  have hp : p.Shortest := by simpa only [AltPath.Shortest, hplen, hpe, hpv] using (level_eq_some_iff M 0 u e).1 he
  have hq : q.Shortest := by simpa only [AltPath.Shortest, hqlen, hqe, hqv] using (level_eq_some_iff M 0 v f).1 hf
  have hppar : p.length % 2 = 0 := by omega
  have hqpar : q.length % 2 = 0 := by omega
  have hup : Blossom M t b p.last := by rw [hpv]; exact hu
  have hvq : Blossom M t c q.last := by rw [hqv]; exact hv
  obtain ⟨B, hB, _, _, _, _⟩ := blossom_on_shortest t b p.last hup p rfl hp
  obtain ⟨C, hC, _, _, _, _⟩ := blossom_on_shortest t c q.last hvq q rfl hq
  have hadjp : G.Adj p.last q.last := by rw [hpv, hqv]; exact hadj
  have hunmp : M.mate p.last ≠ some q.last := by rw [hpv, hqv]; exact hunmatched
  have hCB := p.blossom_edge_boundary_lt q hp hq hppar hqpar t b c hup hvq hb hc hne hconf
    hadjp hunmp (by omega) B hB C hC
  have hBC := q.blossom_edge_boundary_lt p hq hp hqpar hppar t c b hvq hup hc hb (fun he => hne he.symm) hconf
    (G.symm hadjp) (by intro hm; exact hunmp (M.symm hm)) (by omega) C hC B hB
  omega

end MaximumMatching

end GeneralBlossomEdgeClosure

section GeneralStructureDoubleReverse

namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Two reverse splices through a later suffix hit construct an opposite path
at an absent even boundary. The only shared final matched pair is handled
explicitly, so both reverse splices are simple paths. -/
theorem double_reverse_boundary_bound (p r : AltPath M)
    (hre : r.length % 2 = 0)
    (D : Fin (r.length + 1)) (hDe : D.val % 2 = 0)
    (I O : Nat) (hIp : I + 1 ≤ p.length) (hIo : I % 2 = 1)
    (hIN : r.length - 1 ≤ I) (hNO : r.length < O)
    (hjoin : p.vertex ⟨I, by omega⟩ = r.vertex ⟨r.length - 1, by omega⟩)
    (hlast : p.vertex ⟨I + 1, by omega⟩ = r.last)
    (havoid : ∀ (a : Fin (p.length + 1)) (j : Fin (r.length + 1)),
      D.val ≤ j.val → j.val < r.length - 1 → p.vertex a ≠ r.vertex j)
    (g : FirstHit r p (I + 2))
    (hK : g.qi.val < D.val) (hKo : g.qi.val % 2 = 1) (hHe : g.pi.val % 2 = 0) :
    ∃ t, tenacity M (r.vertex D) = some t ∧ t ≤ p.length + O := by
  have hH : I + 2 ≤ g.pi.val := g.in_suffix
  have hNpos : 0 < r.length := by have := D.isLt; omega
  let r₀ := r.take g.qi.val (by omega)
  have hdis₁ : r₀.ReverseDisjoint p (I + 1) g.pi.val := by
    intro a b hb hbH he
    by_cases hbe : b.val = I + 1
    · have hbi : b = ⟨I + 1, by omega⟩ := Fin.ext hbe
      rw [hbi, hlast] at he
      change r.vertex ⟨a.val, _⟩ = r.vertex ⟨r.length, by omega⟩ at he
      have hai := congrArg Fin.val (r.injective _ _ he)
      have ha := a.isLt
      change a.val < g.qi.val + 1 at ha
      change a.val = r.length at hai
      omega
    · exact g.reverse_disjoint (I + 2) (Nat.le_refl _) a b (by omega) hbH he
  let s := r₀.spliceReverse p (I + 1) g.pi.val (by omega) (by omega)
    g.hit hKo hHe hdis₁
  have hslen : s.length = g.qi.val + (g.pi.val - (I + 1)) := rfl
  have hsodd : s.length % 2 = 1 := by rw [hslen]; omega
  have hslast : s.last = r.last := (spliceReverse_last _ _ _ _ _ _ _ _ _ _).trans hlast
  have hdis₂ : s.ReverseDisjoint r D.val r.length := by
    intro a j hDj hjN he
    change (if h : a.val ≤ r₀.length then r₀.vertex ⟨a.val, by omega⟩
      else p.vertex ⟨g.pi.val - (a.val - r₀.length), by omega⟩) = r.vertex j at he
    split at he
    next ha =>
      change r.vertex ⟨a.val, _⟩ = r.vertex j at he
      have hai := congrArg Fin.val (r.injective _ _ he)
      change a.val = j.val at hai
      change a.val ≤ g.qi.val at ha
      omega
    next ha =>
      have ha' : g.qi.val < a.val := by change ¬a.val ≤ g.qi.val at ha; omega
      have habound := a.isLt
      change a.val < g.qi.val + (g.pi.val - (I + 1)) + 1 at habound
      have hindex : I + 1 ≤ g.pi.val - (a.val - r₀.length) := by
        change I + 1 ≤ g.pi.val - (a.val - g.qi.val)
        omega
      by_cases hjlt : j.val < r.length - 1
      · exact havoid _ j hDj hjlt he
      · have hjeq : j.val = r.length - 1 := by omega
        have hj : j = ⟨r.length - 1, by omega⟩ := Fin.ext hjeq
        rw [hj, ← hjoin] at he
        have hei := congrArg Fin.val (p.injective _ _ he)
        change g.pi.val - (a.val - r₀.length) = I at hei
        omega
  let z := s.spliceReverse r D.val r.length (by omega) (Nat.le_refl _) hslast hsodd hre hdis₂
  have hzlen : z.length = g.qi.val + (g.pi.val - (I + 1)) + (r.length - D.val) := rfl
  have hzlast : z.last = r.vertex D := spliceReverse_last _ _ _ _ _ _ _ _ _ _
  have hzo : z.length % 2 = 1 := by rw [hzlen]; omega
  have hwe : HasPathLength M (D.val % 2) (r.vertex D) D.val := r.prefix_witness D
  have hwo : HasPathLength M ((D.val + 1) % 2) (r.vertex D) z.length :=
    ⟨z, hzlast, rfl, by omega⟩
  obtain ⟨t, ht, hbound⟩ := tenacity_bound_of_opposite_witnesses (r.vertex D) D.val z.length hwe hwo
  refine ⟨t, ht, ?_⟩
  have hplength := g.pi.isLt
  have hDlength := D.isLt
  rw [hzlen] at hbound
  omega

/-- The first-hit and shortestness hypotheses supply the two parity guards
and the shared final matched mate for the double reverse construction. -/
theorem double_reverse_boundary_bound_of_firstHit (p r : AltPath M)
    (hp : p.Shortest) (hpe : p.length % 2 = 0) (hre : r.length % 2 = 0)
    (D : Fin (r.length + 1)) (hDe : D.val % 2 = 0)
    (I O : Nat) (hIp : I + 1 ≤ p.length) (hIo : I % 2 = 1)
    (hIN : r.length - 1 ≤ I) (hNO : r.length < O)
    (hjoin : p.vertex ⟨I, by omega⟩ = r.vertex ⟨r.length - 1, by omega⟩)
    (havoid : ∀ (a : Fin (p.length + 1)) (j : Fin (r.length + 1)),
      D.val ≤ j.val → j.val < r.length - 1 → p.vertex a ≠ r.vertex j)
    (g : FirstHit r p (I + 2)) (hK : g.qi.val < D.val) :
    ∃ t, tenacity M (r.vertex D) = some t ∧ t ≤ p.length + O := by
  have hKo : g.qi.val % 2 = 1 := g.odd hpe (by omega)
  have hHe : g.pi.val % 2 = 0 := by
    by_cases he : g.pi.val % 2 = 0
    · exact he
    · have hHo : g.pi.val % 2 = 1 := by omega
      have hbound := p.no_shorter_disjoint_prefix hp g.pi.val (by omega)
        (r.take g.qi.val (by omega)) g.hit
        (by simp only [take_length]; omega) g.forward_disjoint
      have hg := g.in_suffix
      have hD := D.isLt
      change g.pi.val ≤ g.qi.val at hbound
      omega
  have hNpos : 0 < r.length := by have := D.isLt; omega
  have hlast : p.vertex ⟨I + 1, by omega⟩ = r.last := by
    have hpnext := p.mate_next I (by omega) hIo
    have hrnext := r.mate_next (r.length - 1) (by omega) (by omega)
    rw [hjoin] at hpnext
    have hh := M.mate_unique hpnext hrnext
    simpa only [show r.length - 1 + 1 = r.length by omega, last] using hh
  exact p.double_reverse_boundary_bound r hre D hDe I O hIp hIo hIN hNO hjoin hlast
    havoid g hK hKo hHe

end MaximumMatching.AltPath

end GeneralStructureDoubleReverse
