import MaximumMatching.BlossomRelative
import MaximumMatching.MinCorrectness
import MaximumMatching.GeneralLowLocalization
import MaximumMatching.GeneralHighGeometry

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
