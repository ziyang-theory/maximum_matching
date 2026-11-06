import MaximumMatching.BaseRerouting
import MaximumMatching.BridgeBuckets
import MaximumMatching.GeneralBaseStructure
import MaximumMatching.GeneralEdgeGeometry
import MaximumMatching.MinScan

section GeneralBridgeAbsence

/-! Absence of a specified bridge tenacity on short or lower-tenacity shortest
paths, using only relative edge bounds at the preceding odd cutoff. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Excludes only bridges of the specified tenacity; lower bridges may remain. -/
def NoBridgeOfTenacity (p : AltPath M) (t : Nat) : Prop :=
  ∀ i : Fin p.length, Bridge M (p.vertex ⟨i.val, by omega⟩) (p.vertex ⟨i.val + 1, by omega⟩) →
    edgeTenacity M (p.vertex ⟨i.val, by omega⟩) (p.vertex ⟨i.val + 1, by omega⟩) ≠ some t

/-- An actual lower-blossom suffix cannot contain an edge of the current
threshold. The proof transfers an original edge into the shortest segment. -/
theorem lower_relative_edge_ne (p : AltPath M) (t : Nat)
    (hedge : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ i : Fin q.length, levelLE (edgeTenacity M (q.vertex ⟨i.val, by omega⟩)
          (q.vertex ⟨i.val + 1, by omega⟩)) (some (t - 2)))
    (b : V) (hmem : Blossom M (t - 2) b p.last)
    (hb : levelLT (some (t - 2)) (tenacity M b))
    (A : Fin (p.length + 1)) (hAe : A.val % 2 = 0) (hA : p.vertex A = b)
    (hseg : (p.segment A.val (by omega) hAe).Shortest)
    (htpos : 0 < t) (i : Fin p.length) (hAi : A.val ≤ i.val) :
    edgeTenacity M (p.vertex ⟨i.val, by omega⟩) (p.vertex ⟨i.val + 1, by omega⟩) ≠ some t := by
  let q := p.segment A.val (by omega) hAe
  have hbound := hedge b p.last hmem hb q hseg
    ((p.segment_first _ _ _).trans hA) (p.segment_last _ _ _)
    ⟨i.val - A.val, by change i.val - A.val < p.length - A.val; omega⟩
  have hleft : q.vertex ⟨i.val - A.val, by change i.val - A.val < p.length - A.val + 1; omega⟩ =
      p.vertex ⟨i.val, by omega⟩ := by
    change p.vertex ⟨A.val + (i.val - A.val), _⟩ = _
    congr 1
    apply Fin.ext
    change A.val + (i.val - A.val) = i.val
    omega
  have hright : q.vertex ⟨i.val - A.val + 1, by change i.val - A.val + 1 < p.length - A.val + 1; omega⟩ =
      p.vertex ⟨i.val + 1, by omega⟩ := by
    change p.vertex ⟨A.val + (i.val - A.val + 1), _⟩ = _
    congr 1
    apply Fin.ext
    change A.val + (i.val - A.val + 1) = i.val + 1
    omega
  rw [hleft, hright] at hbound
  intro he
  rw [he] at hbound
  change t ≤ t - 2 at hbound
  omega

/-- A shortest path shorter than half the threshold has no bridge of that
threshold. Low blossoms may occur anywhere on the path. -/
theorem short_shortest_no_bridge (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b)
    (hedge : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ i : Fin q.length, levelLE (edgeTenacity M (q.vertex ⟨i.val, by omega⟩)
          (q.vertex ⟨i.val + 1, by omega⟩)) (some (t - 2)))
    (p : AltPath M) (hp : p.Shortest) (hlen : 2 * p.length < t) : p.NoBridgeOfTenacity t := by
  have aux : ∀ L (p : AltPath M), p.length = L → p.Shortest → 2 * p.length < t →
      p.NoBridgeOfTenacity t := by
    intro L
    induction L using Nat.strongRecOn with
    | ind L ih =>
      intro p hpL hp hlen i hib hit
      have hpos : 0 < p.length := by have := i.isLt; omega
      have htlow : (t - 2) % 2 = 1 := by omega
      by_cases hhigh : levelLE (some t) (tenacity M p.last)
      · have hmin : minlevel M p.last = some p.length := minlevel_of_below_half p.last p.length t
          ((level_eq_some_iff M (p.length % 2) p.last p.length).2 hp) hlen hhigh
        have hpred := p.minlevel_last_predecessor_honest hmin hpos
        by_cases hi : i.val < p.length - 1
        · exact ih (p.length - 1) (by omega) (p.take (p.length - 1) (by omega)) rfl hpred
            (by change 2 * (p.length - 1) < t; omega) ⟨i.val, hi⟩ hib hit
        · have hieq : i.val = p.length - 1 := by have := i.isLt; omega
          have hv : p.vertex ⟨i.val + 1, by omega⟩ = p.last := by
            congr 1
            apply Fin.ext
            change i.val + 1 = p.length
            omega
          apply hib.2
          apply Or.inl
          refine ⟨p, hv.symm, ?_, hpos, ?_⟩
          · rw [hv]
            exact hmin
          · congr 1
            exact Fin.ext hieq.symm
      · have hlow : ∃ s, tenacity M p.last = some s ∧ s ≤ t - 2 := by
          cases hs : tenacity M p.last with
          | none => exact False.elim (hhigh (by rw [hs]; trivial))
          | some s =>
            have hsodd := tenacity_odd M p.last s hs
            have hn : ¬t ≤ s := by simpa only [hs, levelLE] using hhigh
            exact ⟨s, rfl, by omega⟩
        obtain ⟨s, hs, hst⟩ := hlow
        obtain ⟨b, hb, hmem⟩ := blossom_cover_of_base_existence (t - 2) htlow hexists p.last s hs hst
        obtain ⟨A, hAe, hA, hprefix, hseg⟩ := blossom_shortest_relative (t - 2) b p.last hmem hb p rfl hp
        have hAlt : A.val < p.length := by
          by_cases he : A.val = p.length
          · have hA' : A = ⟨p.length, by omega⟩ := Fin.ext he
            have hbend : p.last = b := by simpa only [hA', last] using hA
            exact False.elim (blossom_excludes_base (t - 2) b hb (hbend ▸ hmem))
          · have := A.isLt
            omega
        by_cases hi : i.val < A.val
        · exact ih A.val (by omega) (p.take A.val (by omega)) rfl hprefix
            (by change 2 * A.val < t; omega) ⟨i.val, hi⟩ hib hit
        · exact p.lower_relative_edge_ne t hedge b hmem hb A hAe hA hseg (by omega) i (by omega) hit
  exact aux p.length p rfl hp hlen

/-- A shortest path to a lower-tenacity endpoint has no bridge of the current
threshold. Its prefix to the lower boundary is short; its suffix uses lower
relative edge bounds. -/
theorem lower_shortest_no_bridge (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b)
    (hedge : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ i : Fin q.length, levelLE (edgeTenacity M (q.vertex ⟨i.val, by omega⟩)
          (q.vertex ⟨i.val + 1, by omega⟩)) (some (t - 2)))
    (p : AltPath M) (hp : p.Shortest) (s : Nat) (hs : tenacity M p.last = some s) (hst : s < t) :
    p.NoBridgeOfTenacity t := by
  have hsodd := tenacity_odd M p.last s hs
  have htlow : (t - 2) % 2 = 1 := by omega
  obtain ⟨b, hb, hmem⟩ := blossom_cover_of_base_existence (t - 2) htlow hexists p.last s hs (by omega)
  obtain ⟨A, hAe, hA, hprefix, hseg⟩ := blossom_shortest_relative (t - 2) b p.last hmem hb p rfl hp
  let q := p.take A.val (by omega)
  let r := p.segment A.val (by omega) hAe
  have hrfirst : r.first = b := (p.segment_first _ _ _).trans hA
  have hrlast : r.last = p.last := p.segment_last _ _ _
  have hbound := (blossom_relative_length_formula (t - 2) b p.last hmem hb q hprefix hAe hA
    r hseg hrfirst hrlast s hs).2
  change 2 * A.val + (p.length - A.val) ≤ s at hbound
  have hshort : 2 * A.val < t := by have := A.isLt; omega
  have hprefixno := short_shortest_no_bridge t ht hexists hedge q hprefix hshort
  intro i hib hit
  by_cases hi : i.val < A.val
  · exact hprefixno ⟨i.val, hi⟩ hib hit
  · exact p.lower_relative_edge_ne t hedge b hmem hb A hAe hA hseg (by omega) i (by omega) hit

end MaximumMatching.AltPath

end GeneralBridgeAbsence

section GeneralBridgeSplit

/-! Exact-tenacity bridge bookkeeping and local unmatched-edge transitions.
Lower-tenacity bridges are explicitly allowed in every uniqueness statement. -/
namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Exactly one bridge occurrence has the specified tenacity. -/
def UniqueBridgeOfTenacity (p : AltPath M) (t : Nat) : Prop :=
  ∃ i : Fin p.length,
    Bridge M (p.vertex ⟨i.val, by omega⟩) (p.vertex ⟨i.val + 1, by omega⟩) ∧
    edgeTenacity M (p.vertex ⟨i.val, by omega⟩) (p.vertex ⟨i.val + 1, by omega⟩) = some t ∧
    ∀ j : Fin p.length, Bridge M (p.vertex ⟨j.val, by omega⟩)
      (p.vertex ⟨j.val + 1, by omega⟩) →
      edgeTenacity M (p.vertex ⟨j.val, by omega⟩) (p.vertex ⟨j.val + 1, by omega⟩) = some t → j = i

/-- Preserve the unique target-tenacity bridge when the remaining suffix has
none of that tenacity. -/
theorem unique_bridge_of_prefix (p : AltPath M) (t K : Nat) (hK : K ≤ p.length)
    (hprefix : (p.take K hK).UniqueBridgeOfTenacity t)
    (htail : ∀ j : Fin p.length, K ≤ j.val →
      Bridge M (p.vertex ⟨j.val, by omega⟩) (p.vertex ⟨j.val + 1, by omega⟩) →
      edgeTenacity M (p.vertex ⟨j.val, by omega⟩) (p.vertex ⟨j.val + 1, by omega⟩) ≠ some t) :
    p.UniqueBridgeOfTenacity t := by
  obtain ⟨i, hib, hit, hiuniq⟩ := hprefix
  have hiK : i.val < K := i.isLt
  refine ⟨⟨i.val, by omega⟩, hib, hit, ?_⟩
  intro j hjb hjt
  by_cases hjK : j.val < K
  · have heq := hiuniq ⟨j.val, hjK⟩ hjb hjt
    exact Fin.ext (congrArg (fun a : Fin (p.take K hK).length => a.val) heq)
  · exact False.elim (htail j (by omega) hjb hjt)

/-- Insert the unique target-tenacity bridge between a prefix and suffix
which contain no target-tenacity bridge. -/
theorem unique_bridge_at_split (p : AltPath M) (t : Nat) (I : Fin p.length)
    (hprefix : (p.take I.val (by omega)).NoBridgeOfTenacity t)
    (hIb : Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩))
    (hIt : edgeTenacity M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩) = some t)
    (htail : ∀ j : Fin p.length, I.val < j.val →
      Bridge M (p.vertex ⟨j.val, by omega⟩) (p.vertex ⟨j.val + 1, by omega⟩) →
      edgeTenacity M (p.vertex ⟨j.val, by omega⟩) (p.vertex ⟨j.val + 1, by omega⟩) ≠ some t) :
    p.UniqueBridgeOfTenacity t := by
  refine ⟨I, hIb, hIt, ?_⟩
  intro j hjb hjt
  by_cases hji : j.val < I.val
  · exact False.elim (hprefix ⟨j.val, hji⟩ hjb hjt)
  · by_cases hij : I.val < j.val
    · exact False.elim (htail j hij hjb hjt)
    · exact Fin.ext (by omega)

/-- The honest even prefix ending at a bridge endpoint is either short or
ends at a vertex strictly below that bridge's tenacity. -/
theorem bridge_even_prefix_lower_or_short (p : AltPath M) (hp : p.Shortest)
    (hpe : p.length % 2 = 0) (v : V) (hb : Bridge M p.last v)
    (hm : M.mate p.last ≠ some v) (t : Nat) (ht : edgeTenacity M p.last v = some t) :
    (∃ s, tenacity M p.last = some s ∧ s < t) ∨ 2 * p.length < t := by
  have he : evenlevel M p.last = some p.length :=
    (level_eq_some_iff M 0 p.last p.length).2 (by simpa only [Shortest, hpe] using hp)
  by_cases hout : Outer M p.last
  · obtain ⟨s, hs, hst⟩ := (unmatched_bridge_tenacity hb hm t ht).1 hout
    by_cases hstrict : s < t
    · exact Or.inl ⟨s, hs, hstrict⟩
    · have hmin : minlevel M p.last = some p.length := (minlevel_eq_even_of_outer p.last hout).trans he
      have hb := twice_minlevel_le_tenacity p.last p.length s hmin hs
      have hsodd := tenacity_odd M p.last s hs
      exact Or.inr (by omega)
  · have hfinite : ∃ k, minlevel M p.last = some k := by
      obtain ⟨k, hk, _⟩ := minlevel_finite_of_path p
      exact ⟨k, hk⟩
    exact Or.inl ((unmatched_bridge_tenacity hb hm t ht).2 ⟨hfinite, hout⟩)

end AltPath

/-- The minimum level of an unmatched prop destination is one greater than
its predecessor's evenlevel. -/
theorem unmatched_predecessor_minlevel {V : Type} {G : Graph V} {M : Matching G}
    (u v : V) (hpred : Predecessor M u v) (hm : M.mate u ≠ some v)
    (e : Nat) (he : evenlevel M u = some e) : minlevel M v = some (e + 1) := by
  obtain ⟨p, hpv, hpmin, hpos, hpu⟩ := hpred
  have hpo : p.length % 2 = 1 := by
    have ha := p.alternating ⟨p.length - 1, by omega⟩
    have hn : ¬(p.length - 1) % 2 = 1 := by
      intro h
      apply hm
      have hh := ha.2 h
      have hlast : p.vertex ⟨p.length, by omega⟩ = v := hpv
      simpa only [hpu, show p.length - 1 + 1 = p.length by omega, hlast] using hh
    omega
  have hhon := (p.honest_iff_level ⟨p.length - 1, by omega⟩).1
    (p.minlevel_last_predecessor_honest (by rw [hpv]; exact hpmin) hpos)
  have hlev : evenlevel M u = some (p.length - 1) := by
    simpa only [show (p.length - 1) % 2 = 0 by omega, hpu] using hhon
  have heq := Option.some.inj (he.symm.trans hlev)
  exact hpmin.trans (congrArg some (by omega))

namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Traversing an unmatched prop backward at an honest even prefix yields
exactly the current-tenacity maximum level. -/
theorem even_prefix_maxlevel_of_reverse_prop (p : AltPath M) (hp : p.Shortest)
    (hpe : p.length % 2 = 0) (v : V) (hpred : Predecessor M v p.last)
    (hm : M.mate p.last ≠ some v) (t : Nat) (ht : edgeTenacity M p.last v = some t) :
    tenacity M p.last = some t ∧ maxlevel M p.last = some p.length := by
  have he : evenlevel M p.last = some p.length :=
    (level_eq_some_iff M 0 p.last p.length).2 (by simpa only [Shortest, hpe] using hp)
  have ht' : (levelAdd (evenlevel M p.last) (evenlevel M v)).map (· + 1) = some t := by
    simpa only [edgeTenacity, ite_eq_right hm] using ht
  have hf : ∃ f, evenlevel M v = some f ∧ p.length + f + 1 = t := by
    rw [he] at ht'
    cases hv : evenlevel M v with
    | none => simp only [hv, levelAdd, Option.map_none] at ht'; contradiction
    | some f => exact ⟨f, rfl, by simpa only [hv, levelAdd, Option.map_some, Option.some.injEq] using ht'⟩
  obtain ⟨f, hve, hsum⟩ := hf
  have hfp := level_parity M 0 v f hve
  have hmin := unmatched_predecessor_minlevel v p.last hpred (fun h => hm (M.symm h)) f hve
  have ho : oddlevel M p.last = some (f + 1) := by
    have hh := level_of_minlevel p.last (f + 1) hmin
    simpa only [show (f + 1) % 2 = 1 by omega] using hh
  have hle := minlevel_le_path M p.last (f + 1) hmin p rfl
  constructor
  · simp only [tenacity, he, ho, levelAdd]
    exact congrArg some (by omega)
  · simp only [maxlevel, he, ho, levelMax, Nat.max_eq_left hle]

end AltPath
end MaximumMatching

end GeneralBridgeSplit

section GeneralBlossomProps

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

end GeneralBlossomProps

section GeneralBridgeFirstEntry

/-! The bridge recurrence at a first lower-blossom entry. The crossing has
current tenacity, while the actual reversed tail has only lower-tenacity edges. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Original tail edges inherit the lower bound from the actual shortest
reversed relative path; symmetry handles their orientation. -/
theorem first_entry_tail_edge_ne (p : AltPath M) (hpo : p.length % 2 = 1)
    (t : Nat) (hpt : tenacity M p.last = some t)
    (hedge : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ i : Fin q.length, levelLE (edgeTenacity M (q.vertex ⟨i.val, by omega⟩)
          (q.vertex ⟨i.val + 1, by omega⟩)) (some (t - 2)))
    (D : Fin (p.length + 1)) (hDmem : Blossom M (t - 2) p.last (p.vertex D))
    (htail : (p.reverseOddTail hpo D).Shortest) (i : Fin p.length) (hDi : D.val ≤ i.val) :
    edgeTenacity M (p.vertex ⟨i.val, by omega⟩) (p.vertex ⟨i.val + 1, by omega⟩) ≠ some t := by
  have htodd := tenacity_odd M p.last t hpt
  have hc : levelLT (some (t - 2)) (tenacity M p.last) := by rw [hpt]; change t - 2 < t; omega
  let q := p.reverseOddTail hpo D
  let K : Fin q.length := ⟨p.length - (i.val + 1), by change p.length - (i.val + 1) < p.length - D.val; omega⟩
  have hbound := hedge p.last (p.vertex D) hDmem hc q htail
    (p.reverseOddTail_first hpo D) (p.reverseOddTail_last hpo D) K
  have hleft : q.vertex ⟨K.val, by omega⟩ = p.vertex ⟨i.val + 1, by omega⟩ := by
    change p.vertex ⟨p.length - (p.length - (i.val + 1)), _⟩ = _
    congr 1
    apply Fin.ext
    change p.length - (p.length - (i.val + 1)) = i.val + 1
    omega
  have hright : q.vertex ⟨K.val + 1, by omega⟩ = p.vertex ⟨i.val, by omega⟩ := by
    change p.vertex ⟨p.length - (p.length - (i.val + 1) + 1), _⟩ = _
    congr 1
    apply Fin.ext
    change p.length - (p.length - (i.val + 1) + 1) = i.val
    omega
  rw [hleft, hright, edgeTenacity_symmetric] at hbound
  intro he
  rw [he] at hbound
  change t ≤ t - 2 at hbound
  omega

/-- A prop crossing into the endpoint's lower blossom must be traversed
backwards, so the honest outside prefix is a current-tenacity maxlevel path. -/
theorem first_entry_prop_prefix_maxlevel (p : AltPath M) (hp : p.Shortest)
    (hpo : p.length % 2 = 1) (t : Nat) (hpt : tenacity M p.last = some t)
    (hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w)
    (D : Fin (p.length + 1)) (hDo : D.val % 2 = 1)
    (hDmem : Blossom M (t - 2) p.last (p.vertex D))
    (hfirst : ∀ a : Fin (p.length + 1), a.val < D.val → ¬Blossom M (t - 2) p.last (p.vertex a))
    (htail : (p.reverseOddTail hpo D).Shortest)
    (hprefix : p.BFSHonest ⟨D.val - 1, by omega⟩)
    (hprop : PropEdge M (p.vertex ⟨D.val - 1, by omega⟩) (p.vertex D)) :
    tenacity M (p.vertex ⟨D.val - 1, by omega⟩) = some t ∧
      maxlevel M (p.vertex ⟨D.val - 1, by omega⟩) = some (D.val - 1) := by
  have htodd := tenacity_odd M p.last t hpt
  have hc : levelLT (some (t - 2)) (tenacity M p.last) := by rw [hpt]; change t - 2 < t; omega
  have hreverse : Predecessor M (p.vertex D) (p.vertex ⟨D.val - 1, by omega⟩) := by
    rcases hprop with hforward | hreverse
    · rcases blossom_predecessor_mem (t - 2) p.last (p.vertex ⟨D.val - 1, by omega⟩)
        (p.vertex D) hDmem hc hconf hforward with he | hm
      · have hi := congrArg Fin.val (p.injective ⟨D.val - 1, by omega⟩ ⟨p.length, by omega⟩ he)
        change D.val - 1 = p.length at hi
        have := D.isLt
        omega
      · exact False.elim (hfirst ⟨D.val - 1, by omega⟩ (by change D.val - 1 < D.val; omega) hm)
    · exact hreverse
  let r := p.take (D.val - 1) (by omega)
  have hre : r.length % 2 = 0 := by change (D.val - 1) % 2 = 0; omega
  have hm : M.mate r.last ≠ some (p.vertex D) := by
    intro h
    change M.mate (p.vertex ⟨D.val - 1, by omega⟩) = some (p.vertex D) at h
    have hh := (p.alternating ⟨D.val - 1, by omega⟩).1
      (by simpa only [show D.val - 1 + 1 = D.val by omega] using h)
    change (D.val - 1) % 2 = 1 at hh
    omega
  exact r.even_prefix_maxlevel_of_reverse_prop hprefix hre (p.vertex D) hreverse hm t
    (p.first_entry_edge_tenacity hp hpo t hpt D hDo hDmem htail hprefix)

end MaximumMatching.AltPath

end GeneralBridgeFirstEntry

section GeneralBridge

/-! Unique bridge at the endpoint tenacity on arbitrary maxlevel paths.
The induction uses only lower-cutoff bases, confinement, and relative edge
bounds. Other bridge tenacities on the path are allowed. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The general unique-bridge step, also suitable at the shortest augmenting
path threshold: only structural information strictly below `t` is needed. -/
theorem unique_bridge_maxlevel_of_lower (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w)
    (hedge : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ i : Fin q.length, levelLE (edgeTenacity M (q.vertex ⟨i.val, by omega⟩)
          (q.vertex ⟨i.val + 1, by omega⟩)) (some (t - 2)))
    (p : AltPath M) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length) : p.UniqueBridgeOfTenacity t := by
  have no_bridge (r : AltPath M) (hr : r.Shortest)
      (hcase : (∃ s, tenacity M r.last = some s ∧ s < t) ∨ 2 * r.length < t) :
      r.NoBridgeOfTenacity t := by
    rcases hcase with ⟨s, hs, hst⟩ | hshort
    · exact lower_shortest_no_bridge t ht hexists hedge r hr s hs hst
    · exact short_shortest_no_bridge t ht hexists hedge r hr hshort
  have aux : ∀ L (p : AltPath M), p.length = L → tenacity M p.last = some t →
      maxlevel M p.last = some p.length → p.UniqueBridgeOfTenacity t := by
    intro L
    induction L using Nat.strongRecOn with
    | ind L ih =>
      intro p hpL hpt hmax
      have hp := p.shortest_of_maxlevel hmax
      have hpos : 0 < p.length := by
        obtain ⟨e, o, he, ho, _, hop, _⟩ := finite_levels_of_tenacity p.last t hpt
        have hlen : max e o = p.length := by simpa only [maxlevel, he, ho, levelMax, Option.some.injEq] using hmax
        omega
      let pred : Fin (p.length + 1) := ⟨p.length - 1, by omega⟩
      by_cases hpred : p.BFSHonest pred
      · obtain ⟨hfinal, hcases⟩ := p.honest_terminal_bridge_cases hp t hpt hmax hpos hpred
        let I : Fin p.length := ⟨p.length - 1, by omega⟩
        have hnext : p.length - 1 + 1 = p.length := by omega
        rcases hcases with ⟨hbridge, hcase⟩ | ⟨hprop, hten, hmaxpred⟩
        · apply p.unique_bridge_at_split t I (no_bridge (p.take (p.length - 1) (by omega)) hpred hcase)
          · simpa only [I, hnext, last] using hbridge
          · simpa only [I, hnext, last] using hfinal
          · intro j hij _ _
            have := j.isLt
            change p.length - 1 < j.val at hij
            omega
        · have hprefix := ih (p.length - 1) (by omega) (p.take (p.length - 1) (by omega)) rfl hten hmaxpred
          apply p.unique_bridge_of_prefix t (p.length - 1) (by omega) hprefix
          intro j hj hjb _
          have hjeq : j.val = p.length - 1 := by have := j.isLt; omega
          have hprop' : PropEdge M (p.vertex ⟨j.val, by omega⟩) (p.vertex ⟨j.val + 1, by omega⟩) := by
            simpa only [hjeq, hnext, last] using hprop
          exact hjb.2 hprop'
      · obtain ⟨hpo, houter⟩ := p.dishonest_last_predecessor_outer hp t hpt hpos hpred
        have hlow : ∃ s, tenacity M (p.vertex pred) = some s ∧ s < t := by
          by_cases hhigh : levelLE (some t) (tenacity M (p.vertex pred))
          · exact False.elim (hpred (p.limited_bfs_honesty hp pred (by rw [hpt]; exact hhigh)).1)
          · cases hs : tenacity M (p.vertex pred) with
            | none => exact False.elim (hhigh (by rw [hs]; trivial))
            | some s =>
              refine ⟨s, rfl, ?_⟩
              have hn : ¬t ≤ s := by simpa only [hs, levelLE] using hhigh
              omega
        obtain ⟨s, hs, hst⟩ := hlow
        have hsodd := tenacity_odd M (p.vertex pred) s hs
        have hmember := (p.dishonest_outer_predecessor_base hp hpo houter t s hpt hs hst
          (hexists (p.vertex pred) s hs (by omega)) hpred).2
        have hc : levelLT (some (t - 2)) (tenacity M p.last) := by rw [hpt]; change t - 2 < t; omega
        obtain ⟨D, hDo, hDmem, hfirst, htail, _⟩ := p.exists_first_entry_confined_tail hp hpo (t - 2) hc
          (by intro v hv q hq hqf hql; exact hconf p.last v hv hc q hq hqf hql) ⟨pred, hmember⟩
        have hprefix := p.first_entry_prefix_honest hp hpo t hpt hexists hconf D hDo hDmem hfirst htail
        have hentry := p.first_entry_edge_tenacity hp hpo t hpt D hDo hDmem htail hprefix
        let I : Fin p.length := ⟨D.val - 1, by have := D.isLt; omega⟩
        let r := p.take I.val (by omega)
        have hrLast : r.last = p.vertex ⟨D.val - 1, by omega⟩ := rfl
        have hre : r.length % 2 = 0 := by change (D.val - 1) % 2 = 0; omega
        have hnext : D.val - 1 + 1 = D.val := by omega
        have htailno : ∀ j : Fin p.length, I.val < j.val →
            Bridge M (p.vertex ⟨j.val, by omega⟩) (p.vertex ⟨j.val + 1, by omega⟩) →
            edgeTenacity M (p.vertex ⟨j.val, by omega⟩) (p.vertex ⟨j.val + 1, by omega⟩) ≠ some t := by
          intro j hj _
          exact p.first_entry_tail_edge_ne hpo t hpt hedge D hDmem htail j (by change D.val - 1 < j.val at hj; omega)
        by_cases hprop : PropEdge M r.last (p.vertex D)
        · obtain ⟨hrten, hrmax⟩ := p.first_entry_prop_prefix_maxlevel hp hpo t hpt hconf D hDo hDmem
            hfirst htail hprefix hprop
          have hprefixunique := ih r.length (by change D.val - 1 < L; have := D.isLt; omega) r rfl hrten hrmax
          apply p.unique_bridge_of_prefix t I.val (by omega) hprefixunique
          intro j hj hjb hjt
          by_cases hij : I.val < j.val
          · exact htailno j hij hjb hjt
          · have hjeq : j.val = I.val := by omega
            have hprop' : PropEdge M (p.vertex ⟨j.val, by omega⟩) (p.vertex ⟨j.val + 1, by omega⟩) := by
              simpa only [hjeq, I, hnext, hrLast] using hprop
            exact hjb.2 hprop'
        · have hadj : G.Adj r.last (p.vertex D) := by
            have hh := p.adjacent I
            simpa only [I, hnext, hrLast] using hh
          have hbridge : Bridge M r.last (p.vertex D) := ⟨hadj, hprop⟩
          have hm : M.mate r.last ≠ some (p.vertex D) := by
            intro hm
            have hh := (p.alternating I).1 (by simpa only [I, hnext, hrLast] using hm)
            change (D.val - 1) % 2 = 1 at hh
            omega
          have hcase := r.bridge_even_prefix_lower_or_short hprefix hre (p.vertex D) hbridge hm t hentry
          apply p.unique_bridge_at_split t I (no_bridge r hprefix hcase)
          · simpa only [I, hnext, hrLast] using hbridge
          · simpa only [I, hnext] using hentry
          · exact htailno
  exact aux p.length p rfl hpt hmax

/-- Every maxlevel path of tenacity at most the shortest augmenting-path
length contains exactly one bridge of that tenacity. This includes equality
with the shortest augmenting-path length and assumes no structural oracle. -/
theorem general_maxlevel_path_unique_bridge (p : AltPath M) (t : Nat)
    (ht : AtMostShortestAugmenting M t) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length) : p.UniqueBridgeOfTenacity t := by
  have htodd := tenacity_odd M p.last t hpt
  have hcutlt : t - 2 < t := by omega
  have hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b := by
    intro v s hs hst
    have helig : EligibleTenacity M s := by
      refine ⟨tenacity_odd M v s hs, ⟨v, ?_⟩, ?_⟩
      · rw [hs]
        exact Nat.le_refl _
      · intro q hq
        have hbound := ht q hq
        omega
    obtain ⟨b, hb, _⟩ := general_unique_base M s helig v hs
    exact ⟨b, s, hs, hb⟩
  have lowerEligible (b v : V) (hv : Blossom M (t - 2) b v) : EligibleTenacity M (t - 2) := by
    obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound (t - 2) b v hv
    have hsodd := tenacity_odd M v s hs
    refine ⟨by omega, ⟨v, ?_⟩, ?_⟩
    · rw [hs]
      exact hst
    · intro q hq
      have hbound := ht q hq
      omega
  apply unique_bridge_maxlevel_of_lower t htodd hexists
  · intro b v hv hb q hq hqb hqv
    exact general_blossom_relative_confined M (t - 2) (lowerEligible b v hv) b v hv hb q hq hqb hqv
  · intro b v hv hb q hq hqb hqv k
    exact general_blossom_relative_edge_bound M (t - 2) (lowerEligible b v hv) b v hv hb q hq hqb hqv k
  · exact hpt
  · exact hmax

end MaximumMatching.AltPath

end GeneralBridge

section GeneralSupport

/-! Semantic coverage by actual bridge supports, derived from the general
unique bridge theorem. This does not assert that the concrete DDFS traversal
has computed these supports; different supports may overlap. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Every finite-tenacity vertex has an actual path attaining its maximum
parity level. -/
theorem finite_tenacity_maxlevel_path (v : V) (t : Nat) (ht : tenacity M v = some t) :
    ∃ p : AltPath M, p.last = v ∧ maxlevel M v = some p.length := by
  obtain ⟨e, o, he, ho, _, _, _⟩ := finite_levels_of_tenacity v t ht
  have hmax : maxlevel M v = some (max e o) := by simp only [maxlevel, he, ho, levelMax]
  have hl := level_of_maxlevel v (max e o) hmax
  obtain ⟨p, hpv, hplen, _⟩ := ((level_eq_some_iff M ((max e o) % 2) v (max e o)).1 hl).1
  exact ⟨p, hpv, by simpa only [hplen] using hmax⟩

/-- Every current-tenacity vertex belongs to a bridge support of exactly that
tenacity, including the shortest augmenting-path threshold. -/
theorem vertex_in_bridge_support (v : V) (t : Nat)
    (ht : AtMostShortestAugmenting M t) (hvt : tenacity M v = some t) :
    ∃ u w, edgeTenacity M u w = some t ∧ InSupport M u w v := by
  obtain ⟨p, hpv, hpmax⟩ := finite_tenacity_maxlevel_path v t hvt
  obtain ⟨i, hib, hit, _⟩ := p.general_maxlevel_path_unique_bridge t ht
    (by rw [hpv]; exact hvt) (by rw [hpv]; exact hpmax)
  refine ⟨p.vertex ⟨i.val, by omega⟩, p.vertex ⟨i.val + 1, by omega⟩, hit,
    hib, t, ht, hit, hvt, p, hpv, hpmax, ?_⟩
  exact ⟨i, Or.inl ⟨rfl, rfl⟩⟩

/-- The union of supports of all bridges of a permitted tenacity is exactly
that vertex-tenacity stratum. Supports are not asserted disjoint. -/
theorem tenacity_iff_bridge_support (v : V) (t : Nat)
    (ht : AtMostShortestAugmenting M t) :
    tenacity M v = some t ↔ ∃ u w, edgeTenacity M u w = some t ∧ InSupport M u w v := by
  constructor
  · exact vertex_in_bridge_support v t ht
  · rintro ⟨u, w, hit, _, s, _, his, hvs, _⟩
    have hst : s = t := Option.some.inj (his.symm.trans hit)
    simpa only [hst] using hvs

end MaximumMatching

end GeneralSupport
