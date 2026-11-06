import MaximumMatching.GeneralBridgeAbsence
import MaximumMatching.BridgeClassification
import MaximumMatching.MinScan

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
