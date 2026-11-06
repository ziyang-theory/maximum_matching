import MaximumMatching.BridgePending

/-! Completeness of the current tenacity bucket after concrete MIN. Earlier
MAX assignment/refresh events are captured by initialized and preserved state
invariants. No completeness of the current MAX support search is assumed. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

theorem semantic_edgeTenacity_comm (u v : V) : edgeTenacity M u v = edgeTenacity M v u := by
  classical
  by_cases hm : M.mate u = some v
  · have hm' := M.symm hm
    simp only [edgeTenacity, hm, hm', ite_true, matchedEdgeTenacity]
    cases he : oddlevel M u <;> cases hf : oddlevel M v <;> simp [levelAdd, Nat.add_comm]
  · have hm' : M.mate v ≠ some u := fun h => hm (M.symm h)
    simp only [edgeTenacity, hm, hm', ite_false]
    cases he : evenlevel M u <;> cases hf : evenlevel M v <;> simp [levelAdd, Nat.add_comm]

theorem unmatched_bridge_outer_minlevel_bound (u v : V) (i k : Nat)
    (hb : Bridge M u v) (hn : M.mate u ≠ some v) (hu : Outer M u)
    (ht : edgeTenacity M u v = some (2 * i + 1)) (hk : minlevel M u = some k) : k ≤ i := by
  obtain ⟨t, hut, hti⟩ := (unmatched_bridge_tenacity hb hn (2 * i + 1) ht).1 hu
  obtain ⟨e, o, he, ho, _, _, hsum⟩ := finite_levels_of_tenacity u t hut
  have hmin : minlevel M u = some e := (minlevel_eq_even_of_outer u hu).trans he
  have hek := Option.some.inj (hmin.symm.trans hk)
  have hlt : e < o := by simpa only [Outer, he, ho, levelLT] using hu
  omega

namespace Search
variable [DecidableEq V]

omit [DecidableEq V] in
/-- Lemma 8.1 puts a bridge endpoint's required evenlevel either at a known
outer minlevel ≤i or at an inner maxlevel assigned at a strictly earlier
vertex tenacity. Both cases use actual operational label lookup. -/
theorem unmatched_bridge_evenLabel_available (s : State V) (i : Nat) (u v : V)
    (hc : MinCompleteBelow M i s) (hx : MaxCompleteBelowTenacity M (2 * i + 1) s)
    (hb : Bridge M u v) (hn : M.mate u ≠ some v)
    (ht : MaximumMatching.edgeTenacity M u v = some (2 * i + 1))
    (e : Nat) (he : evenlevel M u = some e) : parityLabel s u 0 = some e := by
  have hep := level_parity M 0 u e he
  by_cases hu : Outer M u
  · have hmin : minlevel M u = some e := (minlevel_eq_even_of_outer u hu).trans he
    have hei := unmatched_bridge_outer_minlevel_bound u v i e hb hn hu ht hmin
    have hlabel := hc u e hmin hei
    simp [parityLabel, hlabel, hep]
  · obtain ⟨k, hk, _⟩ := minlevel_le_of_level u e (by simpa only [hep] using he)
    have hinner : Inner M u := ⟨⟨k, hk⟩, hu⟩
    obtain ⟨t, hut, hti⟩ := (unmatched_bridge_tenacity hb hn (2 * i + 1) ht).2 hinner
    obtain ⟨o, ho, hoe, hmin⟩ := inner_oddlevel_lt_evenlevel u e he hinner
    have hop := level_parity M 1 u o ho
    have hsum : e + o = t := by simpa only [tenacity, he, ho, levelAdd, Option.some.injEq] using hut
    have hmax : maxlevel M u = some e := by simp [maxlevel, he, ho, levelMax, Nat.max_eq_left (by omega : o ≤ e)]
    have hlabel := hc u o hmin (by omega)
    have hlabelmax := (hx u t hut hti).trans hmax
    simp [parityLabel, hlabel, hlabelmax, hop, hep]

/-- Every unmatched bridge of current tenacity already has a computable
operational tenacity before this MIN pass, including both mixed and inner cases. -/
theorem unmatched_bridge_tenacity_available (s : State V) (i : Nat) (u v : V)
    (hc : MinCompleteBelow M i s) (hx : MaxCompleteBelowTenacity M (2 * i + 1) s)
    (hb : Bridge M u v) (hn : M.mate u ≠ some v)
    (ht : MaximumMatching.edgeTenacity M u v = some (2 * i + 1)) :
    edgeTenacity M s u v = some (2 * i + 1) := by
  have ht' : (levelAdd (evenlevel M u) (evenlevel M v)).map (· + 1) = some (2 * i + 1) := by
    simpa only [MaximumMatching.edgeTenacity, hn, ite_false] using ht
  cases he : evenlevel M u with
  | none => simp [he, levelAdd] at ht'
  | some e =>
    cases hf : evenlevel M v with
    | none => simp [he, hf, levelAdd] at ht'
    | some f =>
      have he' := unmatched_bridge_evenLabel_available s i u v hc hx hb hn ht e he
      have hnm : M.mate v ≠ some u := fun h => hn (M.symm h)
      have hf' := unmatched_bridge_evenLabel_available s i v u hc hx (bridge_symm hb) hnm
        ((semantic_edgeTenacity_comm v u).trans ht) f hf
      simpa [edgeTenacity, hn, he', hf', he, hf, levelAdd] using ht'

theorem scanCandidates_preserves_edgeTenacity [DecidableRel G.Adj]
    (xs : List (V × V)) (s : State V) (i : Nat) (u v : V) (t : Nat)
    (hi : MinInvariant M i s) (ht : edgeTenacity M s u v = some t) :
    edgeTenacity M (scanCandidates M i xs s) u v = some t := by
  induction xs generalizing s with
  | nil => exact ht
  | cons e es ih =>
    exact ih _ (scanCandidate_minInvariant s i e.1 e.2 hi)
      (scanCandidate_preserves_edgeTenacity s i e.1 e.2 u v t hi ht)

/-- Task 2: the actual MIN enumeration has queued every bridge of tenacity
2i+1, in either stored orientation. The mixed/inner cases use the pending-event
invariant maintained by previous actual MAX refresh steps. -/
theorem scanLevel_current_bucket_complete {n : Nat} {G : Graph (Fin n)} [DecidableRel G.Adj]
    (M : Matching G) (s : State (Fin n)) (i : Nat)
    (hi : MinInvariant M i s) (hx : MaxCompleteBelowTenacity M (2 * i + 1) s)
    (hm : MaxLabelsHaveMin s) (hbefore : ScannedBefore M i s) (hp : UnmatchedPending M i s)
    (u v : Fin n) (hb : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (2 * i + 1)) :
    EdgeInBucket (scanLevel M i s) (2 * i + 1) u v := by
  have hf := frontierAvailable_of_prior_levels s i hi.2.1 hx
  by_cases hn : M.mate u = some v
  · exact scanLevel_matched_bridge_queued M s i u v hi hf hbefore hb hn ht
  · have havail := unmatched_bridge_tenacity_available s i u v hi.2.1 hx hb hn ht
    have hknown := scanCandidates_preserves_edgeTenacity (allCandidates n) s i u v (2 * i + 1) hi havail
    have hpending := scanLevel_unmatchedPending M s i hi hf hm hbefore hp u v (2 * i + 1) hb hn hknown
    rcases hpending with hq | houter | houter
    · exact hq
    · obtain ⟨hu, k, hk, hki⟩ := houter
      have hle := unmatched_bridge_outer_minlevel_bound u v i k hb hn hu ht hk
      omega
    · obtain ⟨hv, k, hk, hki⟩ := houter
      have hnm : M.mate v ≠ some u := fun h => hn (M.symm h)
      have hle := unmatched_bridge_outer_minlevel_bound v u i k (bridge_symm hb) hnm hv
        ((semantic_edgeTenacity_comm v u).trans ht) hk
      omega

end Search
end MaximumMatching
