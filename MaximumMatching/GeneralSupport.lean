import MaximumMatching.GeneralBridge

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
