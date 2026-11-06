import MaximumMatching.MatchingGraphExpansion

/-! The first search-level boundary. Tenacity-one edges join free vertices
and give executable length-one augmenting paths; they require no blossom
expansion or artificial negative lower cutoff. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

theorem edge_tenacity_one_iff_free (u v : V) :
    edgeTenacity M u v = some 1 ↔ M.Free u ∧ M.Free v := by
  classical
  constructor
  · intro ht
    by_cases hm : M.mate u = some v
    · have hh : (levelAdd (oddlevel M u) (oddlevel M v)).map (· + 1) = some 1 := by
        simpa only [edgeTenacity, ite_eq_left hm, matchedEdgeTenacity] using ht
      cases hu : oddlevel M u with
      | none => simp only [hu, levelAdd, Option.map_none] at hh; contradiction
      | some a =>
        cases hv : oddlevel M v with
        | none => simp only [hu, hv, levelAdd, Option.map_none] at hh; contradiction
        | some b =>
          have ha := level_parity M 1 u a hu
          have hab : a + b + 1 = 1 := by
            simpa only [hu, hv, levelAdd, Option.map_some, Option.some.injEq] using hh
          omega
    · have hh : (levelAdd (evenlevel M u) (evenlevel M v)).map (· + 1) = some 1 := by
        simpa only [edgeTenacity, ite_eq_right hm] using ht
      cases hu : evenlevel M u with
      | none => simp only [hu, levelAdd, Option.map_none] at hh; contradiction
      | some a =>
        cases hv : evenlevel M v with
        | none => simp only [hu, hv, levelAdd, Option.map_none] at hh; contradiction
        | some b =>
          have hab : a + b + 1 = 1 := by
            simpa only [hu, hv, levelAdd, Option.map_some, Option.some.injEq] using hh
          exact ⟨(evenlevel_zero_iff_free M u).1 (by simpa only [show a = 0 by omega] using hu),
            (evenlevel_zero_iff_free M v).1 (by simpa only [show b = 0 by omega] using hv)⟩
  · rintro ⟨hu, hv⟩
    have hm : M.mate u ≠ some v := by rw [hu]; intro h; contradiction
    simp only [edgeTenacity, ite_eq_right hm, (evenlevel_zero_iff_free M u).2 hu,
      (evenlevel_zero_iff_free M v).2 hv, levelAdd, Option.map_some]

namespace AltPath

/-- Execute a one-edge augmentation witness directly from its free ends. -/
def freeEdge (u v : V) (hu : M.Free u) (hadj : G.Adj u v) : AltPath M :=
  (trivial M u hu).append v
    (fun _ he => G.loopless v (he ▸ hadj)) hadj
    (by change M.mate u = some v ↔ 0 % 2 = 1; rw [hu]; simp)

theorem freeEdge_augmenting (u v : V) (hu : M.Free u) (hv : M.Free v) (hadj : G.Adj u v) :
    (freeEdge u v hu hadj).Augmenting :=
  ⟨rfl, hv⟩

theorem freeEdge_contains (u v : V) (hu : M.Free u) (hadj : G.Adj u v) :
    (freeEdge u v hu hadj).ContainsEdge u v :=
  ⟨⟨0, by change 0 < 1; omega⟩, Or.inl ⟨rfl, rfl⟩⟩

end AltPath

/-- The entire tenacity-one bridge case has a real shortest augmenting
witness independently of the later odd-cutoff blossom representation. -/
theorem tenacity_one_bridge_augmenting (u v : V) (hb : Bridge M u v)
    (ht : edgeTenacity M u v = some 1) :
    ∃ p : AltPath M, p.Augmenting ∧ p.length = 1 ∧ p.ContainsEdge u v ∧
      ∀ q : AltPath M, q.Augmenting → p.length ≤ q.length := by
  obtain ⟨hu, hv⟩ := (edge_tenacity_one_iff_free u v).1 ht
  exact ⟨AltPath.freeEdge u v hu hb.1, AltPath.freeEdge_augmenting u v hu hv hb.1,
    rfl, AltPath.freeEdge_contains u v hu hb.1, fun q hq => q.augmenting_pos hq⟩

/-- Once length-one augmenting paths are absent, every vertex is above cut
one. Thus a singleton bud forest really represents the first lower cutoff. -/
theorem tenacity_above_one_of_no_short_augmenting
    (hnoaug : ∀ p : AltPath M, p.Augmenting → 1 < p.length) (v : V) :
    levelLT (some 1) (tenacity M v) := by
  cases ht : tenacity M v with
  | none => trivial
  | some t =>
    by_cases hlarge : 1 < t
    · exact hlarge
    · obtain ⟨e, o, he, _, hep, hop, hsum⟩ := finite_levels_of_tenacity v t ht
      have he0 : e = 0 := by omega
      have hf : M.Free v := (evenlevel_zero_iff_free M v).1 (by simpa only [he0] using he)
      have hh := free_tenacity_above M 1 v hf hnoaug
      rw [ht] at hh
      exact hh

namespace Search
variable [DecidableEq V]

theorem uncontracted_lower_representation_one (s : State V)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → 1 < p.length) :
    LowerBlossomRepresentation M 1 s (uncontractedForest s) := by
  intro v k _
  rw [(uncontractedForest s).root_of_fixed v rfl]
  exact ⟨tenacity_above_one_of_no_short_augmenting hnoaug v, Or.inl rfl⟩

end Search
end MaximumMatching
