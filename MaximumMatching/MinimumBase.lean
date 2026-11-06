import MaximumMatching.MinimumBridgeAll
import MaximumMatching.BaseUnique

/-! Induction on minimum level for the common base at globally minimum finite
eligible tenacity. The inner-vertex argument uses the checked parity-agreement theorem; the
outer case reduces across its matched edge to a smaller minimum level. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V}

/-- Agreement between the even and odd shortest paths gives the common base;
existence comes from eligibility and uniqueness comes from one fixed path. -/
theorem unique_base_of_parity_agreement (M : Matching G) (t : Nat)
    (ht : EligibleTenacity M t) (v : V) (hvt : tenacity M v = some t)
    (agree : ∀ (p q : AltPath M), p.last = v → q.last = v →
      p.Shortest → q.Shortest → p.length % 2 = 0 → q.length % 2 = 1 →
      ∀ b, p.BaseOnPath t b ↔ q.BaseOnPath t b) : HasUniqueBase M v t := by
  obtain ⟨e, o, he, ho, hepar, hopar, _⟩ := finite_levels_of_tenacity v t hvt
  obtain ⟨p, hpv, hplen, _⟩ := ((level_eq_some_iff M 0 v e).1 he).1
  obtain ⟨q, hqv, hqlen, _⟩ := ((level_eq_some_iff M 1 v o).1 ho).1
  have hpe : p.length % 2 = 0 := by omega
  have hqo : q.length % 2 = 1 := by omega
  have hp : p.Shortest := by
    simpa only [AltPath.Shortest, hpe, hpv, hplen, hepar] using (level_eq_some_iff M 0 v e).1 he
  have hq : q.Shortest := by
    simpa only [AltPath.Shortest, hqo, hqv, hqlen, hopar] using (level_eq_some_iff M 1 v o).1 ho
  obtain ⟨b, hpb⟩ := p.baseOnPath_exists_of_eligible t ht
  have hqb := (agree p q hpv hqv hp hq hpe hqo b).1 hpb
  have hcommon : ∀ r : AltPath M, r.last = v → r.Shortest → r.BaseOnPath t b := by
    intro r hrv hr
    by_cases hre : r.length % 2 = 0
    · exact (agree r q hrv hqv hr hq hre hqo b).2 hqb
    · have hro : r.length % 2 = 1 := by omega
      exact (agree p r hpv hrv hp hr hpe hro b).1 hpb
  refine ⟨b, hcommon, ?_⟩
  intro c hc
  exact p.baseOnPath_unique t c b (hc p hpv hp) hpb

/-- The outer case reduces to its matched neighbor at a strictly smaller
minimum level. The only induction step left to the caller is the inner case. -/
theorem minimum_unique_base_induction (M : Matching G) (t : Nat)
    (ht : EligibleTenacity M t)
    (innerStep : ∀ (v : V) (k : Nat), minlevel M v = some k → Inner M v →
      tenacity M v = some t →
      (∀ (u : V) (j : Nat), minlevel M u = some j → j < k →
        tenacity M u = some t → HasUniqueBase M u t) → HasUniqueBase M v t)
    (v : V) (hvt : tenacity M v = some t) : HasUniqueBase M v t := by
  have aux : ∀ k (w : V), minlevel M w = some k → tenacity M w = some t →
      HasUniqueBase M w t := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro w hw hwt
      obtain ⟨e, o, he, ho, hepar, hopar, hsum⟩ := finite_levels_of_tenacity w t hwt
      by_cases houter : e < o
      · have hek : e = k := by
          simpa only [minlevel, he, ho, levelMin, Nat.min_eq_left (show e ≤ o by omega),
            Option.some.injEq] using hw
        obtain ⟨u, hm⟩ := eligible_vertex_matched M t ht w hwt
        have hodd := evenlevel_matched M (M.symm hm)
        have heven := evenlevel_matched M hm
        rw [he] at hodd
        rw [ho] at heven
        cases huo : oddlevel M u with
        | none => simp only [huo, Option.map_none] at hodd; contradiction
        | some j =>
          have hje : j + 1 = e := by
            simpa only [huo, Option.map_some, Option.some.injEq] using hodd.symm
          have huj : minlevel M u = some j := by
            simp only [minlevel, heven, Option.map_some, huo, levelMin]
            exact congrArg some (Nat.min_eq_right (by omega))
          have hut : tenacity M u = some t := (matched_tenacity M hm).1.symm.trans hwt
          have hub := ih j (by omega) u huj hut
          exact (matched_unique_base_iff M hm t hwt).2 hub
      · apply innerStep w k hw
        · refine ⟨⟨k, hw⟩, ?_⟩
          simpa only [Outer, he, ho, levelLT] using houter
        · exact hwt
        · intro u j hu hj hut
          exact ih j hj u hu hut
  obtain ⟨e, o, he, ho, _, _, _⟩ := finite_levels_of_tenacity v t hvt
  apply aux (min e o) v
  · simp only [minlevel, he, ho, levelMin]
  · exact hvt

/-- Lemma 6.13, Statement 1: every vertex of globally minimum finite eligible
tenacity has a path-independent base. The induction's inner step is discharged
by the proved parity agreement; no base-existence oracle is assumed. -/
theorem minimum_unique_base (M : Matching G) (t : Nat)
    (ht : EligibleTenacity M t)
    (hmin : ∀ w : V, levelLE (some t) (tenacity M w))
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
  have ht' : EligibleTenacity M (p.length + q.length) := hsum ▸ ht
  have hmin' : ∀ w : V, levelLE (some (p.length + q.length)) (tenacity M w) := hsum ▸ hmin
  have ih' : ∀ (w : V) (j : Nat), minlevel M w = some j → j < q.length →
      tenacity M w = some (p.length + q.length) → HasUniqueBase M w (p.length + q.length) := by
    intro w j hw hj hwt
    rw [hsum] at hwt ⊢
    exact ih w j hw (by omega) hwt
  have h := p.minimum_parity_bases_agree q hp hq hpe hqo
    (hqv.trans hpv.symm) hinner' ht' hmin' ih' b
  simpa only [hsum] using h

end MaximumMatching
