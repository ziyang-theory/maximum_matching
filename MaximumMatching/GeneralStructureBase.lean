import MaximumMatching.GeneralStructureStep

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
  have ht' : EligibleTenacity M (p.length + q.length) := hsum ▸ ht
  have hexists' : ∀ (w : V) (s : Nat), tenacity M w = some s → s ≤ p.length + q.length - 2 →
      ∃ b, IsBase M w b := by simpa only [hsum] using hexists
  have hconf' : ∀ (b w : V), Blossom M (p.length + q.length - 2) b w →
      levelLT (some (p.length + q.length - 2)) (tenacity M b) →
      ∀ r : AltSegment M, r.Shortest → r.first = b → r.last = w →
        ∀ x, r.Contains x → x = b ∨ Blossom M (p.length + q.length - 2) b x := by
    simpa only [hsum] using hconf
  have ih' : ∀ (w : V) (j : Nat), minlevel M w = some j → j < q.length →
      tenacity M w = some (p.length + q.length) → HasUniqueBase M w (p.length + q.length) := by
    intro w j hw hj hwt
    rw [hsum] at hwt ⊢
    exact ih w j hw (by omega) hwt
  have h := p.general_parity_bases_agree q hp hq hpe hqo
    (hqv.trans hpv.symm) hinner' ht' hexists' hconf' ih' b
  simpa only [hsum] using h


end MaximumMatching
