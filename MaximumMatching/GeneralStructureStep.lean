import MaximumMatching.GeneralStructureOrdered
import MaximumMatching.GeneralStructureEvenMinimize

/-! The full current-tenacity inner induction step. Lower blossoms and bases at
smaller current minimum levels imply agreement of both shortest path parities,
including every low-predecessor case and either ordering of path bases. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The odd path's actual base occurs on every opposite even shortest path,
including when its last predecessor lies in a lower-tenacity blossom. -/
theorem low_predecessor_base_occurs (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ p.length + q.length - 2 →
      ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (p.length + q.length - 2) b v →
      levelLT (some (p.length + q.length - 2)) (tenacity M b) →
      ∀ r : AltSegment M, r.Shortest → r.first = b → r.last = v →
        ∀ w, r.Contains w → w = b ∨ Blossom M (p.length + q.length - 2) b w)
    (ih : ∀ (v : V) (k : Nat), minlevel M v = some k → k < q.length →
      tenacity M v = some (p.length + q.length) → HasUniqueBase M v (p.length + q.length))
    (s : Nat) (hs : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) = some s)
    (hst : s < p.length + q.length) (d : V) (hqd : q.BaseOnPath (p.length + q.length) d) :
    ∃ a, p.vertex a = d := by
  apply Classical.byContradiction
  intro hn
  have habsent : ∀ a, p.vertex a ≠ d := by intro a ha; exact hn ⟨a, ha⟩
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hqten : tenacity M q.last = some (p.length + q.length) := by rw [hend]; exact hten
  obtain ⟨D, hD, hDe⟩ := q.baseOnPath_even (p.length + q.length) hqten hqd
  have hdhigh := hqd.choose_spec.2.1
  have hmember := p.low_predecessor_in_base_blossom q hp hq hpe hqo hend hinner
    hexists ih s hs hst d hqd
  have hcurrent : ∀ (v : V) (k : Nat), minlevel M v = some k → k < q.length →
      tenacity M v = some (p.length + q.length) → ∃ a, IsBase M v a := by
    intro v k hmin hk ht
    obtain ⟨a, ha, _⟩ := ih v k hmin hk ht
    exact ⟨a, p.length + q.length, ht, ha⟩
  have hclosed : ∀ r : AltPath M, r.Shortest → Blossom M (p.length + q.length) d r.last →
      r.length < q.length → ∀ (i j : Fin (r.length + 1)), r.vertex i = d → i.val < j.val →
        Blossom M (p.length + q.length) d (r.vertex j) := by
    intro r hr hbl hlen i j hi hij
    exact r.short_blossom_suffix_mem hr (p.length + q.length) q.length (by omega)
      hlen (by omega) hexists hconf hcurrent d hdhigh hbl i j hi hij
  obtain ⟨r, hr, hre, hlen, hbl, hon⟩ := p.initial_even_blossom_candidate q hp hq hpe hqo
    hend hinner d D hD hDe hdhigh habsent hmember hclosed
  exact p.no_even_candidate_at_absent_boundary hp hpe q.length d hdhigh hclosed habsent
    r hr hre hbl hon hlen

/-- Actual bases of opposite shortest paths agree under the lower-tenacity
outer induction and strictly smaller-minlevel inner induction hypotheses. -/
theorem general_parity_bases_eq (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ p.length + q.length - 2 →
      ∃ a, IsBase M v a)
    (hconf : ∀ (a v : V), Blossom M (p.length + q.length - 2) a v →
      levelLT (some (p.length + q.length - 2)) (tenacity M a) →
      ∀ r : AltSegment M, r.Shortest → r.first = a → r.last = v →
        ∀ w, r.Contains w → w = a ∨ Blossom M (p.length + q.length - 2) a w)
    (ih : ∀ (v : V) (k : Nat), minlevel M v = some k → k < q.length →
      tenacity M v = some (p.length + q.length) → HasUniqueBase M v (p.length + q.length))
    (b d : V) (hpb : p.BaseOnPath (p.length + q.length) b)
    (hqd : q.BaseOnPath (p.length + q.length) d) : b = d := by
  by_cases hge : levelLE (some (p.length + q.length))
      (tenacity M (q.vertex ⟨q.length - 1, by omega⟩))
  · have hqb := (p.parity_bases_agree_of_predecessor_ge q hp hq hpe hqo hend hinner hge ih b).1 hpb
    exact q.baseOnPath_unique _ b d hqb hqd
  · have hlow : ∃ s, tenacity M (q.vertex ⟨q.length - 1, by omega⟩) = some s ∧
        s < p.length + q.length := by
      cases hs : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) with
      | none => exact False.elim (hge (by rw [hs]; trivial))
      | some s =>
        have hh : ¬p.length + q.length ≤ s := by simpa only [hs, levelLE] using hge
        exact ⟨s, rfl, by omega⟩
    obtain ⟨s, hs, hst⟩ := hlow
    obtain ⟨D, hD⟩ := p.low_predecessor_base_occurs q hp hq hpe hqo hend hinner
      hexists hconf ih s hs hst d hqd
    have hdhigh := hqd.choose_spec.2.1
    obtain ⟨B, hB, hbhigh, hlast⟩ := hpb
    have hDB : D.val ≤ B.val := by
      apply Nat.le_of_not_lt
      intro hlt
      exact hlast D hlt (by rw [hD]; exact hdhigh)
    have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
    have hBmin : minlevel M b = some B.val := by
      have hh := (p.limited_bfs_honesty hp B (by rw [hten, hB]; exact levelLT_le hbhigh)).2
        (by rw [hten, hB]; exact hbhigh)
      simpa only [hB] using hh
    have hDmin : minlevel M d = some D.val := by
      have hh := (p.limited_bfs_honesty hp D (by rw [hten, hD]; exact levelLT_le hdhigh)).2
        (by rw [hten, hD]; exact hdhigh)
      simpa only [hD] using hh
    exact p.low_predecessor_bases_eq_of_minlevel_le q hp hq hpe hqo hend hinner
      hexists hconf ih s hs hst b d ⟨B, hB, hbhigh, hlast⟩ hqd
      (by rw [hDmin, hBmin]; exact hDB)

/-- The full inner induction step, expressed as equality of the actual
path-relative base predicates. Eligibility supplies a base on each path. -/
theorem general_parity_bases_agree (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (ht : EligibleTenacity M (p.length + q.length))
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ p.length + q.length - 2 →
      ∃ a, IsBase M v a)
    (hconf : ∀ (a v : V), Blossom M (p.length + q.length - 2) a v →
      levelLT (some (p.length + q.length - 2)) (tenacity M a) →
      ∀ r : AltSegment M, r.Shortest → r.first = a → r.last = v →
        ∀ w, r.Contains w → w = a ∨ Blossom M (p.length + q.length - 2) a w)
    (ih : ∀ (v : V) (k : Nat), minlevel M v = some k → k < q.length →
      tenacity M v = some (p.length + q.length) → HasUniqueBase M v (p.length + q.length))
    (b : V) : p.BaseOnPath (p.length + q.length) b ↔ q.BaseOnPath (p.length + q.length) b := by
  constructor
  · intro hpb
    obtain ⟨d, hqd⟩ := q.baseOnPath_exists_of_eligible _ ht
    have he := p.general_parity_bases_eq q hp hq hpe hqo hend hinner hexists hconf ih b d hpb hqd
    exact he.symm ▸ hqd
  · intro hqb
    obtain ⟨d, hpd⟩ := p.baseOnPath_exists_of_eligible _ ht
    have he := p.general_parity_bases_eq q hp hq hpe hqo hend hinner hexists hconf ih d b hpd hqb
    exact he ▸ hpd

end MaximumMatching.AltPath
