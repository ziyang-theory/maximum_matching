import MaximumMatching.GeneralStructureMinimize
import MaximumMatching.GeneralPredecessorBlossom

/-! The ordered common-base step. Lower-tenacity base existence and confinement,
plus bases at smaller current minimum levels, determine opposite path bases
whenever the odd path's base is no later than the even path's base. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- In the lower-predecessor case, actual path bases agree when their minimum
levels are ordered from the odd path to the even path. -/
theorem low_predecessor_bases_eq_of_minlevel_le (p q : AltPath M)
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
    (hst : s < p.length + q.length)
    (b d : V) (hpb : p.BaseOnPath (p.length + q.length) b)
    (hqd : q.BaseOnPath (p.length + q.length) d)
    (horder : levelLE (minlevel M d) (minlevel M b)) : b = d := by
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hqten : tenacity M q.last = some (p.length + q.length) := by rw [hend]; exact hten
  obtain ⟨B, hBb, hBe⟩ := p.baseOnPath_even (p.length + q.length) hten hpb
  obtain ⟨D, hDd, hdhigh, hdlast⟩ := hqd
  have hbhigh := hpb.choose_spec.2.1
  have hBhigh : levelLT (some (p.length + q.length)) (tenacity M (p.vertex B)) := by
    rw [hBb]
    exact hbhigh
  have hBmin : minlevel M b = some B.val := by
    have hh := (p.limited_bfs_honesty hp B (by rw [hten]; exact levelLT_le hBhigh)).2
      (by rw [hten]; exact hBhigh)
    simpa only [hBb] using hh
  have hDmin : minlevel M d = some D.val := by
    have hh := (q.limited_bfs_honesty hq D (by rw [hqten, hDd]; exact levelLT_le hdhigh)).2
      (by rw [hqten, hDd]; exact hdhigh)
    simpa only [hDd] using hh
  have hDB : D.val ≤ B.val := by simpa only [hDmin, hBmin, levelLE] using horder
  have hcurrent : ∀ (v : V) (k : Nat), minlevel M v = some k → k < q.length →
      tenacity M v = some (p.length + q.length) → ∃ a, IsBase M v a := by
    intro v k hmin hk ht
    obtain ⟨a, ha, _⟩ := ih v k hmin hk ht
    exact ⟨a, p.length + q.length, ht, ha⟩
  have hmember := p.low_predecessor_in_base_blossom q hp hq hpe hqo hend hinner
    hexists ih s hs hst d ⟨D, hDd, hdhigh, hdlast⟩
  have heq := p.current_blossom_boundary_eq q hp hq hpe hqo hend hinner
    hexists hconf hcurrent d hmember hdhigh D hDd B hBe hBhigh hDB
  exact hBb.symm.trans heq.symm

/-- All predecessor cases are included in this ordered step. The opposite
order is handled in GeneralStructureStep using the even-witness minimization. -/
theorem parity_bases_eq_of_minlevel_le (p q : AltPath M)
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
    (b d : V) (hpb : p.BaseOnPath (p.length + q.length) b)
    (hqd : q.BaseOnPath (p.length + q.length) d)
    (horder : levelLE (minlevel M d) (minlevel M b)) : b = d := by
  by_cases hge : levelLE (some (p.length + q.length))
      (tenacity M (q.vertex ⟨q.length - 1, by omega⟩))
  · have hqb := (p.parity_bases_agree_of_predecessor_ge q hp hq hpe hqo hend hinner hge ih b).1 hpb
    exact q.baseOnPath_unique _ b d hqb hqd
  · cases hs : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) with
    | none => exact False.elim (hge (by rw [hs]; trivial))
    | some s =>
      have hst : s < p.length + q.length := by
        have hh : ¬p.length + q.length ≤ s := by simpa only [hs, levelLE] using hge
        omega
      exact p.low_predecessor_bases_eq_of_minlevel_le q hp hq hpe hqo hend hinner
        hexists hconf ih s hs hst b d hpb hqd horder

end MaximumMatching.AltPath
