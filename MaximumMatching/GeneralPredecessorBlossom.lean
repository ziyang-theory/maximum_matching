import MaximumMatching.GeneralBaseReroute

/-! Promote the low predecessor to the blossom of the odd path's actual
threshold base. Current-tenacity base uniqueness is invoked only at a strictly
smaller minlevel, at the already located lower-blossom boundary. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

theorem predecessor_blossom_promote (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (ih : ∀ (v : V) (k : Nat), minlevel M v = some k → k < q.length →
      tenacity M v = some (p.length + q.length) → HasUniqueBase M v (p.length + q.length))
    (c : V) (hc : Blossom M (p.length + q.length - 2) c
      (q.vertex ⟨q.length - 1, by omega⟩))
    (hchigh : levelLT (some (p.length + q.length - 2)) (tenacity M c))
    (d : V) (hqd : q.BaseOnPath (p.length + q.length) d) :
    Blossom M (p.length + q.length) d (q.vertex ⟨q.length - 1, by omega⟩) := by
  classical
  obtain ⟨r, hrc, hr, _, hmin, hlt, hpres⟩ :=
    p.predecessor_blossom_prefix q hp hq hpe hqo hend hinner c hc
  have hrd := (hpres d).1 hqd
  have htodd : (p.length + q.length) % 2 = 1 := by omega
  by_cases hct : tenacity M c = some (p.length + q.length)
  · obtain ⟨a, ha, _⟩ := ih c r.length hmin hlt hct
    have hda : d = a := r.baseOnPath_unique _ d a hrd (ha r hrc hr)
    have hbase : IsBase M c d := ⟨p.length + q.length, hct, hda ▸ ha⟩
    have hmem : Blossom M (p.length + q.length) d c :=
      blossom_of_base_le _ htodd d c hbase (by rw [hct]; exact Nat.le_refl _)
    exact (blossom_strict_nested_of_base_mem (p.length + q.length - 2)
      (p.length + q.length) htodd c d hchigh hmem).1 _ hc
  · have hhigh : levelLT (some (p.length + q.length)) (tenacity M c) := by
      have hge := tenacity_ge_of_above_previous_odd c (p.length + q.length) htodd hchigh
      cases hs : tenacity M c with
      | none => trivial
      | some s =>
        have hts : p.length + q.length ≤ s := by simpa only [hs, levelLE] using hge
        have hne : s ≠ p.length + q.length := by intro h; exact hct (hs.trans (congrArg some h))
        change p.length + q.length < s
        omega
    have hrcbase : r.BaseOnPath (p.length + q.length) c := by
      refine ⟨⟨r.length, by omega⟩, hrc, hhigh, ?_⟩
      intro j hj
      change r.length < j.val at hj
      have := j.isLt
      omega
    have hdc := r.baseOnPath_unique _ d c hrd hrcbase
    rw [hdc]
    exact blossom_mono _ _ htodd (by omega) c _ hc

/-- The lower-predecessor branch supplies an actual current-threshold blossom
member for the short-path minimization argument. No current confinement or
global current-tenacity base existence is assumed. -/
theorem low_predecessor_in_base_blossom (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ p.length + q.length - 2 →
      ∃ b, IsBase M v b)
    (ih : ∀ (v : V) (k : Nat), minlevel M v = some k → k < q.length →
      tenacity M v = some (p.length + q.length) → HasUniqueBase M v (p.length + q.length))
    (s : Nat) (hs : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) = some s)
    (hst : s < p.length + q.length) (d : V) (hqd : q.BaseOnPath (p.length + q.length) d) :
    Blossom M (p.length + q.length) d (q.vertex ⟨q.length - 1, by omega⟩) := by
  have hsodd := tenacity_odd M _ s hs
  obtain ⟨c, hc, hmem⟩ := blossom_cover_of_base_existence (p.length + q.length - 2)
    (by omega) hexists _ s hs (by omega)
  exact p.predecessor_blossom_promote q hp hq hpe hqo hend hinner ih c hmem hc d hqd

end MaximumMatching.AltPath
