import MaximumMatching.GeneralBlossomFirstEntry
import MaximumMatching.GeneralBlossomEdgeClosure

/-! The prefix just before a first lower-blossom entry is honest. A shorter
even prefix would create an edge below the lower cutoff between distinct
boundary blossoms, contradicted by the proved small-edge closure. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Once the actual reversed first-entry tail is shortest, its preceding
prefix is shortest too. No honesty or classification is supplied for that
prefix; the low case follows from the small-edge cut closure theorem. -/
theorem first_entry_prefix_honest (p : AltPath M) (hp : p.Shortest)
    (hpo : p.length % 2 = 1) (t : Nat) (hpt : tenacity M p.last = some t)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w)
    (D : Fin (p.length + 1)) (hDo : D.val % 2 = 1)
    (hDmem : Blossom M (t - 2) p.last (p.vertex D))
    (hfirst : ∀ a : Fin (p.length + 1), a.val < D.val → ¬Blossom M (t - 2) p.last (p.vertex a))
    (htail : (p.reverseOddTail hpo D).Shortest) :
    p.BFSHonest ⟨D.val - 1, by omega⟩ := by
  let Z : Fin (p.length + 1) := ⟨D.val - 1, by omega⟩
  have hZe : Z.val % 2 = 0 := by change (D.val - 1) % 2 = 0; omega
  by_cases hhigh : levelLE (some t) (tenacity M (p.vertex Z))
  · exact (p.limited_bfs_honesty hp Z (by rw [hpt]; exact hhigh)).1
  · have hzt : ∃ s, tenacity M (p.vertex Z) = some s ∧ s < t := by
      cases hs : tenacity M (p.vertex Z) with
      | none => exact False.elim (hhigh (by rw [hs]; trivial))
      | some s =>
        refine ⟨s, rfl, ?_⟩
        have hn : ¬t ≤ s := by simpa only [hs, levelLE] using hhigh
        omega
    obtain ⟨s, hzs, hst⟩ := hzt
    have htodd := tenacity_odd M p.last t hpt
    have hsodd := tenacity_odd M (p.vertex Z) s hzs
    have hslow : s ≤ t - 2 := by omega
    have htlow : (t - 2) % 2 = 1 := by
      by_cases hthree : 3 ≤ t
      · omega
      · have htone : t = 1 := by omega
        rw [htone] at hDmem
        exact False.elim hDmem
    have hchigh : levelLT (some (t - 2)) (tenacity M p.last) := by
      rw [hpt]
      change t - 2 < t
      omega
    obtain ⟨b, hb, hbz⟩ := blossom_cover_of_base_existence (t - 2) htlow hexists
      (p.vertex Z) s hzs hslow
    obtain ⟨e, o, hce, hco, _, _, hsum⟩ := finite_levels_of_tenacity p.last t hpt
    have hcop : oddlevel M p.last = some p.length :=
      (level_eq_some_iff M 1 p.last p.length).2 (by simpa only [Shortest, hpo] using hp)
    have hop : o = p.length := Option.some.inj (hco.symm.trans hcop)
    have hcmin : minlevel M p.last = some e :=
      (minlevel_eq_even_of_outer p.last (blossom_outer (t - 2) p.last (p.vertex D) hDmem)).trans hce
    have hde := p.first_entry_evenlevel hpo (t - 2) e hchigh hcmin D hDo hDmem htail
    have hden : e + (p.length - D.val) = t - D.val := by have := D.isLt; omega
    rw [hden] at hde
    obtain ⟨f, hzf, hfb⟩ := p.prefix_level_bound Z
    have hze : evenlevel M (p.vertex Z) = some f := by simpa only [hZe] using hzf
    by_cases hfe : f = D.val - 1
    · exact (p.honest_iff_level Z).2 (by simpa only [hfe, Z] using hzf)
    · have hflt : f < D.val - 1 := by change f ≤ D.val - 1 at hfb; omega
      have hadj : G.Adj (p.vertex Z) (p.vertex D) := by
        have hh := p.adjacent ⟨D.val - 1, by omega⟩
        simpa only [show D.val - 1 + 1 = D.val by omega, Z] using hh
      have hunm : M.mate (p.vertex Z) ≠ some (p.vertex D) := by
        intro hm
        have hodd := (p.alternating ⟨D.val - 1, by omega⟩).1
          (by simpa only [show D.val - 1 + 1 = D.val by omega, Z] using hm)
        change (D.val - 1) % 2 = 1 at hodd
        omega
      have hbceq := blossom_unmatched_edge_boundary_eq (t - 2) b p.last (p.vertex Z) (p.vertex D)
        hbz hDmem hb hchigh hconf hadj hunm f (t - D.val) hze hde (by
          have := D.isLt
          have hfp := level_parity M 0 (p.vertex Z) f hze
          omega)
      rw [hbceq] at hbz
      exact False.elim (hfirst Z (by change D.val - 1 < D.val; omega) hbz)

end MaximumMatching.AltPath
