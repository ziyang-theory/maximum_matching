import MaximumMatching.GeneralStructureInduction

namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

theorem edgeTenacity_symmetric (u v : V) : edgeTenacity M u v = edgeTenacity M v u := by
  classical
  by_cases hm : M.mate u = some v
  · have hm' := M.symm hm
    simp only [edgeTenacity, ite_eq_left hm, ite_eq_left hm', matchedEdgeTenacity]
    cases hu : oddlevel M u <;> cases hv : oddlevel M v <;> simp [levelAdd, Nat.add_comm]
  · have hm' : M.mate v ≠ some u := by intro hh; exact hm (M.symm hh)
    simp only [edgeTenacity, ite_eq_right hm, ite_eq_right hm']
    cases hu : evenlevel M u <;> cases hv : evenlevel M v <;> simp [levelAdd, Nat.add_comm]

namespace AltPath

theorem last_edge_tenacity_of_honest_predecessor (p : AltPath M) (hp : p.Shortest)
    (hpos : 0 < p.length) (hpred : p.BFSHonest ⟨p.length - 1, by omega⟩)
    (t : Nat) (hpt : tenacity M p.last = some t) :
    edgeTenacity M (p.vertex ⟨p.length - 1, by omega⟩) p.last = some t := by
  have hnext : p.length - 1 + 1 = p.length := by omega
  by_cases hpe : p.length % 2 = 0
  · have hm := p.mate_next (p.length - 1) (by omega) (by omega)
    have hmlast : M.mate (p.vertex ⟨p.length - 1, by omega⟩) = some p.last := by
      simpa only [hnext, last] using hm
    rw [edgeTenacity, ite_eq_left hmlast]
    exact (matched_tenacity M hmlast).2.symm.trans hpt
  · have hpo : p.length % 2 = 1 := by omega
    have hm : M.mate (p.vertex ⟨p.length - 1, by omega⟩) ≠ some p.last := by
      intro h
      have he := (p.alternating ⟨p.length - 1, by omega⟩).1
        (by simpa only [hnext, last] using h)
      change (p.length - 1) % 2 = 1 at he
      omega
    have hprede : evenlevel M (p.vertex ⟨p.length - 1, by omega⟩) = some (p.length - 1) := by
      simpa only [show (p.length - 1) % 2 = 0 by omega] using
        (p.honest_iff_level ⟨p.length - 1, by omega⟩).1 hpred
    obtain ⟨e, o, he, ho, _, _, hsum⟩ := finite_levels_of_tenacity p.last t hpt
    have hop : oddlevel M p.last = some p.length :=
      (level_eq_some_iff M 1 p.last p.length).2 (by simpa only [Shortest, hpo] using hp)
    have hoL : o = p.length := Option.some.inj (ho.symm.trans hop)
    simp only [edgeTenacity, ite_eq_right hm, hprede, he, levelAdd, Option.map_some]
    exact congrArg some (by omega)

theorem first_entry_edge_tenacity (p : AltPath M) (hp : p.Shortest)
    (hpo : p.length % 2 = 1) (t : Nat) (hpt : tenacity M p.last = some t)
    (D : Fin (p.length + 1)) (hDo : D.val % 2 = 1)
    (hDmem : Blossom M (t - 2) p.last (p.vertex D))
    (htail : (p.reverseOddTail hpo D).Shortest)
    (hprefix : p.BFSHonest ⟨D.val - 1, by omega⟩) :
    edgeTenacity M (p.vertex ⟨D.val - 1, by omega⟩) (p.vertex D) = some t := by
  have htodd := tenacity_odd M p.last t hpt
  have hclow : levelLT (some (t - 2)) (tenacity M p.last) := by
    rw [hpt]
    change t - 2 < t
    omega
  obtain ⟨e, o, hce, hco, _, _, hsum⟩ := finite_levels_of_tenacity p.last t hpt
  have hcop : oddlevel M p.last = some p.length :=
    (level_eq_some_iff M 1 p.last p.length).2 (by simpa only [Shortest, hpo] using hp)
  have hop : o = p.length := Option.some.inj (hco.symm.trans hcop)
  have hcmin : minlevel M p.last = some e :=
    (minlevel_eq_even_of_outer p.last (blossom_outer (t - 2) p.last (p.vertex D) hDmem)).trans hce
  have hde := p.first_entry_evenlevel hpo (t - 2) e hclow hcmin D hDo hDmem htail
  have hze : evenlevel M (p.vertex ⟨D.val - 1, by omega⟩) = some (D.val - 1) := by
    simpa only [show (D.val - 1) % 2 = 0 by omega] using
      (p.honest_iff_level ⟨D.val - 1, by omega⟩).1 hprefix
  have hnm : M.mate (p.vertex ⟨D.val - 1, by omega⟩) ≠ some (p.vertex D) := by
    intro hm
    have hh := (p.alternating ⟨D.val - 1, by omega⟩).1
      (by simpa only [show D.val - 1 + 1 = D.val by omega] using hm)
    change (D.val - 1) % 2 = 1 at hh
    omega
  simp only [edgeTenacity, ite_eq_right hnm, hze, hde, levelAdd, Option.map_some]
  have := D.isLt
  exact congrArg some (by omega)

end AltPath
end MaximumMatching
