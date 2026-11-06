import MaximumMatching.BridgeClassification
import MaximumMatching.BlossomCover
import MaximumMatching.GeneralWeightedEdges

/-! A dishonest low predecessor of an outer maxlevel endpoint is inside the
endpoint's lower blossom. The prop/bridge distinction is derived from actual
levels, and only the low vertex's already-established base is used. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- An unmatched edge directed into an outer vertex cannot be a prop. -/
theorem not_predecessor_unmatched_outer (c u : V)
    (hc : Outer M c) (hm : M.mate c ≠ some u) : ¬ Predecessor M u c := by
  rintro ⟨p, hp, hpmin, hpos, hu⟩
  have hce := (minlevel_eq_even_of_outer c hc).symm.trans hpmin
  have hpe := level_parity M 0 c p.length hce
  have hlast : p.vertex ⟨p.length, by omega⟩ = c := hp
  have hprev : M.mate c = some u := by
    have hh := p.mate_previous p.length (Nat.le_refl _) hpos hpe
    simpa only [hlast, hu] using hh
  exact hm hprev

/-- If an unmatched edge's finite tenacity is below an outer endpoint's
vertex tenacity, it is a prop directed away from that endpoint. -/
theorem predecessor_of_unmatched_outer_edge_below (c u : V)
    (hc : Outer M c) (ha : G.Adj c u) (hm : M.mate c ≠ some u)
    (t e f : Nat) (hct : tenacity M c = some t)
    (hce : evenlevel M c = some e) (hue : evenlevel M u = some f)
    (hsmall : e + f + 1 < t) : Predecessor M c u := by
  classical
  have hedge : edgeTenacity M c u = some (e + f + 1) := by
    simp only [edgeTenacity, ite_eq_right hm, hce, hue, levelAdd, Option.map_some]
  have hprop : PropEdge M c u := by
    by_cases hp : PropEdge M c u
    · exact hp
    · obtain ⟨s, hs, hbound⟩ := (unmatched_bridge_tenacity ⟨ha, hp⟩ hm _ hedge).1 hc
      have hst := Option.some.inj (hs.symm.trans hct)
      omega
  exact hprop.resolve_right (not_predecessor_unmatched_outer c u hc hm)

/-- An actual common base agrees with a higher-tenacity immediate predecessor
on a minimum-level witness. -/
theorem isBase_of_high_predecessor (c u : V) (hpred : Predecessor M c u)
    (s : Nat) (hut : tenacity M u = some s)
    (hc : levelLT (some s) (tenacity M c)) (hexists : ∃ b, IsBase M u b) :
    IsBase M u c := by
  obtain ⟨b, hb⟩ := hexists
  obtain ⟨p, hp, hpmin, hpos, hpc⟩ := hpred
  have hpshort := p.shortest_of_minlevel (by rw [hp]; exact hpmin)
  have hpb : p.BaseOnPath s b := by
    obtain ⟨r, hur, hcommon⟩ := hb
    have hrs := Option.some.inj (hur.symm.trans hut)
    subst r
    exact hcommon p hp hpshort
  have hpcbase : p.BaseOnPath s c := by
    refine ⟨⟨p.length - 1, by omega⟩, hpc, hc, ?_⟩
    intro j hj
    have hje : j = ⟨p.length, by omega⟩ := Fin.ext (by
      change j.val = p.length
      change p.length - 1 < j.val at hj
      have := j.isLt
      omega)
    rw [hje]
    change ¬levelLT (some s) (tenacity M p.last)
    rw [hp, hut]
    exact Nat.lt_irrefl _
  exact (p.baseOnPath_unique s b c hpb hpcbase) ▸ hb

/-- The low endpoint of a sufficiently small edge has the outer endpoint as
its actual base, using only base existence at the low endpoint. -/
theorem base_of_unmatched_outer_edge_below (c u : V)
    (hc : Outer M c) (ha : G.Adj c u) (hm : M.mate c ≠ some u)
    (t e f s : Nat) (hct : tenacity M c = some t) (hut : tenacity M u = some s)
    (hst : s < t) (hce : evenlevel M c = some e) (hue : evenlevel M u = some f)
    (hsmall : e + f + 1 < t) (hexists : ∃ b, IsBase M u b) : IsBase M u c :=
  isBase_of_high_predecessor c u
    (predecessor_of_unmatched_outer_edge_below c u hc ha hm t e f hct hce hue hsmall)
    s hut (by rw [hct]; exact hst) hexists

namespace AltPath

/-- A dishonest last predecessor can occur only on an outer endpoint's odd
maxlevel path. Even paths trim across a matched edge; an inner endpoint's odd
path is already a minimum-level path and has an honest predecessor. -/
theorem dishonest_last_predecessor_outer (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (hpt : tenacity M p.last = some t) (hpos : 0 < p.length)
    (hdish : ¬p.BFSHonest ⟨p.length - 1, by omega⟩) :
    p.length % 2 = 1 ∧ Outer M p.last := by
  have hpo : p.length % 2 = 1 := by
    by_cases he : p.length % 2 = 0
    · have hm := p.even_last_mate he hpos
      have hh := (matched_shortest_iff M (M.symm hm) (p.length - 1)).mp (by
        rw [show p.length - 1 + 1 = p.length by omega]
        simpa only [Shortest, he] using hp)
      apply False.elim
      apply hdish
      change IsShortest M ((p.length - 1) % 2)
        (p.vertex ⟨p.length - 1, by omega⟩) (p.length - 1)
      simpa only [show (p.length - 1) % 2 = 1 by omega] using hh
    · omega
  refine ⟨hpo, ?_⟩
  apply Classical.byContradiction
  intro hn
  obtain ⟨e, o, he, ho, _, _, _⟩ := finite_levels_of_tenacity p.last t hpt
  have hpodd : oddlevel M p.last = some p.length :=
    (level_eq_some_iff M 1 p.last p.length).mpr (by simpa only [Shortest, hpo] using hp)
  have hop : o = p.length := Option.some.inj (ho.symm.trans hpodd)
  have hoe : o ≤ e := by
    have hnot : ¬e < o := by simpa only [Outer, he, ho, levelLT] using hn
    omega
  have hmin : minlevel M p.last = some p.length := by
    simp only [minlevel, he, ho, levelMin]
    rw [Nat.min_eq_right hoe, hop]
  exact hdish (p.minlevel_last_predecessor_honest hmin hpos)


/-- At an outer endpoint's odd maxlevel path, a dishonest low predecessor is
inside the lower blossom rooted at that endpoint. This closes the terminal
prop case of a low stretch without assuming its boundary in advance. -/
theorem dishonest_outer_predecessor_base (p : AltPath M) (hp : p.Shortest)
    (hpo : p.length % 2 = 1) (hc : Outer M p.last)
    (t s : Nat) (hct : tenacity M p.last = some t)
    (hut : tenacity M (p.vertex ⟨p.length - 1, by omega⟩) = some s)
    (hst : s < t)
    (hexists : ∃ b, IsBase M (p.vertex ⟨p.length - 1, by omega⟩) b)
    (hdish : ¬p.BFSHonest ⟨p.length - 1, by omega⟩) :
    IsBase M (p.vertex ⟨p.length - 1, by omega⟩) p.last ∧
      Blossom M (t - 2) p.last (p.vertex ⟨p.length - 1, by omega⟩) := by
  let u := p.vertex ⟨p.length - 1, by omega⟩
  have hpredpar : (p.length - 1) % 2 = 0 := by omega
  obtain ⟨e, o, hce, hco, _, _, hsum⟩ := finite_levels_of_tenacity p.last t hct
  have hcop : oddlevel M p.last = some p.length :=
    (level_eq_some_iff M 1 p.last p.length).2 (by simpa only [Shortest, hpo] using hp)
  have hop : o = p.length := Option.some.inj (hco.symm.trans hcop)
  obtain ⟨f, huf, hfbound⟩ := p.prefix_level_bound ⟨p.length - 1, by omega⟩
  have hue : evenlevel M u = some f := by simpa only [hpredpar] using huf
  have hflt : f < p.length - 1 := by
    by_cases he : f = p.length - 1
    · exact False.elim (hdish ((p.honest_iff_level _).2 (by simpa only [he] using huf)))
    · change f ≤ p.length - 1 at hfbound
      omega
  have ha : G.Adj p.last u := by
    have hh := G.symm (p.adjacent ⟨p.length - 1, by omega⟩)
    simpa only [show p.length - 1 + 1 = p.length by omega, last, u] using hh
  have hm : M.mate p.last ≠ some u := by
    intro hh
    have he := (p.alternating ⟨p.length - 1, by omega⟩).1
      (by simpa only [show p.length - 1 + 1 = p.length by omega, last, u] using M.symm hh)
    change (p.length - 1) % 2 = 1 at he
    omega
  have hb : IsBase M u p.last := base_of_unmatched_outer_edge_below p.last u hc ha hm
    t e f s hct hut hst hce hue (by omega) hexists
  refine ⟨hb, blossom_of_base_le (t - 2) ?_ p.last u hb ?_⟩
  · have htodd := tenacity_odd M p.last t hct
    have hthree := hb.tenacity_ge_three s hut
    omega
  · have hsodd := tenacity_odd M u s hut
    have htodd := tenacity_odd M p.last t hct
    rw [hut]
    change s ≤ t - 2
    omega

end AltPath

end MaximumMatching
