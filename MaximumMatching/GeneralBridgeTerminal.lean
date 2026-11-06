import MaximumMatching.GeneralMaxCapPredecessor

/-! The terminal edge of a maximum-level shortest path whose preceding
prefix is shortest. Its exact tenacity determines the shorter induction case. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- An honest terminal edge has the endpoint's tenacity. If it is a bridge,
the preceding path is either below half that tenacity or ends at lower
tenacity; otherwise it is a prop and the prefix is again a maximum-level
path of the same tenacity. -/
theorem honest_terminal_bridge_cases (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length) (hpos : 0 < p.length)
    (hpred : p.BFSHonest ⟨p.length - 1, by omega⟩) :
    edgeTenacity M (p.vertex ⟨p.length - 1, by omega⟩) p.last = some t ∧
      ((Bridge M (p.vertex ⟨p.length - 1, by omega⟩) p.last ∧
        ((∃ s, tenacity M (p.vertex ⟨p.length - 1, by omega⟩) = some s ∧ s < t) ∨
          2 * (p.length - 1) < t)) ∨
       (PropEdge M (p.vertex ⟨p.length - 1, by omega⟩) p.last ∧
        tenacity M (p.vertex ⟨p.length - 1, by omega⟩) = some t ∧
        maxlevel M (p.vertex ⟨p.length - 1, by omega⟩) = some (p.length - 1))) := by
  classical
  let u := p.vertex ⟨p.length - 1, by omega⟩
  have hadj : G.Adj u p.last := by
    have hh := p.adjacent ⟨p.length - 1, by omega⟩
    simpa only [u, last, show p.length - 1 + 1 = p.length by omega] using hh
  have hpar : (M.mate u = some p.last) ↔ (p.length - 1) % 2 = 1 := by
    have hh := p.alternating ⟨p.length - 1, by omega⟩
    simpa only [u, last, show p.length - 1 + 1 = p.length by omega] using hh
  have hulevel : level M ((p.length - 1) % 2) u = some (p.length - 1) :=
    (p.honest_iff_level ⟨p.length - 1, by omega⟩).1 hpred
  have hvlevel := (level_eq_some_iff M (p.length % 2) p.last p.length).2 hp
  obtain ⟨e, o, he, ho, hep, hop, hsum⟩ := finite_levels_of_tenacity p.last t hpt
  have hmaxeq : max e o = p.length := by
    simpa only [maxlevel, he, ho, levelMax, Option.some.injEq] using hmax
  by_cases hpe : p.length % 2 = 0
  · have heq : e = p.length := Option.some.inj (he.symm.trans (by simpa only [hpe] using hvlevel))
    subst e
    have holt : o < p.length := by omega
    have hpo : (p.length - 1) % 2 = 1 := by omega
    have hm : M.mate u = some p.last := hpar.2 hpo
    have huo : oddlevel M u = some (p.length - 1) := by simpa only [hpo] using hulevel
    have hue : evenlevel M u = some (o + 1) := by
      simpa only [ho, Option.map_some] using evenlevel_matched M (M.symm hm)
    have hut : tenacity M u = some t := (matched_tenacity M hm).1.trans hpt
    have hedge : edgeTenacity M u p.last = some t := by
      simp only [edgeTenacity, ite_eq_left hm]
      rw [← (matched_tenacity M hm).2, hpt]
    refine ⟨hedge, ?_⟩
    by_cases hprop : PropEdge M u p.last
    · apply Or.inr
      refine ⟨hprop, hut, ?_⟩
      have hle : o + 1 ≤ p.length - 1 := by
        by_cases hle : o + 1 ≤ p.length - 1
        · exact hle
        · have heq : o = p.length - 1 := by omega
          have hvmin : minlevel M p.last = some (p.length - 1) := by
            simp only [minlevel, he, ho, levelMin]
            rw [Nat.min_eq_right (by omega : o ≤ p.length), heq]
          have humin : minlevel M u = some (p.length - 1) := by
            simp only [minlevel, hue, huo, levelMin, Nat.min_eq_right (by omega : p.length - 1 ≤ o + 1)]
          exact False.elim (not_propEdge_of_minlevel_eq M u p.last (p.length - 1) humin hvmin hprop)
      change maxlevel M u = some (p.length - 1)
      simp only [maxlevel, hue, huo, levelMax, Nat.max_eq_right hle]
    · have hbridge : Bridge M u p.last := ⟨hadj, hprop⟩
      obtain ⟨k, hku, _, _, _, _, _, htk⟩ := matched_bridge_levels hbridge hm t hedge
      have hk : k = p.length - 1 := Option.some.inj (hku.symm.trans huo)
      exact Or.inl ⟨hbridge, Or.inr (by omega)⟩
  · have hpo : p.length % 2 = 1 := by omega
    have hoq : o = p.length := Option.some.inj (ho.symm.trans (by simpa only [hpo] using hvlevel))
    subst o
    have helt : e < p.length := by omega
    have hvouter : Outer M p.last := by simpa only [Outer, he, ho, levelLT] using helt
    have huep : (p.length - 1) % 2 = 0 := by omega
    have hue : evenlevel M u = some (p.length - 1) := by simpa only [huep] using hulevel
    have hm : M.mate u ≠ some p.last := fun hh => by have hh' := hpar.1 hh; omega
    have hms : M.mate p.last ≠ some u := fun hh => hm (M.symm hh)
    have hedge : edgeTenacity M u p.last = some t := by
      simp only [edgeTenacity, ite_eq_right hm, hue, he, levelAdd, Option.map_some]
      exact congrArg some (by omega)
    refine ⟨hedge, ?_⟩
    by_cases hprop : PropEdge M u p.last
    · have hpredvu : Predecessor M p.last u :=
        hprop.resolve_left (not_predecessor_unmatched_outer p.last u hvouter hms)
      obtain ⟨r, hru, hrmin, hrpos, hrv⟩ := hpredvu
      have hreodd : r.length % 2 = 1 := by
        by_cases hre : r.length % 2 = 0
        · have hh := r.even_last_mate hre hrpos
          have hh' : M.mate u = some p.last := by simpa only [hru, hrv] using hh
          exact False.elim (hm hh')
        · omega
      have hrshort := r.shortest_of_minlevel (by rw [hru]; exact hrmin)
      have hro : oddlevel M u = some r.length := by
        have hh := (level_eq_some_iff M (r.length % 2) r.last r.length).2 hrshort
        simpa only [hreodd, hru] using hh
      have hprev := (r.honest_iff_level ⟨r.length - 1, by omega⟩).1
        (r.minlevel_last_predecessor_honest (by rw [hru]; exact hrmin) hrpos)
      have hve : evenlevel M p.last = some (r.length - 1) := by
        simpa only [show (r.length - 1) % 2 = 0 by omega, hrv] using hprev
      have hreq : r.length = e + 1 := by have hh := Option.some.inj (he.symm.trans hve); omega
      have hrle : r.length ≤ p.length - 1 :=
        minlevel_le_path M u r.length hrmin (p.take (p.length - 1) (by omega)) rfl
      apply Or.inr
      refine ⟨hprop, ?_, ?_⟩
      · change tenacity M u = some t
        simp only [tenacity, hue, hro, levelAdd]
        exact congrArg some (by omega)
      · change maxlevel M u = some (p.length - 1)
        simp only [maxlevel, hue, hro, levelMax, Nat.max_eq_left hrle]
    · have hbridge : Bridge M u p.last := ⟨hadj, hprop⟩
      apply Or.inl
      refine ⟨hbridge, ?_⟩
      by_cases huouter : Outer M u
      · have heq := (unmatched_bridge_outer_levels hbridge hm (p.length - 1) e hue he huouter hvouter).1
        exact Or.inr (by omega)
      · have hufinite := minlevel_le_of_level u (p.length - 1) (by simpa only [huep] using hue)
        obtain ⟨k, hk, _⟩ := hufinite
        exact Or.inl ((unmatched_bridge_tenacity hbridge hm t hedge).2 ⟨⟨k, hk⟩, huouter⟩)

end MaximumMatching.AltPath
