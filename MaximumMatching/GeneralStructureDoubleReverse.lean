import MaximumMatching.GeneralStructureFirstHit

namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Two reverse splices through a later suffix hit construct an opposite path
at an absent even boundary. The only shared final matched pair is handled
explicitly, so both reverse splices are simple paths. -/
theorem double_reverse_boundary_bound (p r : AltPath M)
    (hre : r.length % 2 = 0)
    (D : Fin (r.length + 1)) (hDe : D.val % 2 = 0)
    (I O : Nat) (hIp : I + 1 ≤ p.length) (hIo : I % 2 = 1)
    (hIN : r.length - 1 ≤ I) (hNO : r.length < O)
    (hjoin : p.vertex ⟨I, by omega⟩ = r.vertex ⟨r.length - 1, by omega⟩)
    (hlast : p.vertex ⟨I + 1, by omega⟩ = r.last)
    (havoid : ∀ (a : Fin (p.length + 1)) (j : Fin (r.length + 1)),
      D.val ≤ j.val → j.val < r.length - 1 → p.vertex a ≠ r.vertex j)
    (g : FirstHit r p (I + 2))
    (hK : g.qi.val < D.val) (hKo : g.qi.val % 2 = 1) (hHe : g.pi.val % 2 = 0) :
    ∃ t, tenacity M (r.vertex D) = some t ∧ t ≤ p.length + O := by
  have hH : I + 2 ≤ g.pi.val := g.in_suffix
  have hNpos : 0 < r.length := by have := D.isLt; omega
  let r₀ := r.take g.qi.val (by omega)
  have hdis₁ : r₀.ReverseDisjoint p (I + 1) g.pi.val := by
    intro a b hb hbH he
    by_cases hbe : b.val = I + 1
    · have hbi : b = ⟨I + 1, by omega⟩ := Fin.ext hbe
      rw [hbi, hlast] at he
      change r.vertex ⟨a.val, _⟩ = r.vertex ⟨r.length, by omega⟩ at he
      have hai := congrArg Fin.val (r.injective _ _ he)
      have ha := a.isLt
      change a.val < g.qi.val + 1 at ha
      change a.val = r.length at hai
      omega
    · exact g.reverse_disjoint (I + 2) (Nat.le_refl _) a b (by omega) hbH he
  let s := r₀.spliceReverse p (I + 1) g.pi.val (by omega) (by omega)
    g.hit hKo hHe hdis₁
  have hslen : s.length = g.qi.val + (g.pi.val - (I + 1)) := rfl
  have hsodd : s.length % 2 = 1 := by rw [hslen]; omega
  have hslast : s.last = r.last := (spliceReverse_last _ _ _ _ _ _ _ _ _ _).trans hlast
  have hdis₂ : s.ReverseDisjoint r D.val r.length := by
    intro a j hDj hjN he
    change (if h : a.val ≤ r₀.length then r₀.vertex ⟨a.val, by omega⟩
      else p.vertex ⟨g.pi.val - (a.val - r₀.length), by omega⟩) = r.vertex j at he
    split at he
    next ha =>
      change r.vertex ⟨a.val, _⟩ = r.vertex j at he
      have hai := congrArg Fin.val (r.injective _ _ he)
      change a.val = j.val at hai
      change a.val ≤ g.qi.val at ha
      omega
    next ha =>
      have ha' : g.qi.val < a.val := by change ¬a.val ≤ g.qi.val at ha; omega
      have habound := a.isLt
      change a.val < g.qi.val + (g.pi.val - (I + 1)) + 1 at habound
      have hindex : I + 1 ≤ g.pi.val - (a.val - r₀.length) := by
        change I + 1 ≤ g.pi.val - (a.val - g.qi.val)
        omega
      by_cases hjlt : j.val < r.length - 1
      · exact havoid _ j hDj hjlt he
      · have hjeq : j.val = r.length - 1 := by omega
        have hj : j = ⟨r.length - 1, by omega⟩ := Fin.ext hjeq
        rw [hj, ← hjoin] at he
        have hei := congrArg Fin.val (p.injective _ _ he)
        change g.pi.val - (a.val - r₀.length) = I at hei
        omega
  let z := s.spliceReverse r D.val r.length (by omega) (Nat.le_refl _) hslast hsodd hre hdis₂
  have hzlen : z.length = g.qi.val + (g.pi.val - (I + 1)) + (r.length - D.val) := rfl
  have hzlast : z.last = r.vertex D := spliceReverse_last _ _ _ _ _ _ _ _ _ _
  have hzo : z.length % 2 = 1 := by rw [hzlen]; omega
  have hwe : HasPathLength M (D.val % 2) (r.vertex D) D.val := r.prefix_witness D
  have hwo : HasPathLength M ((D.val + 1) % 2) (r.vertex D) z.length :=
    ⟨z, hzlast, rfl, by omega⟩
  obtain ⟨t, ht, hbound⟩ := tenacity_bound_of_opposite_witnesses (r.vertex D) D.val z.length hwe hwo
  refine ⟨t, ht, ?_⟩
  have hplength := g.pi.isLt
  have hDlength := D.isLt
  rw [hzlen] at hbound
  omega

/-- The first-hit and shortestness hypotheses supply the two parity guards
and the shared final matched mate for the double reverse construction. -/
theorem double_reverse_boundary_bound_of_firstHit (p r : AltPath M)
    (hp : p.Shortest) (hpe : p.length % 2 = 0) (hre : r.length % 2 = 0)
    (D : Fin (r.length + 1)) (hDe : D.val % 2 = 0)
    (I O : Nat) (hIp : I + 1 ≤ p.length) (hIo : I % 2 = 1)
    (hIN : r.length - 1 ≤ I) (hNO : r.length < O)
    (hjoin : p.vertex ⟨I, by omega⟩ = r.vertex ⟨r.length - 1, by omega⟩)
    (havoid : ∀ (a : Fin (p.length + 1)) (j : Fin (r.length + 1)),
      D.val ≤ j.val → j.val < r.length - 1 → p.vertex a ≠ r.vertex j)
    (g : FirstHit r p (I + 2)) (hK : g.qi.val < D.val) :
    ∃ t, tenacity M (r.vertex D) = some t ∧ t ≤ p.length + O := by
  have hKo : g.qi.val % 2 = 1 := g.odd hpe (by omega)
  have hHe : g.pi.val % 2 = 0 := by
    by_cases he : g.pi.val % 2 = 0
    · exact he
    · have hHo : g.pi.val % 2 = 1 := by omega
      have hbound := p.no_shorter_disjoint_prefix hp g.pi.val (by omega)
        (r.take g.qi.val (by omega)) g.hit
        (by simp only [take_length]; omega) g.forward_disjoint
      have hg := g.in_suffix
      have hD := D.isLt
      change g.pi.val ≤ g.qi.val at hbound
      omega
  have hNpos : 0 < r.length := by have := D.isLt; omega
  have hlast : p.vertex ⟨I + 1, by omega⟩ = r.last := by
    have hpnext := p.mate_next I (by omega) hIo
    have hrnext := r.mate_next (r.length - 1) (by omega) (by omega)
    rw [hjoin] at hpnext
    have hh := M.mate_unique hpnext hrnext
    simpa only [show r.length - 1 + 1 = r.length by omega, last] using hh
  exact p.double_reverse_boundary_bound r hre D hDe I O hIp hIo hIN hNO hjoin hlast
    havoid g hK hKo hHe

end MaximumMatching.AltPath
