import MaximumMatching.GeneralLongLocalization

/-! Actual reverse predecessor witnesses on the descending half of a
maximum-level path. The path segment is preserved vertex by vertex; its
fresh minimum-level prefix is constructed using the established avoidance
theorem. No graph-compression or support conclusion is assumed. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Reverse the actual odd-length stretch between two after-midpoint high
vertices and prepend a minimum-level path to its right endpoint. The result
attains the left endpoint's minimum level and retains every original vertex
at the complementary index `t - K`. -/
theorem reverse_stretch_minlevel_witness (p : AltPath M) (t : Nat) (ht : t % 2 = 1)
    (A J : Fin (p.length + 1)) (hAJ : A.val < J.val)
    (hAe : A.val % 2 = 0) (hJo : J.val % 2 = 1)
    (hJt : J.val ≤ t) (hhalf : t < 2 * A.val)
    (hAmin : minlevel M (p.vertex A) = some (t - A.val))
    (hJmin : minlevel M (p.vertex J) = some (t - J.val))
    (hJten : tenacity M (p.vertex J) = some t) :
    ∃ z : AltPath M, z.length = t - A.val ∧ z.last = p.vertex A ∧
      minlevel M z.last = some z.length ∧
      ∀ K : Fin (p.length + 1), A.val ≤ K.val → K.val ≤ J.val →
        ∃ L : Fin (z.length + 1), L.val = t - K.val ∧ z.vertex L = p.vertex K := by
  have hJlevel : evenlevel M (p.vertex J) = some (t - J.val) := by
    have hh := level_of_minlevel (p.vertex J) (t - J.val) hJmin
    simpa only [show (t - J.val) % 2 = 0 by omega] using hh
  obtain ⟨q, hqJ, hqlen, _⟩ := ((level_eq_some_iff M 0 (p.vertex J) (t - J.val)).1 hJlevel).1
  let a := (p.take J.val (by omega)).segment A.val (by change A.val ≤ J.val; omega) hAe
  have hao : a.length % 2 = 1 := by change (J.val - A.val) % 2 = 1; omega
  let s := a.reverse hao
  have hsn : s.length = J.val - A.val := rfl
  have hsf : s.first = p.vertex J :=
    (a.reverse_first hao).trans ((p.take J.val (by omega)).segment_last A.val (by change A.val ≤ J.val; omega) hAe)
  have hsl : s.last = p.vertex A := a.reverse_last hao
  have hlen : q.length + s.length = t - A.val := by omega
  have htarget : IsShortest M (s.length % 2) s.last (q.length + s.length) := by
    have hh := (level_eq_some_iff M ((t - A.val) % 2) (p.vertex A) (t - A.val)).1
      (level_of_minlevel (p.vertex A) (t - A.val) hAmin)
    simpa only [hsl, hlen, show s.length % 2 = (t - A.val) % 2 by omega] using hh
  have hjoin : q.last = s.first := hqJ.trans hsf.symm
  have hqlevel : evenlevel M q.last = some q.length := by rw [hqJ, hqlen]; exact hJlevel
  have hqhigh : levelLT (some (t - 1)) (tenacity M q.last) := by
    rw [hqJ, hJten]
    change t - 1 < t
    omega
  have hdis := q.segment_avoids_prefix s hjoin htarget (t - 1) hqlevel hqhigh (by omega)
  have hqe : q.length % 2 = 0 := by omega
  let z := q.appendSegment s hqe hjoin hdis
  have hzn : z.length = t - A.val := hlen
  have hzl : z.last = p.vertex A := (q.appendSegment_last s hqe hjoin hdis).trans hsl
  refine ⟨z, hzn, hzl, by rw [hzl, hzn]; exact hAmin, ?_⟩
  intro K hAK hKJ
  let L : Fin (z.length + 1) := ⟨t - K.val, by rw [hzn]; omega⟩
  refine ⟨L, rfl, ?_⟩
  by_cases hKJe : K.val = J.val
  · have hKJ' : K = J := Fin.ext hKJe
    change (if h : t - K.val ≤ q.length then q.vertex ⟨t - K.val, _⟩
      else s.vertex ⟨t - K.val - q.length, _⟩) = p.vertex K
    rw [dite_eq_left (by omega : t - K.val ≤ q.length)]
    have hL : (⟨t - K.val, by omega⟩ : Fin (q.length + 1)) = ⟨q.length, by omega⟩ :=
      Fin.ext (by change t - K.val = q.length; omega)
    rw [hL, hKJ']
    exact hqJ
  · have hKJlt : K.val < J.val := by omega
    change (if h : t - K.val ≤ q.length then q.vertex ⟨t - K.val, _⟩
      else s.vertex ⟨t - K.val - q.length, _⟩) = p.vertex K
    rw [dite_eq_right (by omega : ¬t - K.val ≤ q.length)]
    change p.vertex ⟨A.val + (J.val - A.val - (t - K.val - q.length)), _⟩ = p.vertex K
    congr 1
    apply Fin.ext
    change A.val + (J.val - A.val - (t - K.val - q.length)) = K.val
    omega

/-- The first edge of the original stretch is a genuine predecessor when
traversed backward. Its witness is the constructed minimum-level path. -/
theorem late_reverse_predecessor (p : AltPath M) (t : Nat) (ht : t % 2 = 1)
    (A J : Fin (p.length + 1)) (hAJ : A.val < J.val)
    (hAe : A.val % 2 = 0) (hJo : J.val % 2 = 1)
    (hJt : J.val ≤ t) (hhalf : t < 2 * A.val)
    (hAmin : minlevel M (p.vertex A) = some (t - A.val))
    (hJmin : minlevel M (p.vertex J) = some (t - J.val))
    (hJten : tenacity M (p.vertex J) = some t) :
    Predecessor M (p.vertex ⟨A.val + 1, by have := J.isLt; omega⟩) (p.vertex A) := by
  obtain ⟨z, hzn, hzl, hzm, hvertices⟩ := p.reverse_stretch_minlevel_witness t ht A J hAJ
    hAe hJo hJt hhalf hAmin hJmin hJten
  have hzpos : 0 < z.length := by omega
  obtain ⟨L, hL, hLv⟩ := hvertices ⟨A.val + 1, by have := J.isLt; omega⟩
    (by change A.val ≤ A.val + 1; omega) (by change A.val + 1 ≤ J.val; omega)
  refine ⟨z, hzl, by rw [← hzl]; exact hzm, hzpos, ?_⟩
  have he : (⟨z.length - 1, by omega⟩ : Fin (z.length + 1)) = L := by
    apply Fin.ext
    change z.length - 1 = L.val
    dsimp only at hL
    omega
  rw [he]
  exact hLv

end MaximumMatching.AltPath
