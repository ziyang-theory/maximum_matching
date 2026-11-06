import MaximumMatching.GeneralShortConfinement

/-! Original low vertices on an after-midpoint stretch are localized by
reversing that actual stretch and joining an honest minimum-level prefix. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Reverse a low stretch wholly after the tenacity midpoint. Its original
interior belongs to the lower blossom of its right high endpoint. Actual
endpoint minimum levels justify the fresh join; no avoidance is assumed. -/
theorem late_low_stretch_mem (p : AltPath M) (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w)
    (A K J : Fin (p.length + 1)) (hAK : A.val < K.val) (hKJ : K.val < J.val)
    (hAe : A.val % 2 = 0) (hJo : J.val % 2 = 1) (hJt : J.val ≤ t) (hhalf : t < 2 * A.val)
    (hAmin : minlevel M (p.vertex A) = some (t - A.val))
    (hJmin : minlevel M (p.vertex J) = some (t - J.val))
    (hJten : tenacity M (p.vertex J) = some t)
    (hlow : ∀ k : Fin (p.length + 1), A.val < k.val → k.val < J.val →
      levelLE (tenacity M (p.vertex k)) (some (t - 2))) :
    Blossom M (t - 2) (p.vertex J) (p.vertex K) := by
  have htlow : (t - 2) % 2 = 1 := by omega
  have hJlevel : evenlevel M (p.vertex J) = some (t - J.val) := by
    have hh := level_of_minlevel (p.vertex J) (t - J.val) hJmin
    simpa only [show (t - J.val) % 2 = 0 by omega] using hh
  obtain ⟨q, hqJ, hqlen, hqe⟩ := ((level_eq_some_iff M 0 (p.vertex J) (t - J.val)).mp hJlevel).1
  have hqshort : q.Shortest := by
    have hs := (level_eq_some_iff M 0 (p.vertex J) (t - J.val)).mp hJlevel
    simpa only [Shortest, hqlen, hqe, hqJ] using hs
  let a := (p.take J.val (by omega)).segment A.val (by change A.val ≤ J.val; omega) hAe
  have hao : a.length % 2 = 1 := by change (J.val - A.val) % 2 = 1; omega
  let s := a.reverse hao
  have hsn : s.length = J.val - A.val := rfl
  have hsf : s.first = p.vertex J :=
    (a.reverse_first hao).trans ((p.take J.val (by omega)).segment_last A.val (by change A.val ≤ J.val; omega) hAe)
  have hsl : s.last = p.vertex A := a.reverse_last hao
  have hlen : q.length + s.length = t - A.val := by omega
  have htarget : IsShortest M (s.length % 2) s.last (q.length + s.length) := by
    have hh := (level_eq_some_iff M ((t - A.val) % 2) (p.vertex A) (t - A.val)).mp
      (level_of_minlevel (p.vertex A) (t - A.val) hAmin)
    simpa only [hsl, hlen, show s.length % 2 = (t - A.val) % 2 by omega] using hh
  have hjoin : q.last = s.first := hqJ.trans hsf.symm
  have hqlevel : evenlevel M q.last = some q.length := by rw [hqJ, hqlen]; exact hJlevel
  have hqhigh : levelLT (some (t - 1)) (tenacity M q.last) := by
    rw [hqJ, hJten]
    change t - 1 < t
    omega
  have hdis := q.segment_avoids_prefix s hjoin htarget (t - 1) hqlevel hqhigh (by omega)
  have hqpar : q.length % 2 = 0 := by omega
  let z := q.appendSegment s hqpar hjoin hdis
  have hzn : z.length = t - A.val := hlen
  have hzlast : z.last = p.vertex A := (q.appendSegment_last s hqpar hjoin hdis).trans hsl
  have hzv (u : Fin (z.length + 1)) (hu : q.length < u.val) :
      z.vertex u = p.vertex ⟨J.val - (u.val - q.length), by have := J.isLt; omega⟩ := by
    change (if h : u.val ≤ q.length then q.vertex ⟨u.val, _⟩
      else s.vertex ⟨u.val - q.length, _⟩) = _
    rw [dite_eq_right (by omega : ¬u.val ≤ q.length)]
    change p.vertex ⟨A.val + (J.val - A.val - (u.val - q.length)), _⟩ = _
    congr 1
    apply Fin.ext
    have hub := u.isLt
    change u.val < q.length + (J.val - A.val) + 1 at hub
    change A.val + (J.val - A.val - (u.val - q.length)) = J.val - (u.val - q.length)
    omega
  let I : Fin (z.length + 1) := ⟨q.length, by change q.length < q.length + s.length + 1; omega⟩
  let L : Fin (z.length + 1) := ⟨z.length, by omega⟩
  let U : Fin (z.length + 1) := ⟨q.length + (J.val - K.val), by rw [hzn]; omega⟩
  have hzI : z.vertex I = p.vertex J := by
    change (if h : q.length ≤ q.length then q.vertex ⟨q.length, _⟩ else _) = _
    rw [dite_eq_left (Nat.le_refl _)]
    exact hqJ
  have hzU : z.vertex U = p.vertex K := by
    have hh := hzv U (by change q.length < q.length + (J.val - K.val); omega)
    apply hh.trans
    congr 1
    apply Fin.ext
    change J.val - (q.length + (J.val - K.val) - q.length) = K.val
    omega
  have hm := z.low_stretch_mem (t - 2) htlow hexists hconf I L U
    (by change q.length < q.length + (J.val - K.val); omega)
    (by change q.length + (J.val - K.val) < z.length; rw [hzn]; omega)
    (by change minlevel M z.last = some z.length; rw [hzlast, hzn]; exact hAmin)
    (by rw [hzI, hJten]; change t - 2 < t; omega) (by
      intro u hIu huL
      have hu : q.length < u.val := hIu
      have hult : u.val < z.length := huL
      rw [hzv u hu]
      apply hlow
      · change A.val < J.val - (u.val - q.length)
        have hult' : u.val < t - A.val := by omega
        omega
      · change J.val - (u.val - q.length) < J.val
        omega)
  simpa only [hzI, hzU] using hm

end MaximumMatching.AltPath
