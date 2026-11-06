import MaximumMatching.GeneralBaseReroute

/-! First-hit bounds and avoidance for shortest witnesses to members of an
established lower blossom. These facts require actual blossom membership;
no general confinement hypothesis is used. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A first hit of any sufficiently short alternating path on the suffix after
an absent high even vertex has its old-path index at most its new-path
index. An opposite-parity hit would violate the high vertex's tenacity. -/
theorem first_high_suffix_hit_le_of_length_le (p r : AltPath M) (hp : p.Shortest)
    (hpe : p.length % 2 = 0) (i : Fin (p.length + 1)) (hie : i.val % 2 = 0)
    (t : Nat) (hbound : p.length + r.length ≤ t)
    (hhigh : levelLT (some t) (tenacity M (p.vertex i)))
    (habsent : ∀ a, r.vertex a ≠ p.vertex i)
    (h : FirstHit r p (i.val + 1)) :
    h.qi.val % 2 = 1 ∧ h.pi.val % 2 = 1 ∧ h.pi.val ≤ h.qi.val := by
  have hodd := h.odd hpe (by omega)
  by_cases he : h.pi.val % 2 = 0
  · have hki : i.val ≤ h.pi.val := by have := h.in_suffix; omega
    let s := (r.take h.qi.val (by omega)).spliceReverse p i.val h.pi.val hki
      (by omega) h.hit hodd he (h.reverse_disjoint_of_absent_boundary (by omega) habsent)
    have hslen : s.length = h.qi.val + (h.pi.val - i.val) := rfl
    have hsb : s.last = p.vertex i := spliceReverse_last _ _ _ _ _ _ _ _ _ _
    have hwe := p.prefix_witness i
    have hwo : HasPathLength M ((i.val + 1) % 2) (p.vertex i) s.length :=
      ⟨s, hsb, rfl, by rw [hslen]; omega⟩
    obtain ⟨k, hk, hkbound⟩ := tenacity_bound_of_opposite_witnesses
      (p.vertex i) i.val s.length hwe hwo
    have hgt : t < k := by simpa only [hk, levelLT] using hhigh
    have hrbound := h.qi.isLt
    have hpbound := h.pi.isLt
    omega
  · have hpo : h.pi.val % 2 = 1 := by omega
    refine ⟨hodd, hpo, ?_⟩
    exact p.no_shorter_disjoint_prefix hp h.pi.val (by omega)
      (r.take h.qi.val (by omega)) h.hit
      (by simp only [take_length]; omega) h.forward_disjoint

/-- A shortest path to a member of a lower blossom avoids any distinct high
vertex whose minimum level is at least the boundary's minimum level. A high
vertex on the path would have to occur both before the boundary and at its
honest minimum-level index. -/
theorem high_vertex_absent_of_lower_blossom (t : Nat) (c b : V) (C B : Nat)
    (hcmin : minlevel M c = some C) (hbmin : minlevel M b = some B)
    (horder : C ≤ B) (hne : c ≠ b)
    (hchigh : levelLT (some t) (tenacity M c))
    (hbhigh : levelLT (some t) (tenacity M b))
    (r : AltPath M) (hr : r.Shortest) (hrbl : Blossom M t c r.last) :
    ∀ a, r.vertex a ≠ b := by
  obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound t c r.last hrbl
  obtain ⟨k, hk, _, _, hkmin, _⟩ := blossom_on_shortest t c r.last hrbl r rfl hr
  have hkC : k.val = C := Option.some.inj (hkmin.symm.trans hcmin)
  obtain ⟨j, hj, _, hjlast⟩ := blossom_baseOnPath t c r.last hrbl hchigh r rfl hr
  have hjk : j = k := r.injective j k (hj.trans hk.symm)
  subst j
  intro a ha
  have hgreater : levelLT (tenacity M r.last) (tenacity M (r.vertex a)) := by
    rw [hs, ha]
    cases hb : tenacity M b with
    | none => trivial
    | some z =>
      have hz : t < z := by simpa only [hb, levelLT] using hbhigh
      change s < z
      omega
  have hamin := (r.limited_bfs_honesty hr a (levelLT_le hgreater)).2 hgreater
  rw [ha] at hamin
  have haB : a.val = B := Option.some.inj (hamin.symm.trans hbmin)
  by_cases hka : k.val < a.val
  · exact hjlast a hka (ha.symm ▸ hbhigh)
  · have hak : a = k := Fin.ext (by change a.val = k.val; omega)
    exact hne (hk.symm.trans ((congrArg r.vertex hak).symm.trans ha))

end MaximumMatching.AltPath
