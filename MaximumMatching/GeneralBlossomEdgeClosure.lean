import MaximumMatching.GeneralStructureFirstHit

/-! An unmatched edge with small even-level sum cannot cross two distinct
established blossoms. The proof uses actual shortest paths, confinement, and
two opposite boundary-index inequalities. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

namespace AltPath
private theorem blossom_edge_boundary_lt (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqe : q.length % 2 = 0)
    (t : Nat) (b c : V) (hpb : Blossom M t b p.last) (hqc : Blossom M t c q.last)
    (hbhigh : levelLT (some t) (tenacity M b)) (hchigh : levelLT (some t) (tenacity M c))
    (hne : b ≠ c)
    (hconf : ∀ (a v : V), Blossom M t a v → levelLT (some t) (tenacity M a) →
      ∀ r : AltSegment M, r.Shortest → r.first = a → r.last = v →
        ∀ w, r.Contains w → w = a ∨ Blossom M t a w)
    (hadj : G.Adj p.last q.last) (hunmatched : M.mate p.last ≠ some q.last)
    (hbudget : p.length + q.length + 1 ≤ t)
    (B : Fin (p.length + 1)) (hB : p.vertex B = b)
    (C : Fin (q.length + 1)) (hC : q.vertex C = c) : C.val < B.val := by
  classical
  obtain ⟨C₀, hC₀, hCe₀, hClt₀, hCmin₀, _⟩ := blossom_on_shortest t c q.last hqc q rfl hq
  have hCC : C₀ = C := q.injective _ _ (hC₀.trans hC.symm)
  subst C₀
  have hpbase := blossom_baseOnPath t b p.last hpb hbhigh p rfl hp
  obtain ⟨B₀, hB₀, _, hBlast⟩ := hpbase
  have hBB : B₀ = B := p.injective _ _ (hB₀.trans hB.symm)
  subst B₀
  by_cases hon : ∃ a, p.vertex a = c
  · obtain ⟨a, ha⟩ := hon
    obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound t b p.last hpb
    have hstrict : levelLT (tenacity M p.last) (tenacity M (p.vertex a)) := by
      rw [hs, ha]
      cases hc : tenacity M c with
      | none => trivial
      | some k =>
        have htk : t < k := by simpa only [hc, levelLT] using hchigh
        change s < k
        omega
    have hamin := (p.limited_bfs_honesty hp a (levelLT_le hstrict)).2 hstrict
    rw [ha] at hamin
    have haC : a.val = C.val := Option.some.inj (hamin.symm.trans hCmin₀)
    have hBa : ¬B.val < a.val := by
      intro hlt
      exact hBlast a hlt (by rw [ha]; exact hchigh)
    have hneidx : a.val ≠ B.val := by
      intro he
      have he' : a = B := Fin.ext he
      exact hne (hB.symm.trans ((congrArg p.vertex he').symm.trans ha))
    omega
  · have habsent : ∀ a, p.vertex a ≠ c := by intro a ha; exact hon ⟨a, ha⟩
    by_cases hinter : ∃ (a : Fin (p.length + 1)) (j : Fin (q.length + 1)),
        C.val + 1 ≤ j.val ∧ p.vertex a = q.vertex j
    · obtain ⟨h⟩ := firstHit_exists p q (C.val + 1) hinter
      have hhigh : levelLT (some t) (tenacity M (q.vertex C)) := by rw [hC]; exact hchigh
      have hhit := q.first_high_suffix_hit_le_of_length_le p hq hqe C hCe₀ t
        (by omega) hhigh (by intro a; rw [hC]; exact habsent a) h
      have hwc := q.blossom_suffix_mem t c q.last hqc hchigh hconf rfl hq C h.pi hC
        (by have := h.in_suffix; omega)
      have hIB : h.qi.val < B.val := by
        by_cases he : h.qi.val = B.val
        · have he' : h.qi = B := Fin.ext he
          have hw : q.vertex h.pi = b := h.hit.symm.trans ((congrArg p.vertex he').trans hB)
          obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound t c (q.vertex h.pi) hwc
          rw [hw] at hs
          have hts : t < s := by simpa only [hs, levelLT] using hbhigh
          omega
        · by_cases hlt : B.val < h.qi.val
          · have hwb := p.blossom_suffix_mem t b p.last hpb hbhigh hconf rfl hp B h.qi hB hlt
            rw [h.hit] at hwb
            exact False.elim (blossoms_disjoint_same_tenacity t b c hbhigh hchigh hne
              (q.vertex h.pi) ⟨hwb, hwc⟩)
          · omega
      have := h.in_suffix
      omega
    · have havoid : ∀ (a : Fin (p.length + 1)) (j : Fin (q.length + 1)),
          C.val ≤ j.val → p.vertex a ≠ q.vertex j := by
        intro a j hCj he
        by_cases hj : C.val < j.val
        · exact hinter ⟨a, j, by omega, he⟩
        · have he' : j = C := Fin.ext (by omega)
          exact habsent a (he.trans ((congrArg q.vertex he').trans hC))
      have hfresh : ∀ a, p.vertex a ≠ q.last := by
        intro a ha
        exact havoid a ⟨q.length, by omega⟩ (by change C.val ≤ q.length; omega) ha
      have hpar : (M.mate p.last = some q.last) ↔ p.length % 2 = 1 := by
        constructor
        · intro h; exact False.elim (hunmatched h)
        · intro h; omega
      let a := p.append q.last hfresh hadj hpar
      have hao : a.length % 2 = 1 := by change (p.length + 1) % 2 = 1; omega
      have hdis : a.ReverseDisjoint q C.val q.length := by
        intro i j hCj hj hhit
        change (if h : i.val ≤ p.length then p.vertex ⟨i.val, _⟩ else q.last) = q.vertex j at hhit
        split at hhit
        · exact havoid _ j hCj hhit
        · have he := congrArg Fin.val (q.injective ⟨q.length, by omega⟩ j hhit)
          change q.length = j.val at he
          omega
      let z := a.spliceReverse q C.val q.length (by omega) (Nat.le_refl _) (append_last _ _ _ _ _)
        hao hqe hdis
      have hzlen : z.length = p.length + 1 + (q.length - C.val) := rfl
      have hzlast : z.last = c := (spliceReverse_last _ _ _ _ _ _ _ _ _ _).trans hC
      have hw₀ : HasPathLength M (C.val % 2) c C.val := by simpa only [hC] using q.prefix_witness C
      have hw₁ : HasPathLength M ((C.val + 1) % 2) c z.length :=
        ⟨z, hzlast, rfl, by rw [hzlen]; omega⟩
      obtain ⟨s, hs, hsb⟩ := tenacity_bound_of_opposite_witnesses c C.val z.length hw₀ hw₁
      have hts : t < s := by simpa only [hs, levelLT] using hchigh
      omega

end AltPath

/-- Unmatched edges whose even-level sum is at most the cutoff have both
endpoints in the same established blossom, assuming confinement at that cutoff. -/
theorem blossom_unmatched_edge_boundary_eq (t : Nat) (b c u v : V)
    (hu : Blossom M t b u) (hv : Blossom M t c v)
    (hb : levelLT (some t) (tenacity M b)) (hc : levelLT (some t) (tenacity M c))
    (hconf : ∀ (a w : V), Blossom M t a w → levelLT (some t) (tenacity M a) →
      ∀ r : AltSegment M, r.Shortest → r.first = a → r.last = w →
        ∀ x, r.Contains x → x = a ∨ Blossom M t a x)
    (hadj : G.Adj u v) (hunmatched : M.mate u ≠ some v)
    (e f : Nat) (he : evenlevel M u = some e) (hf : evenlevel M v = some f)
    (hbudget : e + f + 1 ≤ t) : b = c := by
  apply Classical.byContradiction
  intro hne
  obtain ⟨p, hpv, hplen, hpe⟩ := ((level_eq_some_iff M 0 u e).1 he).1
  obtain ⟨q, hqv, hqlen, hqe⟩ := ((level_eq_some_iff M 0 v f).1 hf).1
  have hp : p.Shortest := by simpa only [AltPath.Shortest, hplen, hpe, hpv] using (level_eq_some_iff M 0 u e).1 he
  have hq : q.Shortest := by simpa only [AltPath.Shortest, hqlen, hqe, hqv] using (level_eq_some_iff M 0 v f).1 hf
  have hppar : p.length % 2 = 0 := by omega
  have hqpar : q.length % 2 = 0 := by omega
  have hup : Blossom M t b p.last := by rw [hpv]; exact hu
  have hvq : Blossom M t c q.last := by rw [hqv]; exact hv
  obtain ⟨B, hB, _, _, _, _⟩ := blossom_on_shortest t b p.last hup p rfl hp
  obtain ⟨C, hC, _, _, _, _⟩ := blossom_on_shortest t c q.last hvq q rfl hq
  have hadjp : G.Adj p.last q.last := by rw [hpv, hqv]; exact hadj
  have hunmp : M.mate p.last ≠ some q.last := by rw [hpv, hqv]; exact hunmatched
  have hCB := p.blossom_edge_boundary_lt q hp hq hppar hqpar t b c hup hvq hb hc hne hconf
    hadjp hunmp (by omega) B hB C hC
  have hBC := q.blossom_edge_boundary_lt p hq hp hqpar hppar t c b hvq hup hc hb (fun he => hne he.symm) hconf
    (G.symm hadjp) (by intro hm; exact hunmp (M.symm hm)) (by omega) C hC B hB
  omega

end MaximumMatching
