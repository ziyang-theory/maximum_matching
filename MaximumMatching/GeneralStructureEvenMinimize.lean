import MaximumMatching.GeneralStructureCandidate
import MaximumMatching.GeneralStructureDoubleReverse
import MaximumMatching.GeneralStructureMinimize
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

private theorem least_even_candidate (P : Nat → Prop) (h : ∃ k, P k) :
    ∃ k, P k ∧ ∀ l, P l → k ≤ l := by
  classical
  obtain ⟨k, hk⟩ := h
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hs : ∃ l, l < k ∧ P l
    · obtain ⟨l, hl, hp⟩ := hs
      exact ih l hl hp
    · exact ⟨k, hk, fun l hl => Nat.le_of_not_lt (fun hlt => hs ⟨l, hlt, hl⟩)⟩

/-- An absent high boundary cannot have a short even shortest path to a blossom
member on the opposite even shortest path. Minimum-length candidates force a
single final matched intersection; two reverse splices then lower its tenacity. -/
theorem no_even_candidate_at_absent_boundary (p : AltPath M) (hp : p.Shortest)
    (hpe : p.length % 2 = 0) (O : Nat) (d : V)
    (hd : levelLT (some (p.length + O)) (tenacity M d))
    (hclosed : ∀ r : AltPath M, r.Shortest → Blossom M (p.length + O) d r.last →
      r.length < O → ∀ (i j : Fin (r.length + 1)), r.vertex i = d → i.val < j.val →
        Blossom M (p.length + O) d (r.vertex j))
    (habsent : ∀ a, p.vertex a ≠ d)
    (r₀ : AltPath M) (hr₀ : r₀.Shortest) (hr₀e : r₀.length % 2 = 0)
    (hmem₀ : Blossom M (p.length + O) d r₀.last)
    (hon₀ : ∃ a, p.vertex a = r₀.last) (hlen₀ : r₀.length < O) : False := by
  let P := fun n => ∃ r : AltPath M, r.length = n ∧ r.Shortest ∧ r.length % 2 = 0 ∧
    Blossom M (p.length + O) d r.last ∧ (∃ a, p.vertex a = r.last)
  have hr₀P : P r₀.length := ⟨r₀, rfl, hr₀, hr₀e, hmem₀, hon₀⟩
  obtain ⟨N, ⟨r, hrN, hr, hre, hmem, hon⟩, hleast⟩ := least_even_candidate P ⟨_, hr₀P⟩
  have hNlt : N < O := by have := hleast r₀.length hr₀P; omega
  obtain ⟨D, hDd, hDe, hDN, _, _⟩ := blossom_on_shortest (p.length + O) d r.last hmem r rfl hr
  have havoid : ∀ (a : Fin (p.length + 1)) (j : Fin (r.length + 1)),
      D.val ≤ j.val → j.val < r.length - 1 → p.vertex a ≠ r.vertex j := by
    intro a j hDj hjN heq
    by_cases he : D.val = j.val
    · have he' : D = j := Fin.ext he
      exact habsent a (heq.trans ((congrArg r.vertex he').symm.trans hDd))
    · have hwmem := hclosed r hr hmem (by omega) D j hDd (by omega)
      obtain ⟨j', _, hm⟩ := r.even_suffix_matched_closed hre (D.val + 1) (by omega) j (by omega)
      obtain ⟨s, hs, hse, hsmem, hson, hlen⟩ := p.even_shortest_blossom_candidate hpe
        (p.length + O) d (r.vertex j) (r.vertex j') j.val hwmem hm ⟨a, heq⟩ (r.prefix_witness j)
      have hmin := hleast s.length ⟨s, rfl, hs, hse, hsmem, hson⟩
      omega
  obtain ⟨a, ha⟩ := hon
  obtain ⟨h⟩ := firstHit_exists p r (D.val + 1)
    ⟨a, ⟨r.length, by omega⟩, by change D.val + 1 ≤ r.length; omega, ha⟩
  have hd' : levelLT (some (p.length + O)) (tenacity M (r.vertex D)) := by rw [hDd]; exact hd
  have habs' : ∀ a, p.vertex a ≠ r.vertex D := by intro a; rw [hDd]; exact habsent a
  have hh := r.first_high_suffix_hit_le_of_length_le p hr hre D hDe (p.length + O)
    (by omega) hd' habs' h
  have hJ : h.pi.val = r.length - 1 := by
    by_cases hj : h.pi.val < r.length - 1
    · exact False.elim (havoid h.qi h.pi (by have := h.in_suffix; omega) hj h.hit)
    · have := h.pi.isLt
      omega
  have hjoin : p.vertex h.qi = r.vertex ⟨r.length - 1, by omega⟩ := by
    have hj : h.pi = ⟨r.length - 1, by omega⟩ := Fin.ext hJ
    simpa only [hj] using h.hit
  let r₁ := r.take (r.length - 1) (by omega)
  have hr₁len : r₁.length = r.length - 1 := rfl
  have hr₁end : r₁.last = p.vertex h.qi := hjoin.symm
  have hr₁odd : r₁.length % 2 = 1 := by omega
  have hr₁short : r₁.Shortest := by
    have hm := r.even_last_mate hre (by omega)
    have he : r.length - 1 + 1 = r.length := by omega
    have hs := (matched_shortest_iff M (M.symm hm) (r.length - 1)).1
      (by rw [he]; simpa only [Shortest, hre] using hr)
    change IsShortest M (r₁.length % 2) r₁.last r₁.length
    rw [hr₁odd]
    exact hs
  have hIstrict : r.length - 1 < h.qi.val := by
    by_cases he : h.qi.val = r.length - 1
    · let z := p.take h.qi.val (by omega)
      have hzshort : z.Shortest := by
        have hsame : z.length = r₁.length := by change h.qi.val = r.length - 1; exact he
        have hzlast : z.last = r₁.last := hr₁end.symm
        simpa only [Shortest, hsame, hzlast] using hr₁short
      have hzmem : Blossom M (p.length + O) d z.last := by
        have hzlast : z.last = r.vertex ⟨r.length - 1, by omega⟩ := hjoin
        rw [hzlast]
        exact hclosed r hr hmem (by omega) D ⟨r.length - 1, by omega⟩ hDd
          (by change D.val < r.length - 1; omega)
      obtain ⟨k, hk, _, _, _, _⟩ := blossom_on_shortest (p.length + O) d z.last hzmem z rfl hzshort
      exact False.elim (habsent ⟨k.val, by have := k.isLt; change k.val < h.qi.val + 1 at this; omega⟩ hk)
    · omega
  obtain ⟨k, j, hIj, hkj⟩ := p.shorter_prefix_intersects hp h.qi.val (by omega)
    r₁ hr₁end (by omega) (by omega)
  have hlast : p.vertex ⟨h.qi.val + 1, by omega⟩ = r.last := by
    have hpnext := p.mate_next h.qi.val (by omega) hh.1
    have hrnext := r.mate_next (r.length - 1) (by omega) (by omega)
    rw [hjoin] at hpnext
    have hm := M.mate_unique hpnext hrnext
    simpa only [show r.length - 1 + 1 = r.length by omega, last] using hm
  have hjcut : h.qi.val + 2 ≤ j.val := by
    by_cases he : j.val = h.qi.val + 1
    · have he' : j = ⟨h.qi.val + 1, by omega⟩ := Fin.ext he
      rw [he', hlast] at hkj
      have heq := congrArg Fin.val (r.injective ⟨k.val, by have := k.isLt; change k.val < r.length - 1 + 1 at this; omega⟩
        ⟨r.length, by omega⟩ hkj)
      have hkb := k.isLt
      change k.val < r.length - 1 + 1 at hkb
      change k.val = r.length at heq
      omega
    · omega
  obtain ⟨g⟩ := firstHit_exists r p (h.qi.val + 2)
    ⟨⟨k.val, by have := k.isLt; change k.val < r.length - 1 + 1 at this; omega⟩, j, hjcut, hkj⟩
  have hK : g.qi.val < D.val := by
    by_cases hg : g.qi.val < r.length - 1
    · by_cases hKD : g.qi.val < D.val
      · exact hKD
      · exact False.elim (havoid g.pi g.qi (by omega) hg g.hit.symm)
    · by_cases he : g.qi.val = r.length - 1
      · have he' : g.qi = ⟨r.length - 1, by omega⟩ := Fin.ext he
        have ghit := g.hit
        rw [he', ← hjoin] at ghit
        have hpidx := congrArg Fin.val (p.injective h.qi g.pi ghit)
        have := g.in_suffix
        omega
      · have he : g.qi = ⟨r.length, by omega⟩ := Fin.ext (by have := g.qi.isLt; change g.qi.val = r.length; omega)
        have hv : r.vertex g.qi = r.last := by rw [he]; rfl
        have hpidx := congrArg Fin.val (p.injective ⟨h.qi.val + 1, by omega⟩ g.pi
          (hlast.trans (hv.symm.trans g.hit)))
        have := g.in_suffix
        change h.qi.val + 1 = g.pi.val at hpidx
        omega
  obtain ⟨s, hs, hbound⟩ := p.double_reverse_boundary_bound_of_firstHit r hp hpe hre D hDe
    h.qi.val O (by omega) hh.1 (by omega) (by omega) hjoin havoid g hK
  rw [hs] at hd'
  change p.length + O < s at hd'
  omega

end MaximumMatching.AltPath
