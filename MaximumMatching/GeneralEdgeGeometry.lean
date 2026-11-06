import MaximumMatching.GeneralBaseInduction
import MaximumMatching.GeneralPathGeometry

section GeneralEdgeHelpers

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

end GeneralEdgeHelpers

section GeneralEdgeBoundStep

namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The edge-tenacity step for every member of the current blossom. Both lower
edge hypotheses are at the preceding odd cutoff; shorter honest prefixes use
strong induction on their actual path length. -/
theorem general_blossom_suffix_edge_step (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w)
    (hlow : ∀ (p : AltPath M), p.Shortest →
      ∀ (b : V), levelLT (some (t - 2)) (tenacity M b) → Blossom M (t - 2) b p.last →
      ∀ (i : Fin (p.length + 1)), p.vertex i = b → ∀ k : Fin p.length, i.val ≤ k.val →
        levelLE (edgeTenacity M (p.vertex ⟨k.val, by omega⟩) (p.vertex ⟨k.val + 1, by omega⟩)) (some (t - 2)))
    (hlowrel : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ (q : AltSegment M), q.Shortest → q.first = b → q.last = v → ∀ k : Fin q.length,
        levelLE (edgeTenacity M (q.vertex ⟨k.val, by omega⟩) (q.vertex ⟨k.val + 1, by omega⟩)) (some (t - 2)))
    (r : AltPath M) (hr : r.Shortest)
    (b : V) (hb : levelLT (some t) (tenacity M b)) (hbl : Blossom M t b r.last)
    (i : Fin (r.length + 1)) (hi : r.vertex i = b) (k : Fin r.length) (hik : i.val ≤ k.val) :
    levelLE (edgeTenacity M (r.vertex ⟨k.val, by omega⟩) (r.vertex ⟨k.val + 1, by omega⟩)) (some t) := by
  have hexistslow : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b := by
    intro v s hs hst
    exact hexists v s hs (by omega)
  have liftBound (e : Option Nat) (he : levelLE e (some (t - 2))) : levelLE e (some t) := by
    cases e with
    | none => exact False.elim he
    | some s => change s ≤ t - 2 at he; change s ≤ t; omega
  have aux : ∀ L (p : AltPath M), p.length = L → p.Shortest →
      ∀ (b : V), levelLT (some t) (tenacity M b) → Blossom M t b p.last →
      ∀ (i : Fin (p.length + 1)), p.vertex i = b → ∀ k : Fin p.length, i.val ≤ k.val →
        levelLE (edgeTenacity M (p.vertex ⟨k.val, by omega⟩) (p.vertex ⟨k.val + 1, by omega⟩)) (some t) := by
    intro L
    induction L using Nat.strongRecOn with
    | ind L ih =>
      intro p hpL hp b hb hbl i hi k hik
      have hbase := blossom_baseOnPath t b p.last hbl hb p rfl hp
      have hprefix (K : Fin (p.length + 1)) (hK : K.val < p.length)
          (hshort : (p.take K.val (by omega)).Shortest) (hkK : k.val < K.val) :
          levelLE (edgeTenacity M (p.vertex ⟨k.val, by omega⟩) (p.vertex ⟨k.val + 1, by omega⟩)) (some t) := by
        have hiK : i.val < K.val := by omega
        obtain ⟨s, hs, hst⟩ := blossom_suffix_tenacity_bound t b p.last hbl hb p rfl hp i K hi hiK
        let a := p.take K.val (by omega)
        have habase := p.baseOnPath_take_after t b hbase i K hi (by omega)
        have hamem : Blossom M t b a.last := a.blossom_of_shortest_base hshort t ht hexists b habase
          (by change levelLE (tenacity M (p.vertex K)) (some t); rw [hs]; exact hst)
        exact ih K.val (by omega) a rfl hshort b hb hamem
          ⟨i.val, by change i.val < K.val + 1; omega⟩ hi
          ⟨k.val, by change k.val < K.val; exact hkK⟩ hik
      obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound t b p.last hbl
      by_cases hst' : s < t
      · have hsodd := tenacity_odd M p.last s hs
        have htlow : (t - 2) % 2 = 1 := by omega
        obtain ⟨c, hc, hcmem⟩ := blossom_cover_of_base_existence (t - 2) htlow hexistslow p.last s hs (by omega)
        obtain ⟨A, hA, _, hAlt, _, hAshort⟩ := blossom_on_shortest (t - 2) c p.last hcmem p rfl hp
        have hblow : levelLT (some (t - 2)) (tenacity M b) := by
          cases he : tenacity M b with
          | none => trivial
          | some n =>
            have hn : t < n := by simpa only [he, levelLT] using hb
            change t - 2 < n
            omega
        have hiA : i.val ≤ A.val := by
          obtain ⟨K, hK, _, hKlast⟩ := blossom_baseOnPath (t - 2) c p.last hcmem hc p rfl hp
          have hKA : K = A := p.injective K A (hK.trans hA.symm)
          subst K
          by_cases hAi : A.val < i.val
          · exact False.elim (hKlast i hAi (by rw [hi]; exact hblow))
          · omega
        by_cases hAk : A.val ≤ k.val
        · exact liftBound _ (hlow p hp c hc hcmem A hA k hAk)
        · exact hprefix A hAlt hAshort (by omega)
      · have hpt : tenacity M p.last = some t := hs.trans (congrArg some (by omega))
        have hpos : 0 < p.length := by have := k.isLt; omega
        let pred : Fin (p.length + 1) := ⟨p.length - 1, by omega⟩
        by_cases hpred : p.BFSHonest pred
        · by_cases hklast : k.val = p.length - 1
          · have he := p.last_edge_tenacity_of_honest_predecessor hp hpos hpred t hpt
            have hk0 : (⟨k.val, by omega⟩ : Fin (p.length + 1)) = pred := Fin.ext hklast
            have hk1 : (⟨k.val + 1, by omega⟩ : Fin (p.length + 1)) = ⟨p.length, by omega⟩ := Fin.ext (by change k.val + 1 = p.length; omega)
            rw [hk0, hk1]
            change levelLE (edgeTenacity M (p.vertex pred) p.last) (some t)
            rw [he]
            exact Nat.le_refl _
          · exact hprefix pred (by change p.length - 1 < p.length; omega) hpred
              (by change k.val < p.length - 1; have := k.isLt; omega)
        · obtain ⟨hpo, houter⟩ := p.dishonest_last_predecessor_outer hp t hpt hpos hpred
          have hipred : i.val < pred.val := by
            by_cases he : i.val = pred.val
            · have he' : i = pred := Fin.ext he
              have hhigh : levelLT (some t) (tenacity M (p.vertex pred)) := by rw [← he', hi]; exact hb
              have hh := (p.limited_bfs_honesty hp pred (by rw [hpt]; exact levelLT_le hhigh)).1
              exact False.elim (hpred hh)
            · change i.val < p.length - 1
              change i.val ≠ p.length - 1 at he
              have := k.isLt
              omega
          obtain ⟨u, hu, hut⟩ := blossom_suffix_tenacity_bound t b p.last hbl hb p rfl hp i pred hi hipred
          have hut' : u < t := by
            by_cases he : u = t
            · have hhon := (p.limited_bfs_honesty hp pred (by rw [hpt, hu, he]; exact Nat.le_refl _)).1
              exact False.elim (hpred hhon)
            · omega
          have huodd := tenacity_odd M (p.vertex pred) u hu
          have hclow : levelLT (some (t - 2)) (tenacity M p.last) := by
            rw [hpt]
            change t - 2 < t
            omega
          have hmember := (p.dishonest_outer_predecessor_base hp hpo houter t u hpt hu hut'
            (hexistslow (p.vertex pred) u hu (by omega)) hpred).2
          obtain ⟨D, hDo, hDmem, hfirst, htailshort, htail⟩ := p.exists_first_entry_confined_tail hp hpo
            (t - 2) hclow (by intro v hv q hq hqf hql; exact hconf p.last v hv hclow q hq hqf hql)
            ⟨pred, hmember⟩
          have hiD : i.val < D.val := by
            by_cases hDi : D.val ≤ i.val
            · rcases htail i hDi with he | hm
              · have hh := congrArg Fin.val (p.injective i ⟨p.length, by omega⟩ he)
                change i.val = p.length at hh
                have := k.isLt
                omega
              · have hmcurrent := (blossom_strict_nested_of_base_mem (t - 2) t ht p.last b hclow hbl).1 _ hm
                exact False.elim (blossom_excludes_base t b hb (hi ▸ hmcurrent))
            · omega
          have hhon := p.first_entry_prefix_honest hp hpo t hpt hexistslow hconf D hDo hDmem hfirst htailshort
          by_cases hDk : D.val ≤ k.val
          · let q := p.reverseOddTail hpo D
            let K : Fin q.length := ⟨p.length - (k.val + 1), by change p.length - (k.val + 1) < p.length - D.val; have := k.isLt; omega⟩
            have he := hlowrel p.last (p.vertex D) hDmem hclow q htailshort
              (p.reverseOddTail_first hpo D) (p.reverseOddTail_last hpo D) K
            have he₀ : q.vertex ⟨K.val, by omega⟩ = p.vertex ⟨k.val + 1, by omega⟩ := by
              change p.vertex ⟨p.length - (p.length - (k.val + 1)), _⟩ = _
              congr 1
              apply Fin.ext
              change p.length - (p.length - (k.val + 1)) = k.val + 1
              have := k.isLt
              omega
            have he₁ : q.vertex ⟨K.val + 1, by omega⟩ = p.vertex ⟨k.val, by omega⟩ := by
              change p.vertex ⟨p.length - (p.length - (k.val + 1) + 1), _⟩ = _
              congr 1
              apply Fin.ext
              change p.length - (p.length - (k.val + 1) + 1) = k.val
              have := k.isLt
              omega
            rw [he₀, he₁, edgeTenacity_symmetric] at he
            exact liftBound _ he
          · by_cases hkD : k.val + 1 = D.val
            · have he := p.first_entry_edge_tenacity hp hpo t hpt D hDo hDmem htailshort hhon
              have hk0 : (⟨k.val, by omega⟩ : Fin (p.length + 1)) = ⟨D.val - 1, by omega⟩ := Fin.ext (by change k.val = D.val - 1; omega)
              have hk1 : (⟨k.val + 1, by omega⟩ : Fin (p.length + 1)) = D := Fin.ext hkD
              rw [hk0, hk1, he]
              exact Nat.le_refl _
            · exact hprefix ⟨D.val - 1, by have := D.isLt; omega⟩
                (by change D.val - 1 < p.length; have := D.isLt; omega) hhon
                (by change k.val < D.val - 1; omega)
  exact aux r.length r rfl hr b hb hbl i hi k hik

end MaximumMatching.AltPath

namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Global suffix edge bounds transfer to every shortest relative segment by
an actual simple shortest concatenation. -/
theorem blossom_relative_edge_bound_of_global (t : Nat) (b v : V)
    (hv : Blossom M t b v) (hb : levelLT (some t) (tenacity M b))
    (hglobal : ∀ p : AltPath M, p.Shortest → p.last = v →
      ∀ i : Fin (p.length + 1), p.vertex i = b → ∀ k : Fin p.length, i.val ≤ k.val →
        levelLE (edgeTenacity M (p.vertex ⟨k.val, by omega⟩) (p.vertex ⟨k.val + 1, by omega⟩)) (some t))
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v)
    (k : Fin q.length) :
    levelLE (edgeTenacity M (q.vertex ⟨k.val, by omega⟩) (q.vertex ⟨k.val + 1, by omega⟩)) (some t) := by
  obtain ⟨s, hs, _⟩ := blossom_tenacity_bound t b v hv
  obtain ⟨r, hrv, hr, _⟩ := finite_tenacity_shortest_parity v s 0 hs
  obtain ⟨i, hib, hie, _, _, hip⟩ := blossom_on_shortest t b v hv r hrv hr
  let p := r.take i.val (by omega)
  have hp : p.Shortest := hip
  have hpe : p.length % 2 = 0 := hie
  have hpb : p.last = b := hib
  let hdis := blossom_relative_avoids_prefix t b v hv hb p hp hpe hpb q hq hqb hqv
  let a := p.appendSegment q hpe (hpb.trans hqb.symm) hdis
  have ha : a.Shortest := blossom_append_relative_shortest t b v hv hb p hp hpe hpb q hq hqb hqv
  have hav : a.last = v := (p.appendSegment_last q hpe (hpb.trans hqb.symm) hdis).trans hqv
  let I : Fin (a.length + 1) := ⟨p.length, by change p.length < p.length + q.length + 1; omega⟩
  have hIb : a.vertex I = b := by
    change (if h : p.length ≤ p.length then p.vertex ⟨p.length, _⟩ else _) = b
    simpa only [Nat.le_refl, dite_true, AltPath.last] using hpb
  have hedge := hglobal a ha hav I hIb
    ⟨p.length + k.val, by change p.length + k.val < p.length + q.length; omega⟩
    (by change p.length ≤ p.length + k.val; omega)
  have hvertex (j : Fin (q.length + 1)) :
      a.vertex ⟨p.length + j.val, by change p.length + j.val < p.length + q.length + 1; omega⟩ = q.vertex j :=
    p.appendSegment_vertex_suffix q hpe (hpb.trans hqb.symm) hdis j
  change levelLE (edgeTenacity M
    (a.vertex ⟨p.length + k.val, by change p.length + k.val < p.length + q.length + 1; omega⟩)
    (a.vertex ⟨p.length + (k.val + 1), by change p.length + (k.val + 1) < p.length + q.length + 1; omega⟩)) (some t) at hedge
  rw [hvertex ⟨k.val, by omega⟩, hvertex ⟨k.val + 1, by omega⟩] at hedge
  exact hedge

end MaximumMatching

end GeneralEdgeBoundStep

section GeneralEdgeBounds

/-! Every edge on an actual shortest relative blossom path has tenacity at most
its eligible cutoff. Strong cutoff induction closes the global and relative
edge bounds together, using the already proved base and confinement theorems. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V}

/-- Joint global and relative edge bounds at every eligible cutoff. -/
theorem general_blossom_edge_bounds (M : Matching G) : ∀ t : Nat, EligibleTenacity M t →
    (∀ (p : AltPath M), p.Shortest → ∀ (b : V), levelLT (some t) (tenacity M b) →
      Blossom M t b p.last → ∀ i : Fin (p.length + 1), p.vertex i = b →
      ∀ k : Fin p.length, i.val ≤ k.val →
        levelLE (edgeTenacity M (p.vertex ⟨k.val, by omega⟩) (p.vertex ⟨k.val + 1, by omega⟩)) (some t)) ∧
    (∀ (b v : V), Blossom M t b v → levelLT (some t) (tenacity M b) →
      ∀ (q : AltSegment M), q.Shortest → q.first = b → q.last = v → ∀ k : Fin q.length,
        levelLE (edgeTenacity M (q.vertex ⟨k.val, by omega⟩) (q.vertex ⟨k.val + 1, by omega⟩)) (some t)) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro ht
    have hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b := by
      intro v s hs hst
      have helig : EligibleTenacity M s := by
        refine ⟨tenacity_odd M v s hs, ⟨v, ?_⟩, ?_⟩
        · rw [hs]
          exact Nat.le_refl _
        · intro p hp
          have := ht.2.2 p hp
          omega
      obtain ⟨b, hb, _⟩ := general_unique_base M s helig v hs
      exact ⟨b, s, hs, hb⟩
    have lowEligible (b v : V) (hv : Blossom M (t - 2) b v) : EligibleTenacity M (t - 2) := by
      obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound (t - 2) b v hv
      have hsodd := tenacity_odd M v s hs
      refine ⟨by have := ht.1; omega, ⟨v, ?_⟩, ?_⟩
      · rw [hs]
        exact hst
      · intro p hp
        have := ht.2.2 p hp
        omega
    have hlowlt : t - 2 < t := by have := ht.1; omega
    have hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
        ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
          ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w := by
      intro b v hv hb q hq hqb hqv
      exact general_blossom_relative_confined M (t - 2) (lowEligible b v hv) b v hv hb q hq hqb hqv
    have hlow : ∀ (p : AltPath M), p.Shortest →
        ∀ (b : V), levelLT (some (t - 2)) (tenacity M b) → Blossom M (t - 2) b p.last →
        ∀ (i : Fin (p.length + 1)), p.vertex i = b → ∀ k : Fin p.length, i.val ≤ k.val →
          levelLE (edgeTenacity M (p.vertex ⟨k.val, by omega⟩) (p.vertex ⟨k.val + 1, by omega⟩)) (some (t - 2)) := by
      intro p hp b hb hv i hi k hik
      exact (ih (t - 2) hlowlt (lowEligible b p.last hv)).1 p hp b hb hv i hi k hik
    have hlowrel : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
        ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v → ∀ k : Fin q.length,
          levelLE (edgeTenacity M (q.vertex ⟨k.val, by omega⟩) (q.vertex ⟨k.val + 1, by omega⟩)) (some (t - 2)) := by
      intro b v hv hb q hq hqb hqv k
      exact (ih (t - 2) hlowlt (lowEligible b v hv)).2 b v hv hb q hq hqb hqv k
    have hglobal : ∀ (p : AltPath M), p.Shortest → ∀ (b : V), levelLT (some t) (tenacity M b) →
        Blossom M t b p.last → ∀ i : Fin (p.length + 1), p.vertex i = b →
        ∀ k : Fin p.length, i.val ≤ k.val →
          levelLE (edgeTenacity M (p.vertex ⟨k.val, by omega⟩) (p.vertex ⟨k.val + 1, by omega⟩)) (some t) := by
      intro p hp b hb hv i hi k hik
      exact AltPath.general_blossom_suffix_edge_step t ht.1 hexists hconf hlow hlowrel p hp b hb hv i hi k hik
    refine ⟨hglobal, ?_⟩
    intro b v hv hb q hq hqb hqv k
    apply blossom_relative_edge_bound_of_global t b v hv hb ?_ q hq hqb hqv k
    intro p hp hpv i hi j hij
    exact hglobal p hp b hb (by rw [hpv]; exact hv) i hi j hij

namespace AltPath
variable {M : Matching G}

/-- Every edge at or after the actual boundary on a shortest path to a blossom
member has finite edge tenacity no greater than the eligible cutoff. -/
theorem general_blossom_suffix_edge_bound (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (ht : EligibleTenacity M t) (b : V)
    (hb : levelLT (some t) (tenacity M b)) (hv : Blossom M t b p.last)
    (i : Fin (p.length + 1)) (hi : p.vertex i = b) (k : Fin p.length) (hik : i.val ≤ k.val) :
    levelLE (edgeTenacity M (p.vertex ⟨k.val, by omega⟩) (p.vertex ⟨k.val + 1, by omega⟩)) (some t) :=
  (general_blossom_edge_bounds M t ht).1 p hp b hb hv i hi k hik

end AltPath

/-- The edge-tenacity clause of Theorem 6.19(4) for every eligible cutoff and
every shortest relative path, with no lower-bound oracle left as a premise. -/
theorem general_blossom_relative_edge_bound (M : Matching G) (t : Nat) (ht : EligibleTenacity M t)
    (b v : V) (hv : Blossom M t b v) (hb : levelLT (some t) (tenacity M b))
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v)
    (k : Fin q.length) :
    levelLE (edgeTenacity M (q.vertex ⟨k.val, by omega⟩) (q.vertex ⟨k.val + 1, by omega⟩)) (some t) :=
  (general_blossom_edge_bounds M t ht).2 b v hv hb q hq hqb hqv k

end MaximumMatching

end GeneralEdgeBounds

section GeneralBridgeTerminal

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

end GeneralBridgeTerminal
