import MaximumMatching.GeneralEdgeHelpers

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
