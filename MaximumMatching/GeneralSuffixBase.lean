import MaximumMatching.GeneralStructureInduction
import MaximumMatching.GeneralRelativeBaseTransfer

namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The suffix-base step, strengthened to every member of the current blossom.
The induction hypotheses concern only the preceding odd cutoff. -/
theorem general_blossom_suffix_base_step (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w)
    (hlow : ∀ (p : AltPath M), p.Shortest →
      ∀ (b : V), levelLT (some (t - 2)) (tenacity M b) → Blossom M (t - 2) b p.last →
      ∀ (i j : Fin (p.length + 1)), p.vertex i = b → i.val < j.val →
        ∃ a, IsBase M (p.vertex j) a ∧ ∃ k : Fin (p.length + 1), i.val ≤ k.val ∧ p.vertex k = a)
    (hlowrel : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ (q : AltSegment M), q.Shortest → q.first = b → q.last = v →
      ∀ j : Fin (q.length + 1), 0 < j.val →
        ∃ a, IsBase M (q.vertex j) a ∧ q.Contains a)
    (r : AltPath M) (hr : r.Shortest)
    (b : V) (hb : levelLT (some t) (tenacity M b)) (hbl : Blossom M t b r.last)
    (i j : Fin (r.length + 1)) (hi : r.vertex i = b) (hij : i.val < j.val) :
    ∃ a, IsBase M (r.vertex j) a ∧ ∃ k : Fin (r.length + 1), i.val ≤ k.val ∧ r.vertex k = a := by
  have hexistslow : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b := by
    intro v s hs hst
    exact hexists v s hs (by omega)
  have aux : ∀ L (p : AltPath M), p.length = L → p.Shortest →
      ∀ (b : V), levelLT (some t) (tenacity M b) → Blossom M t b p.last →
      ∀ (i j : Fin (p.length + 1)), p.vertex i = b → i.val < j.val →
        ∃ a, IsBase M (p.vertex j) a ∧ ∃ k : Fin (p.length + 1), i.val ≤ k.val ∧ p.vertex k = a := by
    intro L
    induction L using Nat.strongRecOn with
    | ind L ih =>
      intro p hpL hp b hb hbl i j hi hij
      have hbase := blossom_baseOnPath t b p.last hbl hb p rfl hp
      have hprefix (K : Fin (p.length + 1)) (hK : K.val < p.length)
          (hshort : (p.take K.val (by omega)).Shortest)
          (hjK : j.val ≤ K.val) :
          ∃ a, IsBase M (p.vertex j) a ∧ ∃ k : Fin (p.length + 1), i.val ≤ k.val ∧ p.vertex k = a := by
        have hiK : i.val < K.val := by omega
        obtain ⟨s, hs, hst⟩ := blossom_suffix_tenacity_bound t b p.last hbl hb p rfl hp i K hi hiK
        let a := p.take K.val (by omega)
        have habase := p.baseOnPath_take_after t b hbase i K hi (by omega)
        have hamem : Blossom M t b a.last := a.blossom_of_shortest_base hshort t ht hexists b habase
          (by change levelLE (tenacity M (p.vertex K)) (some t); rw [hs]; exact hst)
        obtain ⟨c, hc, k, hik, hkc⟩ := ih K.val (by omega) a rfl hshort b hb hamem
          ⟨i.val, by change i.val < K.val + 1; omega⟩
          ⟨j.val, by change j.val < K.val + 1; omega⟩ hi hij
        exact ⟨c, hc, ⟨k.val, by have := k.isLt; change k.val < K.val + 1 at this; omega⟩, hik, hkc⟩
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
        by_cases hAj : A.val < j.val
        · obtain ⟨a, ha, k, hAk, hka⟩ := hlow p hp c hc hcmem A j hA hAj
          exact ⟨a, ha, k, by omega, hka⟩
        · exact hprefix A hAlt hAshort (by omega)
      · have hpt : tenacity M p.last = some t := hs.trans (congrArg some (by omega))
        by_cases hjlast : j.val = p.length
        · obtain ⟨c, hc⟩ := hexists p.last t hpt (Nat.le_refl _)
          have hcb := p.baseOnPath_unique t c b ((isBase_iff_common t hpt).1 hc p rfl hp) hbase
          refine ⟨b, ?_, i, Nat.le_refl _, hi⟩
          have hj : j = ⟨p.length, by omega⟩ := Fin.ext hjlast
          rw [hj]
          exact hcb ▸ hc
        have hjlt : j.val < p.length := by have := j.isLt; omega
        have hpos : 0 < p.length := by omega
        let pred : Fin (p.length + 1) := ⟨p.length - 1, by omega⟩
        by_cases hpred : p.BFSHonest pred
        · exact hprefix pred (by change p.length - 1 < p.length; omega) hpred
            (by change j.val ≤ p.length - 1; omega)
        · obtain ⟨hpo, houter⟩ := p.dishonest_last_predecessor_outer hp t hpt hpos hpred
          obtain ⟨u, hu, hut⟩ := blossom_suffix_tenacity_bound t b p.last hbl hb p rfl hp i pred hi
            (by change i.val < p.length - 1; omega)
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
                omega
              · have hmcurrent := (blossom_strict_nested_of_base_mem (t - 2) t ht p.last b hclow hbl).1 _ hm
                exact False.elim (blossom_excludes_base t b hb (hi ▸ hmcurrent))
            · omega
          by_cases hDj : D.val ≤ j.val
          · let q := p.reverseOddTail hpo D
            let J : Fin (q.length + 1) := ⟨p.length - j.val, by change p.length - j.val < p.length - D.val + 1; omega⟩
            have hJ : q.vertex J = p.vertex j := by
              change p.vertex ⟨p.length - (p.length - j.val), _⟩ = p.vertex j
              congr 1
              apply Fin.ext
              change p.length - (p.length - j.val) = j.val
              have := j.isLt
              omega
            obtain ⟨a, ha, K, hKa⟩ := hlowrel p.last (p.vertex D) hDmem hclow q htailshort
              (p.reverseOddTail_first hpo D) (p.reverseOddTail_last hpo D) J
              (by change 0 < p.length - j.val; omega)
            refine ⟨a, hJ ▸ ha, ⟨p.length - K.val, by omega⟩, ?_, hKa⟩
            have hK := K.isLt
            change K.val < p.length - D.val + 1 at hK
            change i.val ≤ p.length - K.val
            omega
          · have hhon := p.first_entry_prefix_honest hp hpo t hpt hexistslow hconf D hDo hDmem hfirst htailshort
            exact hprefix ⟨D.val - 1, by have := D.isLt; omega⟩
              (by change D.val - 1 < p.length; have := D.isLt; omega) hhon
              (by change j.val ≤ D.val - 1; omega)
  exact aux r.length r rfl hr b hb hbl i j hi hij

end MaximumMatching.AltPath

namespace MaximumMatching
variable {V : Type} {G : Graph V}

/-- Every original vertex after an eligible blossom boundary has its actual
base somewhere on the same original suffix. The endpoint may have any
tenacity at or below the cutoff. -/
theorem general_blossom_suffix_base (M : Matching G) : ∀ t : Nat,
    EligibleTenacity M t → ∀ (p : AltPath M), p.Shortest →
    ∀ (b : V), levelLT (some t) (tenacity M b) → Blossom M t b p.last →
    ∀ (i j : Fin (p.length + 1)), p.vertex i = b → i.val < j.val →
      ∃ a, IsBase M (p.vertex j) a ∧ ∃ k : Fin (p.length + 1), i.val ≤ k.val ∧ p.vertex k = a := by
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
          have htl := ht.2.2 p hp
          omega
      exact (isBase_exists_iff_unique s hs).2 (general_unique_base M s helig v hs)
    have heliglow (b v : V) (hv : Blossom M (t - 2) b v) : EligibleTenacity M (t - 2) := by
      obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound (t - 2) b v hv
      have hsodd := tenacity_odd M v s hs
      refine ⟨by have := ht.1; omega, ⟨v, ?_⟩, ?_⟩
      · rw [hs]
        exact hst
      · intro p hp
        have htl := ht.2.2 p hp
        omega
    have hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w := by
      intro b v hv hb q hq hqb hqv
      exact general_blossom_relative_confined M (t - 2) (heliglow b v hv) b v hv hb q hq hqb hqv
    have hlow : ∀ (p : AltPath M), p.Shortest →
      ∀ (b : V), levelLT (some (t - 2)) (tenacity M b) → Blossom M (t - 2) b p.last →
      ∀ (i j : Fin (p.length + 1)), p.vertex i = b → i.val < j.val →
        ∃ a, IsBase M (p.vertex j) a ∧ ∃ k : Fin (p.length + 1), i.val ≤ k.val ∧ p.vertex k = a := by
      intro p hp b hb hv i j hi hij
      exact ih (t - 2) (by have := ht.1; omega) (heliglow b p.last hv) p hp b hb hv i j hi hij
    have hlowrel : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ (q : AltSegment M), q.Shortest → q.first = b → q.last = v →
      ∀ j : Fin (q.length + 1), 0 < j.val →
        ∃ a, IsBase M (q.vertex j) a ∧ q.Contains a := by
      intro b v hv hb q hq hqb hqv j hj
      apply blossom_relative_base_occurs_of_global (t - 2) b v hv hb ?_ q hq hqb hqv j hj
      intro p hp hpv i j hi hij
      exact hlow p hp b hb (by rw [hpv]; exact hv) i j hi hij
    exact AltPath.general_blossom_suffix_base_step t ht.1 hexists hconf hlow hlowrel

/-- The suffix-base property also holds on every shortest relative path to
an eligible blossom member. The base may occur on either side of the vertex. -/
theorem general_blossom_relative_base (M : Matching G) (t : Nat) (ht : EligibleTenacity M t)
    (b v : V) (hv : Blossom M t b v) (hb : levelLT (some t) (tenacity M b))
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v)
    (j : Fin (q.length + 1)) (hj : 0 < j.val) :
    ∃ a, IsBase M (q.vertex j) a ∧ q.Contains a := by
  apply blossom_relative_base_occurs_of_global t b v hv hb ?_ q hq hqb hqv j hj
  intro p hp hpv i j hi hij
  exact general_blossom_suffix_base M t ht p hp b hb (by rw [hpv]; exact hv) i j hi hij

/-- Theorem 6.19(5): on any shortest path to a vertex of eligible tenacity,
the semantic base of each vertex after the endpoint's base occurs somewhere
on that original suffix, including its initial boundary. -/
theorem general_suffix_base (M : Matching G) (t : Nat) (ht : EligibleTenacity M t)
    (p : AltPath M) (hp : p.Shortest) (hpt : tenacity M p.last = some t)
    (b : V) (hb : IsBase M p.last b)
    (i j : Fin (p.length + 1)) (hi : p.vertex i = b) (hij : i.val < j.val) :
    ∃ k : Fin (p.length + 1), i.val ≤ k.val ∧ base M (p.vertex j) = some (p.vertex k) := by
  have hbh : levelLT (some t) (tenacity M b) := by simpa only [hpt] using hb.high
  have hbl := blossom_of_base_le t ht.1 b p.last hb (by rw [hpt]; exact Nat.le_refl _)
  obtain ⟨a, ha, k, hik, hka⟩ := general_blossom_suffix_base M t ht p hp b hbh hbl i j hi hij
  refine ⟨k, hik, ?_⟩
  rw [hka]
  exact (base_eq_some_iff (p.vertex j) a).2 ha

end MaximumMatching
