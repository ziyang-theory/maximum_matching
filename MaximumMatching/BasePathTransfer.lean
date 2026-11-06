import MaximumMatching.BaseGeometry
import MaximumMatching.GeneralBaseInduction
import MaximumMatching.GeneralBaseStructure
import MaximumMatching.GeneralPathGeometry
import MaximumMatching.RelativePaths

section GeneralRelativeBaseTransfer

/-! Transfer actual base occurrences from global shortest paths to arbitrary
shortest relative segments by the proved shortest, simple joining operation. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A global base-occurrence property after an iterated boundary transfers to
any shortest relative path from that boundary. The located base belongs to the
relative segment itself, including its initial boundary. -/
theorem blossom_relative_base_occurs_of_global (t : Nat) (c v : V)
    (hv : Blossom M t c v) (hc : levelLT (some t) (tenacity M c))
    (hglobal : ∀ p : AltPath M, p.Shortest → p.last = v →
      ∀ (i j : Fin (p.length + 1)), p.vertex i = c → i.val < j.val →
        ∃ b, IsBase M (p.vertex j) b ∧ ∃ k : Fin (p.length + 1), i.val ≤ k.val ∧ p.vertex k = b)
    (q : AltSegment M) (hq : q.Shortest) (hqc : q.first = c) (hqv : q.last = v)
    (j : Fin (q.length + 1)) (hj : 0 < j.val) :
    ∃ b, IsBase M (q.vertex j) b ∧ q.Contains b := by
  obtain ⟨s, hs, _⟩ := blossom_tenacity_bound t c v hv
  obtain ⟨r, hrv, hr, _⟩ := finite_tenacity_shortest_parity v s 0 hs
  obtain ⟨i, hic, hie, _, _, hip⟩ := blossom_on_shortest t c v hv r hrv hr
  let p := r.take i.val (by omega)
  have hp : p.Shortest := hip
  have hpe : p.length % 2 = 0 := hie
  have hpc : p.last = c := hic
  let hdis := blossom_relative_avoids_prefix t c v hv hc p hp hpe hpc q hq hqc hqv
  let a := p.appendSegment q hpe (hpc.trans hqc.symm) hdis
  have ha : a.Shortest := blossom_append_relative_shortest t c v hv hc p hp hpe hpc q hq hqc hqv
  have hav : a.last = v := (p.appendSegment_last q hpe (hpc.trans hqc.symm) hdis).trans hqv
  let I : Fin (a.length + 1) := ⟨p.length, by change p.length < p.length + q.length + 1; omega⟩
  have hIc : a.vertex I = c := by
    change (if h : p.length ≤ p.length then p.vertex ⟨p.length, _⟩ else _) = c
    simpa only [Nat.le_refl, dite_true, AltPath.last] using hpc
  let J : Fin (a.length + 1) := ⟨p.length + j.val, by change p.length + j.val < p.length + q.length + 1; omega⟩
  have hJq : a.vertex J = q.vertex j := p.appendSegment_vertex_suffix q hpe (hpc.trans hqc.symm) hdis j
  obtain ⟨b, hb, k, hIk, hkb⟩ := hglobal a ha hav I J hIc
    (by change p.length < p.length + j.val; omega)
  refine ⟨b, by simpa only [hJq] using hb, ?_⟩
  have hkbound := k.isLt
  change k.val < p.length + q.length + 1 at hkbound
  change p.length ≤ k.val at hIk
  let l : Fin (q.length + 1) := ⟨k.val - p.length, by omega⟩
  have hindex : (⟨p.length + l.val, by change p.length + l.val < p.length + q.length + 1; omega⟩ :
      Fin (a.length + 1)) = k := by
    apply Fin.ext
    change p.length + (k.val - p.length) = k.val
    omega
  have hkl : a.vertex k = q.vertex l := by
    rw [← hindex]
    exact p.appendSegment_vertex_suffix q hpe (hpc.trans hqc.symm) hdis l
  exact ⟨l, hkl.symm.trans hkb⟩

end MaximumMatching

end GeneralRelativeBaseTransfer

section GeneralSuffixBase

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

end GeneralSuffixBase

section GeneralBasePathTransfer

/-! Canonical-base transfer along actual shortest paths. A suffix containing
only vertices of tenacity at most the current cutoff preserves its prefix's
last high vertex. These are path statements, with no support-discovery or
mutable-bud premise. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The proved common-base theorem turns a base witnessed on one actual
shortest path into the semantic base of its endpoint. -/
theorem isBase_of_baseOnPath (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (ht : EligibleTenacity M t) (hpt : tenacity M p.last = some t)
    (b : V) (hb : p.BaseOnPath t b) : IsBase M p.last b := by
  obtain ⟨c, hc, _⟩ := general_unique_base M t ht p.last hpt
  have hcb := p.baseOnPath_unique t c b (hc p rfl hp) hb
  exact hcb ▸ (show IsBase M p.last c from ⟨t, hpt, hc⟩)

/-- If the named prefix endpoint is above the cutoff and all later vertices
are at or below it, that vertex is the endpoint's canonical base. -/
theorem isBase_of_high_suffix_boundary (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (ht : EligibleTenacity M t) (hpt : tenacity M p.last = some t)
    (i : Fin (p.length + 1)) (hi : levelLT (some t) (tenacity M (p.vertex i)))
    (htail : ∀ j : Fin (p.length + 1), i.val < j.val →
      levelLE (tenacity M (p.vertex j)) (some t)) : IsBase M p.last (p.vertex i) := by
  apply p.isBase_of_baseOnPath hp t ht hpt
  refine ⟨i, rfl, hi, ?_⟩
  intro j hij hj
  have hl := htail j hij
  cases he : tenacity M (p.vertex j) with
  | none => simp only [he, levelLE] at hl
  | some k =>
    rw [he] at hl hj
    change t < k at hj
    change k ≤ t at hl
    omega

/-- An honest prefix ending at the current tenacity and a suffix with no
higher-tenacity vertex have the same canonical base. This permits an
intermediate bud itself to have the current tenacity. -/
theorem common_base_of_shortest_prefix (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (ht : EligibleTenacity M t) (hpt : tenacity M p.last = some t)
    (i : Fin (p.length + 1)) (hi : tenacity M (p.vertex i) = some t)
    (hprefix : (p.take i.val (by omega)).Shortest)
    (htail : ∀ j : Fin (p.length + 1), i.val < j.val →
      levelLE (tenacity M (p.vertex j)) (some t)) :
    ∃ b, IsBase M p.last b ∧ IsBase M (p.vertex i) b := by
  obtain ⟨b, hb, _⟩ := general_unique_base M t ht (p.vertex i) hi
  have hqb := hb (p.take i.val (by omega)) rfl hprefix
  have hpb : p.BaseOnPath t b := by
    apply ((p.take i.val (by omega)).baseOnPath_initial_iff p
      (by simp only [take_length]; omega) (fun _ => rfl) t ?_ b).1 hqb
    intro j hj hhigh
    have hl := htail j hj
    cases he : tenacity M (p.vertex j) with
    | none => simp only [he, levelLE] at hl
    | some k =>
      rw [he] at hl hhigh
      change k ≤ t at hl
      change t < k at hhigh
      omega
  exact ⟨b, p.isBase_of_baseOnPath hp t ht hpt b hpb, t, hi, hb⟩

theorem base_eq_of_shortest_prefix (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (ht : EligibleTenacity M t) (hpt : tenacity M p.last = some t)
    (i : Fin (p.length + 1)) (hi : tenacity M (p.vertex i) = some t)
    (hprefix : (p.take i.val (by omega)).Shortest)
    (htail : ∀ j : Fin (p.length + 1), i.val < j.val →
      levelLE (tenacity M (p.vertex j)) (some t)) :
    base M p.last = base M (p.vertex i) := by
  obtain ⟨b, hb, hi⟩ := p.common_base_of_shortest_prefix hp t ht hpt i hi hprefix htail
  exact ((base_eq_some_iff p.last b).2 hb).trans
    ((base_eq_some_iff (p.vertex i) b).2 hi).symm

end MaximumMatching.AltPath

end GeneralBasePathTransfer

section PredecessorExpansion

/-! Actual matching paths for a predecessor edge whose lower endpoint is
contracted to an established lower-blossom boundary. The witness comes from
the defining minimum-level path of the predecessor relation. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Expand one downward predecessor jump through an actual lower blossom.
The expanded weight is the difference of the endpoint minimum levels, and
its strict interior lies in the target blossom. -/
theorem predecessor_blossom_expansion (cut : Nat) (hc : EligibleTenacity M cut)
    (u v b : V) (hpred : Predecessor M u v)
    (hbl : Blossom M cut b u) (hb : levelLT (some cut) (tenacity M b))
    (N B : Nat) (hN : minlevel M v = some N) (hB : minlevel M b = some B) :
    ∃ a : ParitySegment M, a.first = v ∧ a.last = b ∧ a.length + B = N ∧
      a.phase % 2 = (N + 1) % 2 ∧
      (a.phase + a.length) % 2 = (B + 1) % 2 ∧
      (∀ k : Fin (a.length + 1), 0 < k.val → k.val < a.length →
        Blossom M cut b (a.vertex k)) := by
  obtain ⟨p, hpv, hmin, hpos, hpu⟩ := hpred
  have hpn : p.length = N := Option.some.inj (hmin.symm.trans hN)
  let q := p.take (p.length - 1) (by omega)
  have hqu : q.last = u := hpu
  have hq : q.Shortest := p.minlevel_last_predecessor_honest (by rw [hpv]; exact hmin) hpos
  obtain ⟨i, hie, hib, _, hr⟩ := blossom_shortest_relative cut b u hbl hb q hqu hq
  obtain ⟨j, hjb, _, _, hjmin, _⟩ := blossom_on_shortest cut b u hbl q hqu hq
  have hji : j = i := q.injective j i (hjb.trans hib.symm)
  have hiB : i.val = B := by
    rw [hji, hB] at hjmin
    exact (Option.some.inj hjmin).symm
  let r := q.segment i.val (by omega) hie
  let s := p.segment i.val (by have := i.isLt; change i.val < p.length - 1 + 1 at this; omega) hie
  have hsf : s.first = b := hib
  have hsl : s.last = v := (p.segment_last _ _ _).trans hpv
  have hsn : s.length + B = N := by
    change p.length - i.val + B = N
    have := i.isLt
    change i.val < p.length - 1 + 1 at this
    omega
  have hinside : ∀ k : Fin (s.length + 1), 0 < k.val → k.val < s.length →
      Blossom M cut b (s.vertex k) := by
    intro k hk hkl
    have hkr : k.val ≤ q.length - i.val := by
      change k.val < p.length - i.val at hkl
      change k.val ≤ p.length - 1 - i.val
      omega
    have hw := general_blossom_relative_confined M cut hc b u hbl hb r hr hib
      ((q.segment_last _ _ _).trans hqu) (s.vertex k)
      ⟨⟨k.val, by change k.val < q.length - i.val + 1; omega⟩, rfl⟩
    rcases hw with hw | hw
    · have he := s.injective k ⟨0, by omega⟩ (hw.trans hsf.symm)
      have hn := congrArg Fin.val he
      dsimp only at hn
      omega
    · exact hw
  let a := (ParitySegment.ofAltSegment s).reverse
  refine ⟨a, (ParitySegment.ofAltSegment s).reverse_first.trans hsl,
    (ParitySegment.ofAltSegment s).reverse_last.trans hsf, hsn, ?_, ?_, ?_⟩
  · change (0 + s.length + 1) % 2 = (N + 1) % 2
    have hBe : B % 2 = 0 := by omega
    omega
  · change (0 + s.length + 1 + s.length) % 2 = (B + 1) % 2
    have hBe : B % 2 = 0 := by omega
    omega
  · intro k hk hkl
    have hkl' : k.val < s.length := hkl
    exact hinside ⟨s.length - k.val, by omega⟩
      (by change 0 < s.length - k.val; omega)
      (by change s.length - k.val < s.length; omega)

/-- A high-tenacity predecessor scanned before the half-tenacity frontier
is reached at its minimum level, even though arbitrary props may use a
source maximum level. -/
theorem predecessor_high_minlevel (u v : V) (N cut : Nat)
    (hpred : Predecessor M u v) (hN : minlevel M v = some N)
    (hc : cut % 2 = 1) (hbound : 2 * (N - 1) ≤ cut + 1)
    (hu : levelLT (some cut) (tenacity M u)) :
    minlevel M u = some (N - 1) := by
  obtain ⟨p, hpv, hmin, hpos, hpu⟩ := hpred
  have hpn : p.length = N := Option.some.inj (hmin.symm.trans hN)
  have hhon := (p.honest_iff_level ⟨p.length - 1, by omega⟩).1
    (p.minlevel_last_predecessor_honest (by rw [hpv]; exact hmin) hpos)
  have hlu : level M ((N - 1) % 2) u = some (N - 1) := by
    rw [hpu] at hhon
    simpa only [hpn] using hhon
  apply minlevel_of_below_half u (N - 1) (cut + 2) hlu (by omega)
  cases ht : tenacity M u with
  | none => trivial
  | some t =>
    have htodd := tenacity_odd M u t ht
    rw [ht] at hu
    change cut < t at hu
    change cut + 2 ≤ t
    omega

/-- An uncontracted high predecessor is realized by its actual graph edge. -/
theorem predecessor_direct_expansion (cut : Nat) (hc : cut % 2 = 1)
    (u v : V) (hpred : Predecessor M u v)
    (hu : levelLT (some cut) (tenacity M u))
    (N B : Nat) (hN : minlevel M v = some N) (hB : minlevel M u = some B)
    (hbound : 2 * (N - 1) ≤ cut + 1) :
    ∃ a : ParitySegment M, a.first = v ∧ a.last = u ∧ a.length + B = N ∧
      a.phase % 2 = (N + 1) % 2 ∧
      (a.phase + a.length) % 2 = (B + 1) % 2 ∧
      (∀ k : Fin (a.length + 1), 0 < k.val → k.val < a.length →
        Blossom M cut u (a.vertex k)) := by
  have hBu := predecessor_high_minlevel u v N cut hpred hN hc hbound hu
  have hBN : B = N - 1 := Option.some.inj (hB.symm.trans hBu)
  obtain ⟨p, hpv, hmin, hpos, hpu⟩ := hpred
  have hpn : p.length = N := Option.some.inj (hmin.symm.trans hN)
  have hadj : G.Adj v u := by
    have h := G.symm (p.adjacent ⟨p.length - 1, by omega⟩)
    have he : p.vertex ⟨p.length - 1 + 1, by omega⟩ = v := by
      simpa only [show p.length - 1 + 1 = p.length by omega, AltPath.last] using hpv
    rw [he, hpu] at h
    exact h
  have hm : (M.mate v = some u) ↔ (N + 1) % 2 = 1 := by
    have h := p.alternating ⟨p.length - 1, by omega⟩
    have h' : (M.mate u = some v) ↔ (N - 1) % 2 = 1 := by
      have he : p.vertex ⟨p.length - 1 + 1, by omega⟩ = v := by
        simpa only [show p.length - 1 + 1 = p.length by omega, AltPath.last] using hpv
      rw [he, hpu] at h
      simpa only [hpn] using h
    have he : (N - 1) % 2 = (N + 1) % 2 := by omega
    rw [he] at h'
    exact ⟨fun h => h'.1 (M.symm h), fun h => M.symm (h'.2 h)⟩
  let a := ParitySegment.ofEdge v u (N + 1) hadj hm
  refine ⟨a, rfl, rfl, ?_, rfl, ?_, ?_⟩
  · change 1 + B = N
    omega
  · change (N + 1 + 1) % 2 = (B + 1) % 2
    omega
  · intro k hk hkl
    change k.val < 1 at hkl
    omega

end MaximumMatching

end PredecessorExpansion
