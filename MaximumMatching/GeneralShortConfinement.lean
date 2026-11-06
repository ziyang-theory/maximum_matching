import MaximumMatching.GeneralStructureFirstHit

/-! Confinement on short global paths at the current tenacity. Only lower
confinement and current-tenacity bases at smaller minimum level are used. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

private theorem least_index (P : Nat → Prop) (h : ∃ k, P k) :
    ∃ k, P k ∧ ∀ l, P l → k ≤ l := by
  classical
  obtain ⟨k, hk⟩ := h
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hs : ∃ l, l < k ∧ P l
    · obtain ⟨l, hl, hp⟩ := hs
      exact ih l hl hp
    · exact ⟨k, hk, fun l hl => Nat.le_of_not_lt (fun hlt => hs ⟨l, hlt, hl⟩)⟩

/-- A low vertex between high vertices belongs to a lower blossom whose
boundary occurs no earlier than the named high vertex on its left. -/
theorem low_vertex_between_highs (p : AltPath M) (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M t b v → levelLT (some t) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M t b w)
    (D k B : Fin (p.length + 1)) (hDk : D.val < k.val) (hkB : k.val < B.val)
    (hD : levelLT (some t) (tenacity M (p.vertex D)))
    (hB : levelLT (some t) (tenacity M (p.vertex B)))
    (hk : levelLE (tenacity M (p.vertex k)) (some t))
    (hhon : ∀ j : Fin (p.length + 1), j.val ≤ B.val →
      levelLT (some t) (tenacity M (p.vertex j)) → minlevel M (p.vertex j) = some j.val) :
    ∃ i : Fin (p.length + 1), D.val ≤ i.val ∧ i.val < k.val ∧
      levelLT (some t) (tenacity M (p.vertex i)) ∧ Blossom M t (p.vertex i) (p.vertex k) := by
  classical
  let high := fun a : Fin (p.length + 1) => levelLT (some t) (tenacity M (p.vertex a))
  have hnotk : ¬high k := by
    cases he : tenacity M (p.vertex k) with
    | none => simp only [he, levelLE] at hk
    | some s =>
      have hst : s ≤ t := by simpa only [he, levelLE] using hk
      simpa only [high, he, levelLT] using Nat.not_lt_of_ge hst
  obtain ⟨d, ⟨i, hdi, hhi⟩, hminleft⟩ := least_index
    (fun d => ∃ i : Fin (p.length + 1), d + i.val = k.val ∧ high i)
    ⟨k.val - D.val, D, by omega, hD⟩
  have hDi : D.val ≤ i.val := by
    have := hminleft (k.val - D.val) ⟨D, by omega, hD⟩
    omega
  have hik : i.val < k.val := by
    by_cases he : i.val = k.val
    · exact False.elim (hnotk ((Fin.ext he) ▸ hhi))
    · omega
  obtain ⟨m, ⟨j, hjm, hkj, hjB, hhj⟩, hminright⟩ := least_index
    (fun m => ∃ j : Fin (p.length + 1), j.val = m ∧ k.val ≤ j.val ∧ j.val ≤ B.val ∧ high j)
    ⟨B.val, B, rfl, by omega, Nat.le_refl _, hB⟩
  have hkj' : k.val < j.val := by
    by_cases he : j.val = k.val
    · exact False.elim (hnotk ((Fin.ext he) ▸ hhj))
    · omega
  refine ⟨i, hDi, hik, hhi, p.low_stretch_mem t ht hexists hconf i j k hik hkj'
    (hhon j hjB hhj) hhi ?_⟩
  intro a hia haj
  have hna : ¬high a := by
    intro hha
    by_cases hak : a.val ≤ k.val
    · have hd := hminleft (k.val - a.val) ⟨a, by omega, hha⟩
      omega
    · have hm := hminright a.val ⟨a, rfl, by omega, by omega, hha⟩
      omega
  cases he : tenacity M (p.vertex a) with
  | none => exact False.elim (hna (by change levelLT (some t) (tenacity M (p.vertex a)); rw [he]; trivial))
  | some s =>
    change levelLE (some s) (some t)
    have hn : ¬t < s := by simpa only [high, he, levelLT] using hna
    exact Nat.le_of_not_lt hn

/-- Above-cutoff vertices on a short shortest path are honest at their actual
minimum levels, including equality with the current tenacity. -/
theorem short_high_minlevel (r : AltPath M) (hr : r.Shortest) (t : Nat)
    (hhalf : 2 * r.length < t) (hend : levelLE (tenacity M r.last) (some t))
    (i : Fin (r.length + 1)) (hi : levelLE (some t) (tenacity M (r.vertex i))) :
    minlevel M (r.vertex i) = some i.val ∧ (r.take i.val (by omega)).Shortest := by
  have hle : levelLE (tenacity M r.last) (tenacity M (r.vertex i)) := by
    cases he : tenacity M r.last with
    | none => simp only [he, levelLE] at hend
    | some e =>
      have het : e ≤ t := by simpa only [he, levelLE] using hend
      cases hv : tenacity M (r.vertex i) with
      | none => trivial
      | some v =>
        have htv : t ≤ v := by simpa only [hv, levelLE] using hi
        change e ≤ v
        omega
  have hhon := (r.limited_bfs_honesty hr i hle).1
  exact ⟨minlevel_of_below_half (r.vertex i) i.val t ((r.honest_iff_level i).1 hhon)
    (by have := i.isLt; omega) hi, hhon⟩

/-- A short shortest path stays in its established current-threshold blossom
after the boundary. Lower confinement and bases at strictly smaller minimum
level suffice; current-threshold confinement is not assumed. -/
theorem short_blossom_suffix_mem (r : AltPath M) (hr : r.Shortest)
    (t O : Nat) (ht : t % 2 = 1) (hlen : r.length < O) (hhalf : 2 * r.length < t)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w)
    (hcurrent : ∀ (v : V) (k : Nat), minlevel M v = some k → k < O →
      tenacity M v = some t → ∃ b, IsBase M v b)
    (d : V) (hd : levelLT (some t) (tenacity M d)) (hbl : Blossom M t d r.last)
    (i j : Fin (r.length + 1)) (hi : r.vertex i = d) (hij : i.val < j.val) :
    Blossom M t d (r.vertex j) := by
  classical
  obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound t d r.last hbl
  have hend : levelLE (tenacity M r.last) (some t) := by simpa only [hs, levelLE] using hst
  have hbase := blossom_baseOnPath t d r.last hbl hd r rfl hr
  obtain ⟨i₀, hi₀, _, hlast⟩ := hbase
  have hii : i₀ = i := r.injective i₀ i (hi₀.trans hi.symm)
  subst i₀
  have htlow : (t - 2) % 2 = 1 := by
    have hrpos : 0 < r.length := by have := j.isLt; omega
    omega
  have hhighlow : ∀ v, levelLT (some t) (tenacity M v) →
      levelLT (some (t - 2)) (tenacity M v) := by
    intro v hv
    cases he : tenacity M v with
    | none => trivial
    | some n =>
      have hn : t < n := by simpa only [he, levelLT] using hv
      change t - 2 < n
      omega
  have hcurrentbase : ∀ a : Fin (r.length + 1), i.val < a.val →
      tenacity M (r.vertex a) = some t → IsBase M (r.vertex a) d := by
    intro a hia hat
    have hage : levelLE (some t) (tenacity M (r.vertex a)) := by rw [hat]; exact Nat.le_refl _
    obtain ⟨hamin, hashort⟩ := r.short_high_minlevel hr t hhalf hend a hage
    obtain ⟨b, hb⟩ := hcurrent (r.vertex a) a.val hamin (by have := a.isLt; omega) hat
    have hb' := hb
    obtain ⟨z, hz, hcommon⟩ := hb'
    have hzt : z = t := Option.some.inj (hz.symm.trans hat)
    subst z
    have hadBase : (r.take a.val (by omega)).BaseOnPath t d := by
      refine ⟨⟨i.val, by change i.val < a.val + 1; omega⟩, hi, hd, ?_⟩
      intro k hk
      exact hlast ⟨k.val, by have := k.isLt; change k.val < a.val + 1 at this; omega⟩ hk
    have hbd := (r.take a.val (by omega)).baseOnPath_unique t b d
      (hcommon _ rfl hashort) hadBase
    exact hbd ▸ hb
  have hpromote : ∀ a : Fin (r.length + 1), i.val ≤ a.val →
      levelLT (some (t - 2)) (tenacity M (r.vertex a)) →
      Blossom M (t - 2) (r.vertex a) (r.vertex j) → Blossom M t d (r.vertex j) := by
    intro a hia hahigh hamem
    by_cases hae : a.val = i.val
    · have hai : a = i := Fin.ext hae
      rw [hai, hi] at hamem
      exact blossom_mono (t - 2) t ht (by omega) d (r.vertex j) hamem
    · have hat : tenacity M (r.vertex a) = some t := by
        have hge := tenacity_ge_of_above_previous_odd (r.vertex a) t ht hahigh
        have hn := hlast a (by omega)
        cases he : tenacity M (r.vertex a) with
        | none => exact False.elim (hn (by rw [he]; trivial))
        | some n =>
          have htn : t ≤ n := by simpa only [he, levelLE] using hge
          have hnt : ¬t < n := by simpa only [he, levelLT] using hn
          exact congrArg some (by omega)
      have had := hcurrentbase a (by omega) hat
      have hmem : Blossom M t d (r.vertex a) := blossom_of_base_le t ht d (r.vertex a) had
        (by rw [hat]; exact Nat.le_refl _)
      exact (blossom_strict_nested_of_base_mem (t - 2) t ht (r.vertex a) d hahigh hmem).1 _ hamem
  have hjlow : ∃ n, tenacity M (r.vertex j) = some n ∧ n ≤ t := by
    have hn := hlast j hij
    cases he : tenacity M (r.vertex j) with
    | none => exact False.elim (hn (by rw [he]; trivial))
    | some n =>
      have hn' : ¬t < n := by simpa only [he, levelLT] using hn
      exact ⟨n, rfl, by omega⟩
  obtain ⟨n, hn, hnt⟩ := hjlow
  by_cases hnt' : n = t
  · have hjt : tenacity M (r.vertex j) = some t := hn.trans (congrArg some hnt')
    exact blossom_of_base_le t ht d (r.vertex j) (hcurrentbase j hij hjt)
      (by rw [hjt]; exact Nat.le_refl _)
  · have hnodd := tenacity_odd M (r.vertex j) n hn
    have hnlower : n ≤ t - 2 := by omega
    have hjlower : levelLE (tenacity M (r.vertex j)) (some (t - 2)) := by
      simpa only [hn, levelLE] using hnlower
    by_cases hnext : ∃ B : Fin (r.length + 1), j.val < B.val ∧
        levelLT (some (t - 2)) (tenacity M (r.vertex B))
    · obtain ⟨B, hjB, hB⟩ := hnext
      obtain ⟨a, hia, haj, ha, hamem⟩ := r.low_vertex_between_highs (t - 2) htlow hexists hconf
        i j B hij hjB (by rw [hi]; exact hhighlow d hd) hB hjlower (by
          intro k _ hk
          exact (r.short_high_minlevel hr t hhalf hend k
            (tenacity_ge_of_above_previous_odd (r.vertex k) t ht hk)).1)
      exact hpromote a hia ha hamem
    · have hslower : s ≤ t - 2 := by
        by_cases hsl : s ≤ t - 2
        · exact hsl
        · have hlastHigh : levelLT (some (t - 2)) (tenacity M r.last) := by
            simpa only [hs, levelLT] using Nat.lt_of_not_ge hsl
          have hjlt : j.val < r.length := by
            by_cases hje : j.val = r.length
            · have hjend : r.vertex j = r.last := congrArg r.vertex (Fin.ext hje)
              rw [hjend, hs] at hn
              have hsn := Option.some.inj hn
              omega
            · have := j.isLt; omega
          exact False.elim (hnext ⟨⟨r.length, by omega⟩, hjlt, hlastHigh⟩)
      obtain ⟨a, hahigh, hamem⟩ := blossom_cover_of_base_existence (t - 2) htlow hexists r.last s hs hslower
      obtain ⟨A, hA, _, _, _, _⟩ := blossom_on_shortest (t - 2) a r.last hamem r rfl hr
      have hAj : A.val < j.val := by
        by_cases hAj : A.val < j.val
        · exact hAj
        · by_cases he : A.val = j.val
          · have hAj' : A = j := Fin.ext he
            rw [hAj'] at hA
            have hh : levelLT (some (t - 2)) (tenacity M (r.vertex j)) := hA.symm ▸ hahigh
            rw [hn] at hh
            change t - 2 < n at hh
            omega
          · exact False.elim (hnext ⟨A, by omega, hA.symm ▸ hahigh⟩)
      have hiA : i.val ≤ A.val := by
        obtain ⟨K, hK, _, hKlast⟩ := blossom_baseOnPath (t - 2) a r.last hamem hahigh r rfl hr
        have hKA : K = A := r.injective K A (hK.trans hA.symm)
        subst K
        by_cases hAi : A.val < i.val
        · exact False.elim (hKlast i hAi (by rw [hi]; exact hhighlow d hd))
        · omega
      exact hpromote A hiA (hA.symm ▸ hahigh)
        (by rw [hA]; exact r.blossom_suffix_mem (t - 2) a r.last hamem hahigh hconf rfl hr A j hA hAj)

end MaximumMatching.AltPath
