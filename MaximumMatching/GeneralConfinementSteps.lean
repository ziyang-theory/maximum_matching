import MaximumMatching.BaseRerouting
import MaximumMatching.GeneralBaseStructure
import MaximumMatching.GeneralPathGeometry
import MaximumMatching.RelativePaths

section GeneralShortConfinement

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

end GeneralShortConfinement

section GeneralLowerConfinement

/-! Confinement at the current cutoff when the endpoint has lower tenacity.
Its lower blossom supplies the final segment. The prefix to that lower
boundary has minimum level, so current short-path confinement applies there. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Lower-tenacity members of a current blossom have all their shortest paths
confined after the current boundary. Only lower confinement and actual bases
at the current tenacity are used. -/
theorem lower_endpoint_blossom_suffix_mem (r : AltPath M) (hr : r.Shortest)
    (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w)
    (hcurrent : ∀ v : V, tenacity M v = some t → ∃ b, IsBase M v b)
    (d : V) (hd : levelLT (some t) (tenacity M d)) (hbl : Blossom M t d r.last)
    (s : Nat) (hs : tenacity M r.last = some s) (hst : s < t)
    (i j : Fin (r.length + 1)) (hi : r.vertex i = d) (hij : i.val < j.val) :
    Blossom M t d (r.vertex j) := by
  have hsodd := tenacity_odd M r.last s hs
  have htlow : (t - 2) % 2 = 1 := by omega
  have hslower : s ≤ t - 2 := by omega
  obtain ⟨a, hahigh, hamem⟩ := blossom_cover_of_base_existence (t - 2) htlow hexists r.last s hs hslower
  obtain ⟨A, hA, hAe, _, hAmin, hAshort⟩ := blossom_on_shortest (t - 2) a r.last hamem r rfl hr
  have hdlow : levelLT (some (t - 2)) (tenacity M d) := by
    cases he : tenacity M d with
    | none => trivial
    | some n =>
      have hn : t < n := by simpa only [he, levelLT] using hd
      change t - 2 < n
      omega
  have hiA : i.val ≤ A.val := by
    obtain ⟨K, hK, _, hKlast⟩ := blossom_baseOnPath (t - 2) a r.last hamem hahigh r rfl hr
    have hKA : K = A := r.injective K A (hK.trans hA.symm)
    subst K
    by_cases hAi : A.val < i.val
    · exact False.elim (hKlast i hAi (by rw [hi]; exact hdlow))
    · omega
  have hbase := blossom_baseOnPath t d r.last hbl hd r rfl hr
  have hpromote : a = d ∨ Blossom M t d a := by
    by_cases hAi : A.val = i.val
    · exact Or.inl (hA.symm.trans ((congrArg r.vertex (Fin.ext hAi)).trans hi))
    · have hAt : tenacity M a = some t := by
        obtain ⟨n, hn, hnt⟩ := blossom_suffix_tenacity_bound t d r.last hbl hd r rfl hr i A hi (by omega)
        have hge := tenacity_ge_of_above_previous_odd a t ht hahigh
        rw [hA] at hn
        have htn : t ≤ n := by simpa only [hn, levelLE] using hge
        exact hn.trans (congrArg some (by omega))
      obtain ⟨b, hb⟩ := hcurrent a hAt
      have hcomm := (isBase_iff_common t hAt).1 hb
      have hprefixbase := r.baseOnPath_take_after t d hbase i A hi hiA
      have hbd := (r.take A.val (by omega)).baseOnPath_unique t b d
        (hcomm _ hA hAshort) hprefixbase
      exact Or.inr (blossom_of_base_le t ht d a (hbd ▸ hb) (by rw [hAt]; exact Nat.le_refl _))
  by_cases hAj : A.val < j.val
  · have hjlower := r.blossom_suffix_mem (t - 2) a r.last hamem hahigh hconf rfl hr A j hA hAj
    rcases hpromote with had | had
    · rw [had] at hjlower
      exact blossom_mono (t - 2) t ht (by omega) d (r.vertex j) hjlower
    · exact (blossom_strict_nested_of_base_mem (t - 2) t ht a d hahigh had).1 _ hjlower
  · have hAi : i.val < A.val := by omega
    have had : Blossom M t d a := by
      rcases hpromote with had | had
      · have hindex := congrArg Fin.val (r.injective A i (hA.trans (had.trans hi.symm)))
        omega
      · exact had
    have hAt : tenacity M a = some t := by
      obtain ⟨n, hn, hnt⟩ := blossom_tenacity_bound t d a had
      have hge := tenacity_ge_of_above_previous_odd a t ht hahigh
      have htn : t ≤ n := by simpa only [hn, levelLE] using hge
      exact hn.trans (congrArg some (by omega))
    have hhalf : 2 * A.val < t := by
      have hbound := twice_minlevel_le_tenacity a A.val t hAmin hAt
      omega
    let p := r.take A.val (by omega)
    have hpbl : Blossom M t d p.last := by change Blossom M t d (r.vertex A); rw [hA]; exact had
    exact p.short_blossom_suffix_mem hAshort t (A.val + 1) ht (by change A.val < A.val + 1; omega)
      hhalf hexists hconf (by intro v k _ _ hv; exact hcurrent v hv) d hd hpbl
      ⟨i.val, by change i.val < A.val + 1; omega⟩
      ⟨j.val, by change j.val < A.val + 1; omega⟩ hi hij

end MaximumMatching.AltPath

namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The relative-path form for every lower-tenacity member of the current
blossom, including members whose current boundary is an iterated base. -/
theorem lower_endpoint_blossom_relative_confined
    (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w)
    (hcurrent : ∀ v : V, tenacity M v = some t → ∃ b, IsBase M v b)
    (b v : V) (hb : levelLT (some t) (tenacity M b)) (hv : Blossom M t b v)
    (s : Nat) (hs : tenacity M v = some s) (hst : s < t)
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v) :
    ∀ w, q.Contains w → w = b ∨ Blossom M t b w := by
  obtain ⟨r, hrv, hr, _⟩ := finite_tenacity_shortest_parity v s 0 hs
  obtain ⟨i, hib, hie, _, _, hip⟩ := blossom_on_shortest t b v hv r hrv hr
  let p := r.take i.val (by omega)
  have hp : p.Shortest := hip
  have hpe : p.length % 2 = 0 := hie
  have hpb : p.last = b := hib
  let hdis := blossom_relative_avoids_prefix t b v hv hb p hp hpe hpb q hq hqb hqv
  let joined := p.appendSegment q hpe (hpb.trans hqb.symm) hdis
  have hjshort : joined.Shortest := blossom_append_relative_shortest t b v hv hb p hp hpe hpb q hq hqb hqv
  have hjend : joined.last = v := (p.appendSegment_last q hpe (hpb.trans hqb.symm) hdis).trans hqv
  let baseIndex : Fin (joined.length + 1) := ⟨p.length, by change p.length < p.length + q.length + 1; omega⟩
  have hbase : joined.vertex baseIndex = b := by
    change (if h : p.length ≤ p.length then p.vertex ⟨p.length, _⟩ else _) = b
    simpa only [Nat.le_refl, dite_true, AltPath.last] using hpb
  intro w hw
  obtain ⟨j, rfl⟩ := hw
  by_cases hj : j.val = 0
  · have hj0 : j = ⟨0, by omega⟩ := Fin.ext hj
    exact Or.inl (by rw [hj0]; exact hqb)
  · apply Or.inr
    have hc := joined.lower_endpoint_blossom_suffix_mem hjshort t ht hexists hconf hcurrent b hb
      (by rw [hjend]; exact hv) s (by rw [hjend]; exact hs) hst baseIndex
      ⟨p.length + j.val, by change p.length + j.val < p.length + q.length + 1; omega⟩
      hbase (by change p.length < p.length + j.val; omega)
    rwa [p.appendSegment_vertex_suffix q hpe (hpb.trans hqb.symm) hdis j] at hc

end MaximumMatching

end GeneralLowerConfinement

section GeneralLongLocalization

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

end GeneralLongLocalization

section GeneralBlossomFirstEntry

/-! Confinement after the first entry into an established blossom on a
shortest path ending at its boundary. Replacing the reversed tail by an
arbitrary shortest relative path proves the actual tail shortest. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Reverse the suffix of an odd path. Its first edge is unmatched, regardless
of the parity of the cut index. -/
def reverseOddTail (p : AltPath M) (hpo : p.length % 2 = 1)
    (D : Fin (p.length + 1)) : AltSegment M where
  length := p.length - D.val
  vertex i := p.vertex ⟨p.length - i.val, by omega⟩
  injective := by
    intro i j he
    have hh := congrArg Fin.val (p.injective _ _ he)
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    change p.length - i.val = p.length - j.val at hh
    omega
  adjacent := by
    intro i
    have hh := G.symm (p.adjacent ⟨p.length - (i.val + 1), by omega⟩)
    simpa only [show p.length - (i.val + 1) + 1 = p.length - i.val by omega] using hh
  alternating := by
    intro i
    have hh := p.alternating ⟨p.length - (i.val + 1), by omega⟩
    have hindex : p.length - (i.val + 1) + 1 = p.length - i.val := by omega
    have hpar : (p.length - (i.val + 1)) % 2 = i.val % 2 := by omega
    constructor
    · intro hm
      have hm' := M.symm hm
      have ha := hh.1 (by simpa only [hindex] using hm')
      simpa only [hpar] using ha
    · intro hi
      have hm := M.symm (hh.2 (by simpa only [hpar] using hi))
      simpa only [hindex] using hm

@[simp] theorem reverseOddTail_first (p : AltPath M) (hpo) (D) :
    (p.reverseOddTail hpo D).first = p.last := by
  simp only [reverseOddTail, AltSegment.first, Nat.sub_zero]
  rfl

@[simp] theorem reverseOddTail_last (p : AltPath M) (hpo) (D) :
    (p.reverseOddTail hpo D).last = p.vertex D := by
  change p.vertex ⟨p.length - (p.length - D.val), _⟩ = p.vertex D
  congr 1
  apply Fin.ext
  have := D.isLt
  change p.length - (p.length - D.val) = D.val
  omega

/-- The first entry into an established blossom occurs across an unmatched
edge, hence at an odd path index. Matching closure excludes an even entry. -/
theorem first_blossom_entry_odd (p : AltPath M) (t : Nat) (b : V)
    (D : Fin (p.length + 1)) (hDmem : Blossom M t b (p.vertex D))
    (hfirst : ∀ a : Fin (p.length + 1), a.val < D.val → ¬Blossom M t b (p.vertex a)) :
    D.val % 2 = 1 := by
  have hDpos : 0 < D.val := by
    by_cases hz : D.val = 0
    · have hD : D = ⟨0, by omega⟩ := Fin.ext hz
      let q := AltPath.trivial M p.first p.start_free
      have hq : q.Shortest := by
        change IsShortest M 0 p.first 0
        exact ⟨⟨q, rfl, rfl, rfl⟩, fun _ _ => Nat.zero_le _⟩
      have hmem : Blossom M t b q.last := by
        change Blossom M t b p.first
        simpa only [hD, first] using hDmem
      obtain ⟨i, _, _, hi, _, _⟩ := blossom_on_shortest t b q.last hmem q rfl hq
      change i.val < 0 at hi
      omega
    · omega
  by_cases he : D.val % 2 = 0
  · have hm := p.mate_previous D.val (by omega) hDpos he
    have hprev := (matched_blossom_iff hm t b).1 hDmem
    exact False.elim (hfirst ⟨D.val - 1, by omega⟩ (by change D.val - 1 < D.val; omega) hprev)
  · omega

/-- At the first blossom entry, the actual reversed tail is a shortest relative
path. Consequently every original tail vertex lies in the blossom or is its
boundary. The lower confinement premise is used only for already-established
shortest relative paths. -/
theorem first_entry_reverse_tail_shortest (p : AltPath M) (hp : p.Shortest)
    (hpo : p.length % 2 = 1) (t : Nat)
    (hc : levelLT (some t) (tenacity M p.last))
    (hconf : ∀ (v : V), Blossom M t p.last v →
      ∀ q : AltSegment M, q.Shortest → q.first = p.last → q.last = v →
        ∀ w, q.Contains w → w = p.last ∨ Blossom M t p.last w)
    (D : Fin (p.length + 1)) (hDo : D.val % 2 = 1)
    (hDmem : Blossom M t p.last (p.vertex D))
    (hfirst : ∀ a : Fin (p.length + 1), a.val < D.val → ¬Blossom M t p.last (p.vertex a)) :
    (p.reverseOddTail hpo D).Shortest ∧
      ∀ j : Fin (p.length + 1), D.val ≤ j.val →
        p.vertex j = p.last ∨ Blossom M t p.last (p.vertex j) := by
  have hDlt : D.val < p.length := by
    by_cases he : D.val = p.length
    · have hD : D = ⟨p.length, by omega⟩ := Fin.ext he
      rw [hD] at hDmem
      exact False.elim (blossom_excludes_base t p.last hc hDmem)
    · have := D.isLt
      omega
  obtain ⟨s, hvs, _⟩ := blossom_tenacity_bound t p.last (p.vertex D) hDmem
  obtain ⟨r, hrD, hr, hre⟩ := finite_tenacity_shortest_parity (p.vertex D) s 0 hvs
  obtain ⟨i, hie, hi, _, hq⟩ := blossom_shortest_relative t p.last (p.vertex D) hDmem hc r hrD hr
  let q := r.segment i.val (by omega) hie
  have hqf : q.first = p.last := (r.segment_first _ _ _).trans hi
  have hql : q.last = p.vertex D := (r.segment_last _ _ _).trans hrD
  have hqe : q.length % 2 = 0 := by
    change (r.length - i.val) % 2 = 0
    omega
  have hdis : (p.take D.val (by omega)).SegmentReverseDisjoint q 0 q.length := by
    intro a j _ hj he
    have haved : a.val ≤ D.val := by have := a.isLt; change a.val < D.val + 1 at this; omega
    change p.vertex ⟨a.val, _⟩ = q.vertex j at he
    by_cases had : a.val = D.val
    · have ha : (⟨a.val, by omega⟩ : Fin (p.length + 1)) = D := Fin.ext had
      rw [ha, ← hql] at he
      have hje := congrArg Fin.val (q.injective ⟨q.length, by omega⟩ j he)
      change q.length = j.val at hje
      omega
    · rcases hconf (p.vertex D) hDmem q hq hqf hql (q.vertex j) ⟨j, rfl⟩ with hcj | hmem
      · rw [hcj] at he
        have hae := congrArg Fin.val (p.injective ⟨a.val, by omega⟩ ⟨p.length, by omega⟩ he)
        change a.val = p.length at hae
        omega
      · exact hfirst ⟨a.val, by omega⟩ (by change a.val < D.val; omega) (he ▸ hmem)
  let z := (p.take D.val (by omega)).spliceReverseSegment q 0 q.length
    (by omega) (Nat.le_refl _) hql.symm hDo hqe hdis
  have hzlast : z.last = p.last := (spliceReverseSegment_last _ _ _ _ _ _ _ _ _ _).trans hqf
  have hzlen : z.length = D.val + q.length := by
    change D.val + (q.length - 0) = _
    omega
  have hbound : p.length ≤ z.length := hp.2 z.length ⟨z, hzlast, rfl, by rw [hzlen]; omega⟩
  let a := p.reverseOddTail hpo D
  have haf : a.first = p.last := p.reverseOddTail_first hpo D
  have hal : a.last = p.vertex D := p.reverseOddTail_last hpo D
  have hae : a.length % 2 = 0 := by change (p.length - D.val) % 2 = 0; omega
  have hqa : q.length ≤ a.length := hq a (haf.trans hqf.symm) (hal.trans hql.symm) (hae.trans hqe.symm)
  have hlen : a.length = q.length := by
    change p.length - D.val = q.length
    change q.length ≤ p.length - D.val at hqa
    rw [hzlen] at hbound
    omega
  have hashort : a.Shortest := by
    intro s hsf hsl hspar
    rw [hlen]
    exact hq s (hsf.trans (haf.trans hqf.symm)) (hsl.trans (hal.trans hql.symm))
      (hspar.trans (hae.trans hqe.symm))
  refine ⟨hashort, ?_⟩
  intro j hDj
  apply hconf (p.vertex D) hDmem a hashort haf hal (p.vertex j)
  refine ⟨⟨p.length - j.val, by change p.length - j.val < p.length - D.val + 1; omega⟩, ?_⟩
  change p.vertex ⟨p.length - (p.length - j.val), _⟩ = p.vertex j
  congr 1
  apply Fin.ext
  have := j.isLt
  change p.length - (p.length - j.val) = j.val
  omega

private theorem least_member_index (P : Nat → Prop) (h : ∃ k, P k) :
    ∃ k, P k ∧ ∀ l, l < k → ¬P l := by
  classical
  obtain ⟨k, hk⟩ := h
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hs : ∃ l, l < k ∧ P l
    · obtain ⟨l, hl, hp⟩ := hs
      exact ih l hl hp
    · exact ⟨k, hk, fun l hl hp => hs ⟨l, hl, hp⟩⟩

/-- Select the first actual blossom entry and derive its odd parity. -/
theorem first_blossom_entry (p : AltPath M) (t : Nat) (b : V)
    (hmem : ∃ i : Fin (p.length + 1), Blossom M t b (p.vertex i)) :
    ∃ D : Fin (p.length + 1), D.val % 2 = 1 ∧ Blossom M t b (p.vertex D) ∧
      ∀ a : Fin (p.length + 1), a.val < D.val → ¬Blossom M t b (p.vertex a) := by
  let P := fun k => ∃ i : Fin (p.length + 1), i.val = k ∧ Blossom M t b (p.vertex i)
  obtain ⟨i, hi⟩ := hmem
  obtain ⟨k, ⟨D, hD, hmem⟩, hleast⟩ := least_member_index P ⟨i.val, i, rfl, hi⟩
  have hfirst : ∀ a : Fin (p.length + 1), a.val < D.val → ¬Blossom M t b (p.vertex a) := by
    intro a ha hmem
    exact hleast a.val (by omega) ⟨a, rfl, hmem⟩
  exact ⟨D, p.first_blossom_entry_odd t b D hmem hfirst, hmem, hfirst⟩

/-- Any actual blossom visit on an odd shortest path ending at the boundary
supplies a concrete first index and a confined actual suffix. -/
theorem exists_first_entry_confined_tail (p : AltPath M) (hp : p.Shortest)
    (hpo : p.length % 2 = 1) (t : Nat)
    (hc : levelLT (some t) (tenacity M p.last))
    (hconf : ∀ (v : V), Blossom M t p.last v →
      ∀ q : AltSegment M, q.Shortest → q.first = p.last → q.last = v →
        ∀ w, q.Contains w → w = p.last ∨ Blossom M t p.last w)
    (hmem : ∃ i : Fin (p.length + 1), Blossom M t p.last (p.vertex i)) :
    ∃ D : Fin (p.length + 1), D.val % 2 = 1 ∧ Blossom M t p.last (p.vertex D) ∧
      (∀ a : Fin (p.length + 1), a.val < D.val → ¬Blossom M t p.last (p.vertex a)) ∧
      (p.reverseOddTail hpo D).Shortest ∧
      ∀ j : Fin (p.length + 1), D.val ≤ j.val →
        p.vertex j = p.last ∨ Blossom M t p.last (p.vertex j) := by
  obtain ⟨D, hDo, hDmem, hfirst⟩ := p.first_blossom_entry t p.last hmem
  obtain ⟨hshort, htail⟩ := p.first_entry_reverse_tail_shortest hp hpo t hc hconf D hDo hDmem hfirst
  exact ⟨D, hDo, hDmem, hfirst, hshort, htail⟩

/-- The first entry's evenlevel is exactly the boundary's minimum level plus
the length of the actual reversed tail. No path-index honesty is assumed. -/
theorem first_entry_evenlevel (p : AltPath M) (hpo : p.length % 2 = 1)
    (t C : Nat) (hc : levelLT (some t) (tenacity M p.last))
    (hcmin : minlevel M p.last = some C)
    (D : Fin (p.length + 1)) (hDo : D.val % 2 = 1)
    (hDmem : Blossom M t p.last (p.vertex D))
    (hshort : (p.reverseOddTail hpo D).Shortest) :
    evenlevel M (p.vertex D) = some (C + (p.length - D.val)) := by
  have hce : evenlevel M p.last = some C :=
    (minlevel_eq_even_of_outer p.last (blossom_outer t p.last (p.vertex D) hDmem)).symm.trans hcmin
  obtain ⟨q, hqc, hqC, hqe⟩ := ((level_eq_some_iff M 0 p.last C).1 hce).1
  have hqshort : q.Shortest := by
    simpa only [Shortest, hqc, hqC, hqe] using (level_eq_some_iff M 0 p.last C).1 hce
  obtain ⟨s, hds, _⟩ := blossom_tenacity_bound t p.last (p.vertex D) hDmem
  let r := p.reverseOddTail hpo D
  have hrf : r.first = p.last := p.reverseOddTail_first hpo D
  have hrl : r.last = p.vertex D := p.reverseOddTail_last hpo D
  have hre : r.length % 2 = 0 := by change (p.length - D.val) % 2 = 0; omega
  have hl := (blossom_relative_length_formula t p.last (p.vertex D) hDmem hc
    q hqshort (by omega) hqc r hshort hrf hrl s hds).1
  rw [hre, hqC] at hl
  change IsShortest M 0 (p.vertex D) (C + (p.length - D.val)) at hl
  exact (level_eq_some_iff M 0 (p.vertex D) (C + (p.length - D.val))).2
    hl

end MaximumMatching.AltPath

end GeneralBlossomFirstEntry

section GeneralFirstEntryPrefix

/-! The prefix just before a first lower-blossom entry is honest. A shorter
even prefix would create an edge below the lower cutoff between distinct
boundary blossoms, contradicted by the proved small-edge closure. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Once the actual reversed first-entry tail is shortest, its preceding
prefix is shortest too. No honesty or classification is supplied for that
prefix; the low case follows from the small-edge cut closure theorem. -/
theorem first_entry_prefix_honest (p : AltPath M) (hp : p.Shortest)
    (hpo : p.length % 2 = 1) (t : Nat) (hpt : tenacity M p.last = some t)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w)
    (D : Fin (p.length + 1)) (hDo : D.val % 2 = 1)
    (hDmem : Blossom M (t - 2) p.last (p.vertex D))
    (hfirst : ∀ a : Fin (p.length + 1), a.val < D.val → ¬Blossom M (t - 2) p.last (p.vertex a))
    (htail : (p.reverseOddTail hpo D).Shortest) :
    p.BFSHonest ⟨D.val - 1, by omega⟩ := by
  let Z : Fin (p.length + 1) := ⟨D.val - 1, by omega⟩
  have hZe : Z.val % 2 = 0 := by change (D.val - 1) % 2 = 0; omega
  by_cases hhigh : levelLE (some t) (tenacity M (p.vertex Z))
  · exact (p.limited_bfs_honesty hp Z (by rw [hpt]; exact hhigh)).1
  · have hzt : ∃ s, tenacity M (p.vertex Z) = some s ∧ s < t := by
      cases hs : tenacity M (p.vertex Z) with
      | none => exact False.elim (hhigh (by rw [hs]; trivial))
      | some s =>
        refine ⟨s, rfl, ?_⟩
        have hn : ¬t ≤ s := by simpa only [hs, levelLE] using hhigh
        omega
    obtain ⟨s, hzs, hst⟩ := hzt
    have htodd := tenacity_odd M p.last t hpt
    have hsodd := tenacity_odd M (p.vertex Z) s hzs
    have hslow : s ≤ t - 2 := by omega
    have htlow : (t - 2) % 2 = 1 := by
      by_cases hthree : 3 ≤ t
      · omega
      · have htone : t = 1 := by omega
        rw [htone] at hDmem
        exact False.elim hDmem
    have hchigh : levelLT (some (t - 2)) (tenacity M p.last) := by
      rw [hpt]
      change t - 2 < t
      omega
    obtain ⟨b, hb, hbz⟩ := blossom_cover_of_base_existence (t - 2) htlow hexists
      (p.vertex Z) s hzs hslow
    obtain ⟨e, o, hce, hco, _, _, hsum⟩ := finite_levels_of_tenacity p.last t hpt
    have hcop : oddlevel M p.last = some p.length :=
      (level_eq_some_iff M 1 p.last p.length).2 (by simpa only [Shortest, hpo] using hp)
    have hop : o = p.length := Option.some.inj (hco.symm.trans hcop)
    have hcmin : minlevel M p.last = some e :=
      (minlevel_eq_even_of_outer p.last (blossom_outer (t - 2) p.last (p.vertex D) hDmem)).trans hce
    have hde := p.first_entry_evenlevel hpo (t - 2) e hchigh hcmin D hDo hDmem htail
    have hden : e + (p.length - D.val) = t - D.val := by have := D.isLt; omega
    rw [hden] at hde
    obtain ⟨f, hzf, hfb⟩ := p.prefix_level_bound Z
    have hze : evenlevel M (p.vertex Z) = some f := by simpa only [hZe] using hzf
    by_cases hfe : f = D.val - 1
    · exact (p.honest_iff_level Z).2 (by simpa only [hfe, Z] using hzf)
    · have hflt : f < D.val - 1 := by change f ≤ D.val - 1 at hfb; omega
      have hadj : G.Adj (p.vertex Z) (p.vertex D) := by
        have hh := p.adjacent ⟨D.val - 1, by omega⟩
        simpa only [show D.val - 1 + 1 = D.val by omega, Z] using hh
      have hunm : M.mate (p.vertex Z) ≠ some (p.vertex D) := by
        intro hm
        have hodd := (p.alternating ⟨D.val - 1, by omega⟩).1
          (by simpa only [show D.val - 1 + 1 = D.val by omega, Z] using hm)
        change (D.val - 1) % 2 = 1 at hodd
        omega
      have hbceq := blossom_unmatched_edge_boundary_eq (t - 2) b p.last (p.vertex Z) (p.vertex D)
        hbz hDmem hb hchigh hconf hadj hunm f (t - D.val) hze hde (by
          have := D.isLt
          have hfp := level_parity M 0 (p.vertex Z) f hze
          omega)
      rw [hbceq] at hbz
      exact False.elim (hfirst Z (by change D.val - 1 < D.val; omega) hbz)

end MaximumMatching.AltPath

end GeneralFirstEntryPrefix

section GeneralConfinement

/-! The confinement step at an arbitrary odd tenacity. Induction on actual
shortest-path length handles honest prefixes. At a dishonest predecessor,
the first entry into the endpoint's lower blossom supplies a shorter honest
prefix and a confined tail. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Current-tenacity shortest paths stay in their actual boundary blossom.
The only confinement premise is at the preceding odd cutoff. -/
theorem current_blossom_suffix_mem (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w)
    (hcurrent : ∀ v : V, tenacity M v = some t → ∃ b, IsBase M v b)
    (r : AltPath M) (hr : r.Shortest) (hrt : tenacity M r.last = some t)
    (b : V) (hb : levelLT (some t) (tenacity M b)) (hbl : Blossom M t b r.last)
    (i j : Fin (r.length + 1)) (hi : r.vertex i = b) (hij : i.val < j.val) :
    Blossom M t b (r.vertex j) := by
  have hall : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b := by
    intro v s hs hst
    by_cases he : s = t
    · exact hcurrent v (he ▸ hs)
    · have hsodd := tenacity_odd M v s hs
      exact hexists v s hs (by omega)
  have aux : ∀ L (p : AltPath M), p.length = L → p.Shortest → tenacity M p.last = some t →
      ∀ (b : V), levelLT (some t) (tenacity M b) → Blossom M t b p.last →
      ∀ (i j : Fin (p.length + 1)), p.vertex i = b → i.val < j.val →
        Blossom M t b (p.vertex j) := by
    intro L
    induction L using Nat.strongRecOn with
    | ind L ih =>
      intro p hpL hp hpt b hb hbl i j hi hij
      have hbase := blossom_baseOnPath t b p.last hbl hb p rfl hp
      by_cases hjlast : j.val = p.length
      · have hj : j = ⟨p.length, by omega⟩ := Fin.ext hjlast
        rw [hj]
        exact hbl
      have hjlt : j.val < p.length := by have := j.isLt; omega
      have hpos : 0 < p.length := by omega
      have hprefix (K : Fin (p.length + 1)) (hK : K.val < p.length)
          (hshort : (p.take K.val (by omega)).Shortest)
          (hjK : j.val ≤ K.val) : Blossom M t b (p.vertex j) := by
        have hiK : i.val < K.val := by omega
        obtain ⟨s, hs, hst⟩ := blossom_suffix_tenacity_bound t b p.last hbl hb p rfl hp i K hi hiK
        let a := p.take K.val (by omega)
        have habase := p.baseOnPath_take_after t b hbase i K hi (by omega)
        have hamem : Blossom M t b a.last := a.blossom_of_shortest_base hshort t ht hall b habase
          (by change levelLE (tenacity M (p.vertex K)) (some t); rw [hs]; exact hst)
        by_cases he : s = t
        · exact ih K.val (by omega) a rfl hshort (by change tenacity M (p.vertex K) = some t; simpa only [he] using hs)
            b hb hamem ⟨i.val, by change i.val < K.val + 1; omega⟩
            ⟨j.val, by change j.val < K.val + 1; omega⟩ hi hij
        · exact a.lower_endpoint_blossom_suffix_mem hshort t ht hexists hconf hcurrent b hb hamem
            s hs (by omega) ⟨i.val, by change i.val < K.val + 1; omega⟩
            ⟨j.val, by change j.val < K.val + 1; omega⟩ hi hij
      let pred : Fin (p.length + 1) := ⟨p.length - 1, by omega⟩
      by_cases hpred : p.BFSHonest pred
      · exact hprefix pred (by change p.length - 1 < p.length; omega) hpred
          (by change j.val ≤ p.length - 1; omega)
      · obtain ⟨hpo, houter⟩ := p.dishonest_last_predecessor_outer hp t hpt hpos hpred
        obtain ⟨s, hs, hst⟩ := blossom_suffix_tenacity_bound t b p.last hbl hb p rfl hp i pred hi
          (by change i.val < p.length - 1; omega)
        have hst' : s < t := by
          by_cases he : s = t
          · have hhon := (p.limited_bfs_honesty hp pred (by rw [hpt, hs, he]; exact Nat.le_refl _)).1
            exact False.elim (hpred hhon)
          · omega
        have hsodd := tenacity_odd M (p.vertex pred) s hs
        have hcutodd : (t - 2) % 2 = 1 := by omega
        have hclow : levelLT (some (t - 2)) (tenacity M p.last) := by
          rw [hpt]
          change t - 2 < t
          omega
        have hmember := (p.dishonest_outer_predecessor_base hp hpo houter t s hpt hs hst'
          (hexists (p.vertex pred) s hs (by omega)) hpred).2
        obtain ⟨D, hDo, hDmem, hfirst, htailshort, htail⟩ := p.exists_first_entry_confined_tail hp hpo
          (t - 2) hclow (by intro v hv q hq hqf hql; exact hconf p.last v hv hclow q hq hqf hql)
          ⟨pred, hmember⟩
        have htailcurrent : ∀ k : Fin (p.length + 1), D.val ≤ k.val → Blossom M t b (p.vertex k) := by
          intro k hDk
          rcases htail k hDk with he | hm
          · rw [he]
            exact hbl
          · exact (blossom_strict_nested_of_base_mem (t - 2) t ht p.last b hclow hbl).1 _ hm
        have hiD : i.val < D.val := by
          by_cases hDi : D.val ≤ i.val
          · exact False.elim (blossom_excludes_base t b hb (hi ▸ htailcurrent i hDi))
          · omega
        by_cases hDj : D.val ≤ j.val
        · exact htailcurrent j hDj
        · have hhon := p.first_entry_prefix_honest hp hpo t hpt hexists hconf D hDo hDmem hfirst htailshort
          exact hprefix ⟨D.val - 1, by have := D.isLt; omega⟩
            (by change D.val - 1 < p.length; have := D.isLt; omega) hhon
            (by change j.val ≤ D.val - 1; omega)
  exact aux r.length r rfl hr hrt b hb hbl i j hi hij

/-- Global shortest-path confinement for every member of the current blossom,
combining the current-tenacity and lower-tenacity endpoint cases. -/
theorem general_blossom_suffix_mem_of_current (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w)
    (hcurrent : ∀ v : V, tenacity M v = some t → ∃ b, IsBase M v b)
    (r : AltPath M) (hr : r.Shortest)
    (b : V) (hb : levelLT (some t) (tenacity M b)) (hbl : Blossom M t b r.last)
    (i j : Fin (r.length + 1)) (hi : r.vertex i = b) (hij : i.val < j.val) :
    Blossom M t b (r.vertex j) := by
  obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound t b r.last hbl
  by_cases he : s = t
  · exact current_blossom_suffix_mem t ht hexists hconf hcurrent r hr
      (he ▸ hs) b hb hbl i j hi hij
  · exact r.lower_endpoint_blossom_suffix_mem hr t ht hexists hconf hcurrent b hb hbl
      s hs (by omega) i j hi hij

end MaximumMatching.AltPath

namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The full current-cutoff relative confinement step. Every shortest relative
path is joined to a shortest even boundary prefix using derived disjointness. -/
theorem general_blossom_relative_confined_of_current
    (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w)
    (hcurrent : ∀ v : V, tenacity M v = some t → ∃ b, IsBase M v b)
    (b v : V) (hv : Blossom M t b v) (hb : levelLT (some t) (tenacity M b))
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v) :
    ∀ w, q.Contains w → w = b ∨ Blossom M t b w := by
  obtain ⟨s, hs, _⟩ := blossom_tenacity_bound t b v hv
  obtain ⟨r, hrv, hr, _⟩ := finite_tenacity_shortest_parity v s 0 hs
  obtain ⟨i, hib, hie, _, _, hip⟩ := blossom_on_shortest t b v hv r hrv hr
  let p := r.take i.val (by omega)
  have hp : p.Shortest := hip
  have hpe : p.length % 2 = 0 := hie
  have hpb : p.last = b := hib
  let hdis := blossom_relative_avoids_prefix t b v hv hb p hp hpe hpb q hq hqb hqv
  let joined := p.appendSegment q hpe (hpb.trans hqb.symm) hdis
  have hjshort : joined.Shortest := blossom_append_relative_shortest t b v hv hb p hp hpe hpb q hq hqb hqv
  have hjend : joined.last = v := (p.appendSegment_last q hpe (hpb.trans hqb.symm) hdis).trans hqv
  let baseIndex : Fin (joined.length + 1) := ⟨p.length, by change p.length < p.length + q.length + 1; omega⟩
  have hbase : joined.vertex baseIndex = b := by
    change (if h : p.length ≤ p.length then p.vertex ⟨p.length, _⟩ else _) = b
    simpa only [Nat.le_refl, dite_true, AltPath.last] using hpb
  intro w hw
  obtain ⟨j, rfl⟩ := hw
  by_cases hj : j.val = 0
  · have hj0 : j = ⟨0, by omega⟩ := Fin.ext hj
    exact Or.inl (by rw [hj0]; exact hqb)
  · apply Or.inr
    have hc := AltPath.general_blossom_suffix_mem_of_current t ht hexists hconf hcurrent joined hjshort b hb
      (by rw [hjend]; exact hv) baseIndex
      ⟨p.length + j.val, by change p.length + j.val < p.length + q.length + 1; omega⟩
      hbase (by change p.length < p.length + j.val; omega)
    rwa [p.appendSegment_vertex_suffix q hpe (hpb.trans hqb.symm) hdis j] at hc

end MaximumMatching

end GeneralConfinement
