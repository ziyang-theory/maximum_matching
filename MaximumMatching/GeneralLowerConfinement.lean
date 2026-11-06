import MaximumMatching.GeneralShortConfinement
import MaximumMatching.GeneralBlossomJoin
import MaximumMatching.MinimumRelative

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
