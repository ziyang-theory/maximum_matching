import MaximumMatching.BlossomStructure
import MaximumMatching.BridgeBuckets
import MaximumMatching.GeneralBaseStructure
import MaximumMatching.MinScan
import MaximumMatching.MinimumBaseStructure
import MaximumMatching.WeightedPaths

section GeneralWeightedEdges

/-! Actual ordinary compressed edges in the higher-tenacity construction.
Base existence and confinement below the contraction threshold are explicit
induction hypotheses. Segment witnesses and their lengths are constructed from
maximal low-tenacity stretches of real minimum-level paths. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

namespace AltPath

theorem shortest_of_minlevel (p : AltPath M)
    (hmin : minlevel M p.last = some p.length) : p.Shortest :=
  (level_eq_some_iff M (p.length % 2) p.last p.length).1
    (level_of_minlevel p.last p.length hmin)

/-- The high vertex before a maximal low stretch is the actual lower blossom
boundary of its last low vertex. Neither that boundary nor its location is
supplied by the caller. -/
theorem low_stretch_boundary (p : AltPath M) (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b)
    (i j : Fin (p.length + 1)) (hij : i.val + 1 < j.val)
    (hjmin : minlevel M (p.vertex j) = some j.val)
    (hhigh : levelLT (some t) (tenacity M (p.vertex i)))
    (hlow : ∀ k : Fin (p.length + 1), i.val < k.val → k.val < j.val →
      levelLE (tenacity M (p.vertex k)) (some t)) :
    Blossom M t (p.vertex i) (p.vertex ⟨j.val - 1, by omega⟩) ∧
      i.val % 2 = 0 ∧ minlevel M (p.vertex i) = some i.val ∧
      (p.take (j.val - 1) (by omega)).Shortest := by
  let a := p.take j.val (by omega)
  have hamin : minlevel M a.last = some a.length := hjmin
  have hpred := a.minlevel_last_predecessor_honest hamin (by change 0 < j.val; omega)
  let q := p.take (j.val - 1) (by omega)
  have hq : q.Shortest := hpred
  have hu := hlow ⟨j.val - 1, by omega⟩
    (by change i.val < j.val - 1; omega) (by change j.val - 1 < j.val; omega)
  change levelLE (tenacity M q.last) (some t) at hu
  have hut : ∃ s, tenacity M q.last = some s ∧ s ≤ t := by
    cases hs : tenacity M q.last with
    | none => rw [hs] at hu; exact False.elim hu
    | some s => exact ⟨s, rfl, by simpa only [hs, levelLE] using hu⟩
  obtain ⟨s, hs, hst⟩ := hut
  obtain ⟨b, hb, hbl⟩ := blossom_cover_of_base_existence t ht hexists q.last s hs hst
  have hqb := blossom_baseOnPath t b q.last hbl hb q rfl hq
  have hqi : q.BaseOnPath t (p.vertex i) := by
    refine ⟨⟨i.val, by change i.val < j.val - 1 + 1; omega⟩, rfl, hhigh, ?_⟩
    intro k hk hkhigh
    have hkval : k.val < j.val := by have := k.isLt; change k.val < j.val - 1 + 1 at this; omega
    have hklo := hlow ⟨k.val, by omega⟩ (by change i.val < k.val at hk; exact hk) hkval
    change levelLT (some t) (tenacity M (p.vertex ⟨k.val, by omega⟩)) at hkhigh
    cases hten : tenacity M (p.vertex ⟨k.val, by omega⟩) with
    | none => simp only [hten, levelLE] at hklo
    | some z =>
      have hzle : z ≤ t := by simpa only [hten, levelLE] using hklo
      have hzgt : t < z := by simpa only [hten, levelLT] using hkhigh
      omega
  have hbi : b = p.vertex i := q.baseOnPath_unique t b (p.vertex i) hqb hqi
  rw [hbi] at hbl
  obtain ⟨k, hk, hke, _, hkmin, _⟩ := blossom_on_shortest t (p.vertex i) q.last hbl q rfl hq
  have hki : k.val = i.val := by
    have hh := p.injective ⟨k.val, by have := k.isLt; change k.val < j.val - 1 + 1 at this; omega⟩ i hk
    exact congrArg Fin.val hh
  refine ⟨hbl, by omega, ?_, hq⟩
  simpa only [hki] using hkmin

/-- Under the lower-tenacity confinement induction hypothesis, the maximal
stretch gives an actual alternating edge realization, with its exact weight.
The final high endpoint is outside the target blossom after reversal. -/
theorem low_stretch_expansion (p : AltPath M) (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M t b v → levelLT (some t) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M t b w)
    (i j : Fin (p.length + 1)) (hij : i.val + 1 < j.val)
    (hjmin : minlevel M (p.vertex j) = some j.val)
    (hhi : levelLT (some t) (tenacity M (p.vertex i)))
    (hhj : levelLT (some t) (tenacity M (p.vertex j)))
    (hlow : ∀ k : Fin (p.length + 1), i.val < k.val → k.val < j.val →
      levelLE (tenacity M (p.vertex k)) (some t)) :
    ∃ s : AltSegment M, s.first = p.vertex i ∧ s.last = p.vertex j ∧
      s.length = j.val - i.val ∧ BlossomEdgeExpansion M t s ∧
      minlevel M (p.vertex i) = some i.val := by
  obtain ⟨hbl, hie, himin, hq⟩ := p.low_stretch_boundary t ht hexists i j hij hjmin hhi hlow
  let q := p.take (j.val - 1) (by omega)
  obtain ⟨k, hke, hk, _, hrelative⟩ := blossom_shortest_relative t (p.vertex i) q.last hbl hhi q rfl hq
  have hki : k.val = i.val := by
    have hh := p.injective ⟨k.val, by have := k.isLt; change k.val < j.val - 1 + 1 at this; omega⟩ i hk
    exact congrArg Fin.val hh
  let r := q.segment i.val (by change i.val ≤ j.val - 1; omega) hie
  have hr : r.Shortest := by simpa only [hki] using hrelative
  have hrf : r.first = p.vertex i := rfl
  have hrl : r.last = q.last := q.segment_last _ _ _
  let s := (p.take j.val (by omega)).segment i.val (by change i.val ≤ j.val; omega) hie
  have hsf : s.first = p.vertex i := rfl
  have hsl : s.last = p.vertex j := (p.take j.val (by omega)).segment_last _ _ _
  refine ⟨s, hsf, hsl, rfl, ⟨by rw [hsf]; exact hhi, by rw [hsl]; exact hhj, ?_⟩, himin⟩
  intro a ha hal
  have hab : a.val ≤ j.val - 1 - i.val := by change a.val < j.val - i.val at hal; omega
  have hw := hconf (p.vertex i) q.last hbl hhi r hr hrf hrl
    (s.vertex a) ⟨⟨a.val, by change a.val < j.val - 1 - i.val + 1; omega⟩, rfl⟩
  rcases hw with hw | hw
  · have he := p.injective ⟨i.val + a.val, by change a.val < j.val - i.val at hal; omega⟩ i hw
    have hv := congrArg Fin.val he
    dsimp only at hv
    omega
  · exact hw

/-- Reverse the ordinary compressed-edge witness into a descending edge.
Its length is the difference of the actual endpoint minlevels; matching phase
is computed from that expanded length, not from the compressed edge count. -/
theorem low_stretch_reverse_expansion (p : AltPath M) (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M t b v → levelLT (some t) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M t b w)
    (i j : Fin (p.length + 1)) (hij : i.val + 1 < j.val)
    (hjmin : minlevel M (p.vertex j) = some j.val)
    (hhi : levelLT (some t) (tenacity M (p.vertex i)))
    (hhj : levelLT (some t) (tenacity M (p.vertex j)))
    (hlow : ∀ k : Fin (p.length + 1), i.val < k.val → k.val < j.val →
      levelLE (tenacity M (p.vertex k)) (some t)) :
    ∃ s : ParitySegment M, s.first = p.vertex j ∧ s.last = p.vertex i ∧
      s.length = j.val - i.val ∧ s.phase % 2 = (j.val - i.val + 1) % 2 ∧
      (∀ k : Fin (s.length + 1), 0 < k.val → k.val < s.length →
        Blossom M t (p.vertex i) (s.vertex k)) ∧
      minlevel M (p.vertex i) = some i.val := by
  obtain ⟨a, haf, hal, han, hax, hmin⟩ :=
    p.low_stretch_expansion t ht hexists hconf i j hij hjmin hhi hhj hlow
  let s := (ParitySegment.ofAltSegment a).reverse
  refine ⟨s, (ParitySegment.ofAltSegment a).reverse_first.trans hal,
    (ParitySegment.ofAltSegment a).reverse_last.trans haf, han, ?_, ?_, hmin⟩
  · change (0 + a.length + 1) % 2 = _
    rw [han]
    omega
  · intro k hk hkl
    have hpos : 0 < a.length - k.val := by change k.val < a.length at hkl; omega
    have hlt : a.length - k.val < a.length := by omega
    have hh := hax.2.2 ⟨a.length - k.val, by omega⟩ hpos hlt
    rw [haf] at hh
    exact hh

end AltPath
end MaximumMatching

end GeneralWeightedEdges

section GeneralLowLocalization

/-! Locate low vertices on an honest high-core prefix inside actual lower
blossoms. Maximal low stretches are selected from the finite path; their
boundaries are not supplied as conclusions by an external oracle. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Every vertex inside an ordinary low stretch belongs to the blossom of its
preceding high boundary, under the lower-threshold confinement hypothesis. -/
theorem low_stretch_mem (p : AltPath M) (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M t b v → levelLT (some t) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M t b w)
    (i j k : Fin (p.length + 1)) (hik : i.val < k.val) (hkj : k.val < j.val)
    (hjmin : minlevel M (p.vertex j) = some j.val)
    (hhi : levelLT (some t) (tenacity M (p.vertex i)))
    (hlow : ∀ a : Fin (p.length + 1), i.val < a.val → a.val < j.val →
      levelLE (tenacity M (p.vertex a)) (some t)) : Blossom M t (p.vertex i) (p.vertex k) := by
  obtain ⟨hbl, hie, _, hq⟩ := p.low_stretch_boundary t ht hexists i j (by omega) hjmin hhi hlow
  let q := p.take (j.val - 1) (by omega)
  obtain ⟨a, hae, ha, _, hr⟩ := blossom_shortest_relative t (p.vertex i) q.last hbl hhi q rfl hq
  have hai : a.val = i.val := by
    have hh := p.injective ⟨a.val, by have := a.isLt; change a.val < j.val - 1 + 1 at this; omega⟩ i ha
    exact congrArg Fin.val hh
  let r := q.segment i.val (by change i.val ≤ j.val - 1; omega) hie
  have hrs : r.Shortest := by simpa only [hai] using hr
  have hrf : r.first = p.vertex i := rfl
  have hrl : r.last = q.last := q.segment_last _ _ _
  have hw := hconf (p.vertex i) q.last hbl hhi r hrs hrf hrl (p.vertex k)
    ⟨⟨k.val - i.val, by change k.val - i.val < j.val - 1 - i.val + 1; omega⟩, by
      change p.vertex ⟨i.val + (k.val - i.val), _⟩ = p.vertex k
      congr 1
      apply Fin.ext
      change i.val + (k.val - i.val) = k.val
      omega⟩
  rcases hw with hw | hw
  · have hv := congrArg Fin.val (p.injective k i hw)
    omega
  · exact hw

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

/-- A low vertex before an honest high-core endpoint has a preceding boundary
on the same path. All other high vertices in that prefix need only satisfy
their actual minlevel/index equality. -/
theorem low_vertex_boundary_before (p : AltPath M) (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M t b v → levelLT (some t) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M t b w)
    (k B : Fin (p.length + 1)) (hkB : k.val < B.val)
    (hroot : levelLT (some t) (tenacity M p.first))
    (hB : levelLT (some t) (tenacity M (p.vertex B)))
    (hk : levelLE (tenacity M (p.vertex k)) (some t))
    (hhon : ∀ j : Fin (p.length + 1), j.val ≤ B.val →
      levelLT (some t) (tenacity M (p.vertex j)) → minlevel M (p.vertex j) = some j.val) :
    ∃ i : Fin (p.length + 1), i.val < k.val ∧
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
    ⟨k.val, ⟨0, by omega⟩, by simp, hroot⟩
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
  refine ⟨i, hik, hhi, p.low_stretch_mem t ht hexists hconf i j k hik hkj'
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

/-- A low-blossom visit before an honest high endpoint forces that blossom's
actual boundary to occur earlier on the original path. This rules out early
intersections when the boundary is absent, without assuming avoidance. -/
theorem blossom_member_before_high_forces_boundary (p : AltPath M) (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M t b v → levelLT (some t) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M t b w)
    (k B : Fin (p.length + 1)) (hkB : k.val < B.val)
    (hroot : levelLT (some t) (tenacity M p.first))
    (hB : levelLT (some t) (tenacity M (p.vertex B)))
    (hhon : ∀ j : Fin (p.length + 1), j.val ≤ B.val →
      levelLT (some t) (tenacity M (p.vertex j)) → minlevel M (p.vertex j) = some j.val)
    (c : V) (hc : levelLT (some t) (tenacity M c)) (hmem : Blossom M t c (p.vertex k)) :
    ∃ i : Fin (p.length + 1), i.val < k.val ∧ p.vertex i = c := by
  classical
  obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound t c (p.vertex k) hmem
  have hk : levelLE (tenacity M (p.vertex k)) (some t) := by simpa only [hs, levelLE] using hst
  obtain ⟨i, hik, hi, hbl⟩ := p.low_vertex_boundary_before t ht hexists hconf k B hkB hroot hB hk hhon
  refine ⟨i, hik, ?_⟩
  apply Classical.byContradiction
  intro hne
  exact blossoms_disjoint_same_tenacity t (p.vertex i) c hi hc hne (p.vertex k) ⟨hbl, hmem⟩

end MaximumMatching.AltPath

end GeneralLowLocalization

section GeneralHighGeometry

/-! Geometry of the high-tenacity core of a shortest maxlevel path. Unlike the
minimum-tenacity lemmas, only the vertices named in each statement need have
tenacity at least that of the endpoint. Lower blossoms elsewhere are allowed. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A high vertex has the same triangular minlevel as in the minimum case. -/
theorem high_minlevel_triangle (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (i : Fin (p.length + 1))
    (hi : levelLE (some (p.length + q.length)) (tenacity M (p.vertex i))) :
    minlevel M (p.vertex i) = some (min i.val (p.length + q.length - i.val)) := by
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hhon := (p.limited_bfs_honesty hp i (by rw [hten]; exact hi)).1
  have hlevel := (p.honest_iff_level i).1 hhon
  by_cases hhalf : 2 * i.val < p.length + q.length
  · have hm := minlevel_of_below_half (p.vertex i) i.val (p.length + q.length)
      hlevel hhalf hi
    rw [hm, Nat.min_eq_left (by omega)]
  · have hstrict : p.length + q.length < 2 * i.val := by omega
    exact (levels_of_opposite_bound (p.vertex i) i.val (p.length + q.length)
      hlevel (by omega) hi (p.above_half_opposite q hp hpe hqo hend hinner i hstrict)).2

/-- Every high vertex past the midpoint has exactly the endpoint's tenacity. -/
theorem high_tenacity_above_half (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (i : Fin (p.length + 1))
    (hi : levelLE (some (p.length + q.length)) (tenacity M (p.vertex i)))
    (hhalf : p.length + q.length < 2 * i.val) :
    tenacity M (p.vertex i) = some (p.length + q.length) := by
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hhon := (p.limited_bfs_honesty hp i (by rw [hten]; exact hi)).1
  exact (levels_of_opposite_bound (p.vertex i) i.val (p.length + q.length)
    ((p.honest_iff_level i).1 hhon) (by omega) hi
    (p.above_half_opposite q hp hpe hqo hend hinner i hhalf)).1

/-- Adjacent high vertices straddle the unique midpoint exactly when their
edge is a bridge. Edges involving low vertices require the lower-blossom step. -/
theorem high_edge_bridge_iff (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (i : Fin p.length)
    (hsource : levelLE (some (p.length + q.length))
      (tenacity M (p.vertex ⟨i.val, by omega⟩)))
    (htarget : levelLE (some (p.length + q.length))
      (tenacity M (p.vertex ⟨i.val + 1, by omega⟩))) :
    Bridge M (p.vertex ⟨i.val, by omega⟩) (p.vertex ⟨i.val + 1, by omega⟩) ↔
      2 * i.val + 1 = p.length + q.length := by
  let u := p.vertex ⟨i.val, by omega⟩
  let v := p.vertex ⟨i.val + 1, by omega⟩
  have hu := p.high_minlevel_triangle q hp hq hpe hqo hend hinner ⟨i.val, by omega⟩ hsource
  have hv := p.high_minlevel_triangle q hp hq hpe hqo hend hinner ⟨i.val + 1, by omega⟩ htarget
  have ha : G.Adj u v := p.adjacent i
  have hpar : (M.mate u = some v) ↔ i.val % 2 = 1 := p.alternating i
  by_cases he : 2 * i.val + 1 = p.length + q.length
  · have hue : minlevel M u = some i.val := by
      simpa only [u, Nat.min_eq_left (show i.val ≤ p.length + q.length - i.val by omega)] using hu
    have hve : minlevel M v = some i.val := by
      simpa only [v, Nat.min_eq_right (show p.length + q.length - (i.val + 1) ≤ i.val + 1 by omega),
        show p.length + q.length - (i.val + 1) = i.val by omega,
        Nat.min_eq_right (show i.val ≤ i.val + 1 by omega)] using hv
    exact ⟨fun _ => he, fun _ => ⟨ha, not_propEdge_of_minlevel_eq M u v i.val hue hve⟩⟩
  · have hprop : PropEdge M u v := by
      by_cases hl : 2 * i.val + 1 < p.length + q.length
      · have hue : minlevel M u = some i.val := by
          simpa only [u, Nat.min_eq_left (show i.val ≤ p.length + q.length - i.val by omega)] using hu
        have hve : minlevel M v = some (i.val + 1) := by
          simpa only [v, Nat.min_eq_left (show i.val + 1 ≤ p.length + q.length - (i.val + 1) by omega)] using hv
        exact Or.inl (predecessor_of_consecutive_minlevels M u v i.val hue hve ha hpar)
      · have hue : minlevel M u = some (p.length + q.length - (i.val + 1) + 1) := by
          have hu' : minlevel M u = some (p.length + q.length - i.val) := by
            simpa only [u, Nat.min_eq_right (show p.length + q.length - i.val ≤ i.val by omega)] using hu
          simpa only [show p.length + q.length - i.val = p.length + q.length - (i.val + 1) + 1 by omega] using hu'
        have hve : minlevel M v = some (p.length + q.length - (i.val + 1)) := by
          simpa only [v, Nat.min_eq_right (show p.length + q.length - (i.val + 1) ≤ i.val + 1 by omega)] using hv
        refine Or.inr (predecessor_of_consecutive_minlevels M v u _ hve hue (G.symm ha) ?_)
        have hpmod : (p.length + q.length - (i.val + 1)) % 2 = i.val % 2 := by omega
        rw [hpmod]
        exact ⟨fun hm => hpar.1 (M.symm hm), fun h => M.symm (hpar.2 h)⟩
    exact ⟨fun hb => False.elim (hb.2 hprop), fun h => False.elim (he h)⟩

/-- The high-high midpoint bridge has the actual endpoint tenacity. This
proves the two adjacent-endpoint cases in the general bridge induction. -/
theorem high_middle_edge_tenacity (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (i : Fin p.length) (hi : 2 * i.val + 1 = p.length + q.length)
    (hsource : levelLE (some (p.length + q.length))
      (tenacity M (p.vertex ⟨i.val, by omega⟩)))
    (htarget : levelLE (some (p.length + q.length))
      (tenacity M (p.vertex ⟨i.val + 1, by omega⟩))) :
    edgeTenacity M (p.vertex ⟨i.val, by omega⟩) (p.vertex ⟨i.val + 1, by omega⟩) =
      some (p.length + q.length) := by
  let u := p.vertex ⟨i.val, by omega⟩
  let v := p.vertex ⟨i.val + 1, by omega⟩
  have hpar : (M.mate u = some v) ↔ i.val % 2 = 1 := p.alternating i
  have hvt : tenacity M v = some (p.length + q.length) :=
    p.high_tenacity_above_half q hp hq hpe hqo hend hinner ⟨i.val + 1, by omega⟩ htarget
      (by change p.length + q.length < 2 * (i.val + 1); omega)
  change edgeTenacity M u v = _
  unfold edgeTenacity
  by_cases hm : M.mate u = some v
  · rw [ite_eq_left hm, ← (matched_tenacity M hm).2, hvt]
  · rw [ite_eq_right hm]
    have hie : i.val % 2 = 0 := by have hn : ¬i.val % 2 = 1 := fun h => hm (hpar.2 h); omega
    have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
    have hhu := (p.honest_iff_level ⟨i.val, by omega⟩).1
      (p.limited_bfs_honesty hp _ (by rw [hten]; exact hsource)).1
    have hhv := (p.honest_iff_level ⟨i.val + 1, by omega⟩).1
      (p.limited_bfs_honesty hp _ (by rw [hten]; exact htarget)).1
    have hue : evenlevel M u = some i.val := by simpa only [hie] using hhu
    have hvo : oddlevel M v = some (i.val + 1) := by
      simpa only [show (i.val + 1) % 2 = 1 by omega] using hhv
    have hve : evenlevel M v = some i.val := by
      unfold tenacity at hvt
      rw [hvo] at hvt
      cases he : evenlevel M v with
      | none => simp only [he, levelAdd] at hvt; contradiction
      | some k =>
        have hk : k + (i.val + 1) = p.length + q.length := by
          simpa only [he, levelAdd, Option.some.injEq] using hvt
        exact congrArg some (by omega)
    rw [hue, hve]
    simp only [levelAdd, Option.map_some]
    exact congrArg some (by omega)

end MaximumMatching.AltPath

end GeneralHighGeometry

section GeneralMaxCapPredecessor

/-! A dishonest low predecessor of an outer maxlevel endpoint is inside the
endpoint's lower blossom. The prop/bridge distinction is derived from actual
levels, and only the low vertex's already-established base is used. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- An unmatched edge directed into an outer vertex cannot be a prop. -/
theorem not_predecessor_unmatched_outer (c u : V)
    (hc : Outer M c) (hm : M.mate c ≠ some u) : ¬ Predecessor M u c := by
  rintro ⟨p, hp, hpmin, hpos, hu⟩
  have hce := (minlevel_eq_even_of_outer c hc).symm.trans hpmin
  have hpe := level_parity M 0 c p.length hce
  have hlast : p.vertex ⟨p.length, by omega⟩ = c := hp
  have hprev : M.mate c = some u := by
    have hh := p.mate_previous p.length (Nat.le_refl _) hpos hpe
    simpa only [hlast, hu] using hh
  exact hm hprev

/-- If an unmatched edge's finite tenacity is below an outer endpoint's
vertex tenacity, it is a prop directed away from that endpoint. -/
theorem predecessor_of_unmatched_outer_edge_below (c u : V)
    (hc : Outer M c) (ha : G.Adj c u) (hm : M.mate c ≠ some u)
    (t e f : Nat) (hct : tenacity M c = some t)
    (hce : evenlevel M c = some e) (hue : evenlevel M u = some f)
    (hsmall : e + f + 1 < t) : Predecessor M c u := by
  classical
  have hedge : edgeTenacity M c u = some (e + f + 1) := by
    simp only [edgeTenacity, ite_eq_right hm, hce, hue, levelAdd, Option.map_some]
  have hprop : PropEdge M c u := by
    by_cases hp : PropEdge M c u
    · exact hp
    · obtain ⟨s, hs, hbound⟩ := (unmatched_bridge_tenacity ⟨ha, hp⟩ hm _ hedge).1 hc
      have hst := Option.some.inj (hs.symm.trans hct)
      omega
  exact hprop.resolve_right (not_predecessor_unmatched_outer c u hc hm)

/-- An actual common base agrees with a higher-tenacity immediate predecessor
on a minimum-level witness. -/
theorem isBase_of_high_predecessor (c u : V) (hpred : Predecessor M c u)
    (s : Nat) (hut : tenacity M u = some s)
    (hc : levelLT (some s) (tenacity M c)) (hexists : ∃ b, IsBase M u b) :
    IsBase M u c := by
  obtain ⟨b, hb⟩ := hexists
  obtain ⟨p, hp, hpmin, hpos, hpc⟩ := hpred
  have hpshort := p.shortest_of_minlevel (by rw [hp]; exact hpmin)
  have hpb : p.BaseOnPath s b := by
    obtain ⟨r, hur, hcommon⟩ := hb
    have hrs := Option.some.inj (hur.symm.trans hut)
    subst r
    exact hcommon p hp hpshort
  have hpcbase : p.BaseOnPath s c := by
    refine ⟨⟨p.length - 1, by omega⟩, hpc, hc, ?_⟩
    intro j hj
    have hje : j = ⟨p.length, by omega⟩ := Fin.ext (by
      change j.val = p.length
      change p.length - 1 < j.val at hj
      have := j.isLt
      omega)
    rw [hje]
    change ¬levelLT (some s) (tenacity M p.last)
    rw [hp, hut]
    exact Nat.lt_irrefl _
  exact (p.baseOnPath_unique s b c hpb hpcbase) ▸ hb

/-- The low endpoint of a sufficiently small edge has the outer endpoint as
its actual base, using only base existence at the low endpoint. -/
theorem base_of_unmatched_outer_edge_below (c u : V)
    (hc : Outer M c) (ha : G.Adj c u) (hm : M.mate c ≠ some u)
    (t e f s : Nat) (hct : tenacity M c = some t) (hut : tenacity M u = some s)
    (hst : s < t) (hce : evenlevel M c = some e) (hue : evenlevel M u = some f)
    (hsmall : e + f + 1 < t) (hexists : ∃ b, IsBase M u b) : IsBase M u c :=
  isBase_of_high_predecessor c u
    (predecessor_of_unmatched_outer_edge_below c u hc ha hm t e f hct hce hue hsmall)
    s hut (by rw [hct]; exact hst) hexists

namespace AltPath

/-- A dishonest last predecessor can occur only on an outer endpoint's odd
maxlevel path. Even paths trim across a matched edge; an inner endpoint's odd
path is already a minimum-level path and has an honest predecessor. -/
theorem dishonest_last_predecessor_outer (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (hpt : tenacity M p.last = some t) (hpos : 0 < p.length)
    (hdish : ¬p.BFSHonest ⟨p.length - 1, by omega⟩) :
    p.length % 2 = 1 ∧ Outer M p.last := by
  have hpo : p.length % 2 = 1 := by
    by_cases he : p.length % 2 = 0
    · have hm := p.even_last_mate he hpos
      have hh := (matched_shortest_iff M (M.symm hm) (p.length - 1)).mp (by
        rw [show p.length - 1 + 1 = p.length by omega]
        simpa only [Shortest, he] using hp)
      apply False.elim
      apply hdish
      change IsShortest M ((p.length - 1) % 2)
        (p.vertex ⟨p.length - 1, by omega⟩) (p.length - 1)
      simpa only [show (p.length - 1) % 2 = 1 by omega] using hh
    · omega
  refine ⟨hpo, ?_⟩
  apply Classical.byContradiction
  intro hn
  obtain ⟨e, o, he, ho, _, _, _⟩ := finite_levels_of_tenacity p.last t hpt
  have hpodd : oddlevel M p.last = some p.length :=
    (level_eq_some_iff M 1 p.last p.length).mpr (by simpa only [Shortest, hpo] using hp)
  have hop : o = p.length := Option.some.inj (ho.symm.trans hpodd)
  have hoe : o ≤ e := by
    have hnot : ¬e < o := by simpa only [Outer, he, ho, levelLT] using hn
    omega
  have hmin : minlevel M p.last = some p.length := by
    simp only [minlevel, he, ho, levelMin]
    rw [Nat.min_eq_right hoe, hop]
  exact hdish (p.minlevel_last_predecessor_honest hmin hpos)


/-- At an outer endpoint's odd maxlevel path, a dishonest low predecessor is
inside the lower blossom rooted at that endpoint. This closes the terminal
prop case of a low stretch without assuming its boundary in advance. -/
theorem dishonest_outer_predecessor_base (p : AltPath M) (hp : p.Shortest)
    (hpo : p.length % 2 = 1) (hc : Outer M p.last)
    (t s : Nat) (hct : tenacity M p.last = some t)
    (hut : tenacity M (p.vertex ⟨p.length - 1, by omega⟩) = some s)
    (hst : s < t)
    (hexists : ∃ b, IsBase M (p.vertex ⟨p.length - 1, by omega⟩) b)
    (hdish : ¬p.BFSHonest ⟨p.length - 1, by omega⟩) :
    IsBase M (p.vertex ⟨p.length - 1, by omega⟩) p.last ∧
      Blossom M (t - 2) p.last (p.vertex ⟨p.length - 1, by omega⟩) := by
  let u := p.vertex ⟨p.length - 1, by omega⟩
  have hpredpar : (p.length - 1) % 2 = 0 := by omega
  obtain ⟨e, o, hce, hco, _, _, hsum⟩ := finite_levels_of_tenacity p.last t hct
  have hcop : oddlevel M p.last = some p.length :=
    (level_eq_some_iff M 1 p.last p.length).2 (by simpa only [Shortest, hpo] using hp)
  have hop : o = p.length := Option.some.inj (hco.symm.trans hcop)
  obtain ⟨f, huf, hfbound⟩ := p.prefix_level_bound ⟨p.length - 1, by omega⟩
  have hue : evenlevel M u = some f := by simpa only [hpredpar] using huf
  have hflt : f < p.length - 1 := by
    by_cases he : f = p.length - 1
    · exact False.elim (hdish ((p.honest_iff_level _).2 (by simpa only [he] using huf)))
    · change f ≤ p.length - 1 at hfbound
      omega
  have ha : G.Adj p.last u := by
    have hh := G.symm (p.adjacent ⟨p.length - 1, by omega⟩)
    simpa only [show p.length - 1 + 1 = p.length by omega, last, u] using hh
  have hm : M.mate p.last ≠ some u := by
    intro hh
    have he := (p.alternating ⟨p.length - 1, by omega⟩).1
      (by simpa only [show p.length - 1 + 1 = p.length by omega, last, u] using M.symm hh)
    change (p.length - 1) % 2 = 1 at he
    omega
  have hb : IsBase M u p.last := base_of_unmatched_outer_edge_below p.last u hc ha hm
    t e f s hct hut hst hce hue (by omega) hexists
  refine ⟨hb, blossom_of_base_le (t - 2) ?_ p.last u hb ?_⟩
  · have htodd := tenacity_odd M p.last t hct
    have hthree := hb.tenacity_ge_three s hut
    omega
  · have hsodd := tenacity_odd M u s hut
    have htodd := tenacity_odd M p.last t hct
    rw [hut]
    change s ≤ t - 2
    omega

end AltPath

end MaximumMatching

end GeneralMaxCapPredecessor
