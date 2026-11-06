import MaximumMatching.BlossomRelative
import MaximumMatching.BlossomCover
import MaximumMatching.MinScan
import MaximumMatching.WeightedExpansion

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
