import MaximumMatching.BlossomRelative
import MaximumMatching.WeightedTopExpansion

/-! Actual segment witnesses for low-tenacity top vertices in the source's
higher-tenacity graph. Lower-threshold confinement is an explicit induction
hypothesis; assigned artificial layers are not used as expanded path lengths. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Reverse an actual shortest even relative path from a lower-blossom boundary
to its member. The resulting descending top edge has matching phase one at
both endpoints, and length `evenlevel(member) - minlevel(boundary)`. -/
theorem blossom_even_top_segment (t : Nat) (b v : V)
    (hbl : Blossom M t b v) (hb : levelLT (some t) (tenacity M b))
    (hconf : ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
      ∀ w, q.Contains w → w = b ∨ Blossom M t b w)
    (e c : Nat) (he : evenlevel M v = some e) (hc : minlevel M b = some c) :
    ∃ a : ParitySegment M, a.first = v ∧ a.last = b ∧ a.length = e - c ∧
      a.phase % 2 = 1 ∧ (a.phase + a.length) % 2 = 1 ∧
      (∀ i : Fin (a.length + 1), i.val < a.length → Blossom M t b (a.vertex i)) := by
  obtain ⟨p, hpv, hpn, hpe⟩ := ((level_eq_some_iff M 0 v e).1 he).1
  have hp : p.Shortest := by
    have hs := (level_eq_some_iff M 0 v e).1 he
    simpa only [AltPath.Shortest, hpn, hpe, hpv] using hs
  obtain ⟨i, hie, hi, _, hr⟩ := blossom_shortest_relative t b v hbl hb p hpv hp
  obtain ⟨j, hj, _, _, hjmin, _⟩ := blossom_on_shortest t b v hbl p hpv hp
  have hji : j = i := p.injective j i (hj.trans hi.symm)
  have hic : i.val = c := by
    rw [hji, hc] at hjmin
    exact (Option.some.inj hjmin).symm
  let r := p.segment i.val (by omega) hie
  have hrf : r.first = b := hi
  have hrl : r.last = v := (p.segment_last _ _ _).trans hpv
  have hlen : r.length = e - c := by change p.length - i.val = _; omega
  have hre : r.length % 2 = 0 := by change (p.length - i.val) % 2 = 0; have := i.isLt; omega
  let a := (ParitySegment.ofAltSegment r).reverse
  refine ⟨a, (ParitySegment.ofAltSegment r).reverse_first.trans hrl,
    (ParitySegment.ofAltSegment r).reverse_last.trans hrf, hlen, ?_, ?_, ?_⟩
  · change (0 + r.length + 1) % 2 = 1
    omega
  · change (0 + r.length + 1 + r.length) % 2 = 1
    omega
  · intro k hk
    have hk' : 0 < r.length - k.val := by change k.val < r.length at hk; omega
    have hw := hconf r hr hrf hrl (a.vertex k)
      ⟨⟨r.length - k.val, by omega⟩, rfl⟩
    rcases hw with hw | hw
    · have heq : r.vertex ⟨r.length - k.val, by omega⟩ = r.vertex ⟨0, by omega⟩ := hw.trans hrf.symm
      have hv := congrArg Fin.val (r.injective _ _ heq)
      dsimp only at hv
      omega
    · exact hw

end MaximumMatching
