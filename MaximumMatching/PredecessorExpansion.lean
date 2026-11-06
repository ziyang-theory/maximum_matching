import MaximumMatching.GeneralStructureInduction
import MaximumMatching.GeneralWeightedEdges
import MaximumMatching.MinTenacityGeometry

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
