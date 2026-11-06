import MaximumMatching.MatchingGraphExpansion
import MaximumMatching.GeneralWeightedTop
import MaximumMatching.BridgeClassification
import MaximumMatching.GeneralEdgeHelpers

/-! Construct the two real endpoint-to-bud paths for a bridge at the next
odd tenacity. These use current lower-blossom fibers and semantic bridge
classification; no endpoint path or length budget is supplied by the caller. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The unmatched-bridge endpoint uses its even relative path. A high
uncontracted endpoint is necessarily outer; a low endpoint uses its actual
lower-blossom even path. -/
theorem unmatched_bridge_top_segment (cut : Nat) (hc : cut % 2 = 1)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut < p.length)
    (u v b : V) (hbridge : Bridge M u v) (hm : M.mate u ≠ some v)
    (ht : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hb : levelLT (some cut) (tenacity M b))
    (hfiber : u = b ∨ Blossom M cut b u)
    (E B : Nat) (hE : evenlevel M u = some E) (hB : minlevel M b = some B) :
    ∃ a : ParitySegment M, a.first = u ∧ a.last = b ∧ a.length + B = E ∧
      a.phase % 2 = 1 ∧ (a.phase + a.length) % 2 = (B + 1) % 2 ∧
      (∀ k : Fin (a.length + 1), k.val < a.length →
        Blossom M cut b (a.vertex k)) := by
  rcases hfiber with rfl | hbl
  · have houter : Outer M u := by
      apply Classical.byContradiction
      intro hn
      have hEp := level_parity M 0 u E hE
      obtain ⟨k, hk, _⟩ := minlevel_le_of_level u E (by simpa only [hEp] using hE)
      obtain ⟨t, ht', htc⟩ := (unmatched_bridge_tenacity hbridge hm (cut + 2) ht).2 ⟨⟨k, hk⟩, hn⟩
      have hto := tenacity_odd M u t ht'
      rw [ht'] at hb
      change cut < t at hb
      omega
    have hBE : B = E := Option.some.inj
      (hB.symm.trans ((minlevel_eq_even_of_outer u houter).trans hE))
    have hBp : B % 2 = 0 := by have := level_parity M 0 u E hE; omega
    refine ⟨ParitySegment.trivial M u 1, rfl, rfl, ?_, rfl, ?_, ?_⟩
    · change 0 + B = E
      omega
    · change (1 + 0) % 2 = (B + 1) % 2
      omega
    · intro k hk
      change k.val < 0 at hk
      omega
  · obtain ⟨t, hut, htc⟩ := blossom_tenacity_bound cut b u hbl
    have helig : EligibleTenacity M cut := ⟨hc, ⟨u, by simpa only [hut, levelLE] using htc⟩, hnoaug⟩
    have hconf := general_blossom_relative_confined M cut helig b u hbl hb
    obtain ⟨a, haf, hal, han, hap, hae, hai⟩ := blossom_even_top_segment cut b u hbl hb hconf E B hE hB
    have hBe : evenlevel M b = some B := (minlevel_eq_even_of_outer b (blossom_outer cut b u hbl)).symm.trans hB
    have hBp := level_parity M 0 b B hBe
    have hBE : B ≤ E := by
      obtain ⟨p, hp, hl, hpar⟩ := ((level_eq_some_iff M 0 u E).1 hE).1
      have hps : p.Shortest := by
        simpa only [AltPath.Shortest, hp, hl, hpar] using (level_eq_some_iff M 0 u E).1 hE
      obtain ⟨i, _, _, _, himin, _⟩ := blossom_on_shortest cut b u hbl p hp hps
      have hiB := Option.some.inj (himin.symm.trans hB)
      have := i.isLt
      omega
    exact ⟨a, haf, hal, by omega, hap, by omega, hai⟩

end MaximumMatching

namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}
namespace BudGraphInvariant
variable {cap cut : Nat} {s : State V} {F : BudForest V}

/-- Actual bridge endpoint paths with all phase and total-budget equations
needed for weighted DDFS path lifting. The lower representation is explicit;
no same-level petal is identified with a whole mathematical blossom. -/
theorem bridge_top_segments (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1)
    (hnoaug : ∀ p : AltPath M, p.Augmenting → cut < p.length)
    (hrep : LowerBlossomRepresentation M cut s F)
    (u v : V) (hbridge : Bridge M u v) (ht : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, s.minLabel u = some k) (hv : ∃ k, s.minLabel v = some k) :
    ∃ a b : ParitySegment M,
      a.first = u ∧ a.last = F.root u ∧ b.first = v ∧ b.last = F.root v ∧
      (a.phase + a.length) % 2 = ((s.minLabel (F.root u)).getD 0 + 1) % 2 ∧
      (b.phase + b.length) % 2 = ((s.minLabel (F.root v)).getD 0 + 1) % 2 ∧
      (∀ k : Fin (a.length + 1), k.val < a.length → Blossom M cut (F.root u) (a.vertex k)) ∧
      (∀ k : Fin (b.length + 1), k.val < b.length → Blossom M cut (F.root v) (b.vertex k)) ∧
      a.phase % 2 = b.phase % 2 ∧
      ((M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1) ∧
      (a.length + (s.minLabel (F.root u)).getD 0) +
        (b.length + (s.minLabel (F.root v)).getD 0) + 1 = cut + 2 := by
  obtain ⟨U, hU⟩ := hu
  obtain ⟨V, hV⟩ := hv
  obtain ⟨B, hB⟩ := h.rootAssigned u U hU
  obtain ⟨C, hC⟩ := h.rootAssigned v V hV
  obtain ⟨hbhigh, hufiber⟩ := hrep u U hU
  obtain ⟨hchigh, hvfiber⟩ := hrep v V hV
  have hBm := h.minInvariant.1.1 (F.root u) B hB
  have hCm := h.minInvariant.1.1 (F.root v) C hC
  by_cases hm : M.mate u = some v
  · obtain ⟨i, hui, hvi, hum, hvm, _, _, hti⟩ := matched_bridge_levels hbridge hm (cut + 2) ht
    have hut : tenacity M u = some (cut + 2) := by
      have htm : matchedEdgeTenacity M u v = some (cut + 2) := by simpa only [MaximumMatching.edgeTenacity, ite_eq_left hm] using ht
      exact (matched_tenacity M hm).1.trans ((matched_tenacity M hm).2.trans htm)
    have hvt : tenacity M v = some (cut + 2) := (matched_tenacity M hm).2.trans
      (by simpa only [MaximumMatching.edgeTenacity, ite_eq_left hm] using ht)
    have hub : u = F.root u := by
      rcases hufiber with he | hb
      · exact he
      · obtain ⟨t, ht', htc⟩ := blossom_tenacity_bound cut (F.root u) u hb
        have := Option.some.inj (ht'.symm.trans hut)
        omega
    have hvc : v = F.root v := by
      rcases hvfiber with he | hb
      · exact he
      · obtain ⟨t, ht', htc⟩ := blossom_tenacity_bound cut (F.root v) v hb
        have := Option.some.inj (ht'.symm.trans hvt)
        omega
    have hBi : B = i := Option.some.inj (hBm.symm.trans (hub ▸ hum))
    have hCi : C = i := Option.some.inj (hCm.symm.trans (hvc ▸ hvm))
    have hio := level_parity M 1 u i hui
    refine ⟨ParitySegment.trivial M u 0, ParitySegment.trivial M v 0,
      rfl, hub, rfl, hvc, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
    · change (0 + 0) % 2 = ((s.minLabel (F.root u)).getD 0 + 1) % 2
      simp only [hB, Option.getD_some]
      omega
    · change (0 + 0) % 2 = ((s.minLabel (F.root v)).getD 0 + 1) % 2
      simp only [hC, Option.getD_some]
      omega
    · intro k hk; change k.val < 0 at hk; omega
    · intro k hk; change k.val < 0 at hk; omega
    · change (M.mate v = some u) ↔ (0 + 1) % 2 = 1
      exact ⟨fun _ => rfl, fun _ => M.symm hm⟩
    · change (0 + (s.minLabel (F.root u)).getD 0) + (0 + (s.minLabel (F.root v)).getD 0) + 1 = cut + 2
      simp only [hB, hC, Option.getD_some]
      omega
  · have hlevels : ∃ E D, evenlevel M u = some E ∧ evenlevel M v = some D ∧ E + D + 1 = cut + 2 := by
      have he : (levelAdd (evenlevel M u) (evenlevel M v)).map (· + 1) = some (cut + 2) :=
        by simpa only [MaximumMatching.edgeTenacity, ite_eq_right hm] using ht
      cases hEu : evenlevel M u with
      | none => simp only [hEu, levelAdd, Option.map_none] at he; contradiction
      | some E =>
        cases hDv : evenlevel M v with
        | none => simp only [hEu, hDv, levelAdd, Option.map_none] at he; contradiction
        | some D =>
          exact ⟨E, D, rfl, rfl, by simpa only [hEu, hDv, levelAdd, Option.map_some, Option.some.injEq] using he⟩
    obtain ⟨E, D, hE, hD, hsum⟩ := hlevels
    have hm' : M.mate v ≠ some u := fun hh => hm (M.symm hh)
    have ht' : MaximumMatching.edgeTenacity M v u = some (cut + 2) := (edgeTenacity_symmetric v u).trans ht
    obtain ⟨a, haf, hal, han, hap, hae, hai⟩ := unmatched_bridge_top_segment cut hc hnoaug
      u v (F.root u) hbridge hm ht hbhigh hufiber E B hE hBm
    obtain ⟨b, hbf, hbl, hbn, hbp, hbe, hbi⟩ := unmatched_bridge_top_segment cut hc hnoaug
      v u (F.root v) (bridge_symm hbridge) hm' ht' hchigh hvfiber D C hD hCm
    refine ⟨a, b, haf, hal, hbf, hbl, ?_, ?_, hai, hbi, by omega, ?_, ?_⟩
    · simpa only [hB, Option.getD_some] using hae
    · simpa only [hC, Option.getD_some] using hbe
    · rw [haf, hbf]
      constructor
      · intro hh; exact False.elim (hm' hh)
      · intro hh; omega
    · simp only [hB, hC, Option.getD_some]
      omega

end BudGraphInvariant
end MaximumMatching.Search
