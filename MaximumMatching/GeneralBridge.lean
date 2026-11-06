import MaximumMatching.GeneralBridgeFirstEntry
import MaximumMatching.GeneralBridgeTerminal
import MaximumMatching.GeneralEdgeBounds

/-! Unique bridge at the endpoint tenacity on arbitrary maxlevel paths.
The induction uses only lower-cutoff bases, confinement, and relative edge
bounds. Other bridge tenacities on the path are allowed. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The general unique-bridge step, also suitable at the shortest augmenting
path threshold: only structural information strictly below `t` is needed. -/
theorem unique_bridge_maxlevel_of_lower (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w)
    (hedge : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ i : Fin q.length, levelLE (edgeTenacity M (q.vertex ⟨i.val, by omega⟩)
          (q.vertex ⟨i.val + 1, by omega⟩)) (some (t - 2)))
    (p : AltPath M) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length) : p.UniqueBridgeOfTenacity t := by
  have no_bridge (r : AltPath M) (hr : r.Shortest)
      (hcase : (∃ s, tenacity M r.last = some s ∧ s < t) ∨ 2 * r.length < t) :
      r.NoBridgeOfTenacity t := by
    rcases hcase with ⟨s, hs, hst⟩ | hshort
    · exact lower_shortest_no_bridge t ht hexists hedge r hr s hs hst
    · exact short_shortest_no_bridge t ht hexists hedge r hr hshort
  have aux : ∀ L (p : AltPath M), p.length = L → tenacity M p.last = some t →
      maxlevel M p.last = some p.length → p.UniqueBridgeOfTenacity t := by
    intro L
    induction L using Nat.strongRecOn with
    | ind L ih =>
      intro p hpL hpt hmax
      have hp := p.shortest_of_maxlevel hmax
      have hpos : 0 < p.length := by
        obtain ⟨e, o, he, ho, _, hop, _⟩ := finite_levels_of_tenacity p.last t hpt
        have hlen : max e o = p.length := by simpa only [maxlevel, he, ho, levelMax, Option.some.injEq] using hmax
        omega
      let pred : Fin (p.length + 1) := ⟨p.length - 1, by omega⟩
      by_cases hpred : p.BFSHonest pred
      · obtain ⟨hfinal, hcases⟩ := p.honest_terminal_bridge_cases hp t hpt hmax hpos hpred
        let I : Fin p.length := ⟨p.length - 1, by omega⟩
        have hnext : p.length - 1 + 1 = p.length := by omega
        rcases hcases with ⟨hbridge, hcase⟩ | ⟨hprop, hten, hmaxpred⟩
        · apply p.unique_bridge_at_split t I (no_bridge (p.take (p.length - 1) (by omega)) hpred hcase)
          · simpa only [I, hnext, last] using hbridge
          · simpa only [I, hnext, last] using hfinal
          · intro j hij _ _
            have := j.isLt
            change p.length - 1 < j.val at hij
            omega
        · have hprefix := ih (p.length - 1) (by omega) (p.take (p.length - 1) (by omega)) rfl hten hmaxpred
          apply p.unique_bridge_of_prefix t (p.length - 1) (by omega) hprefix
          intro j hj hjb _
          have hjeq : j.val = p.length - 1 := by have := j.isLt; omega
          have hprop' : PropEdge M (p.vertex ⟨j.val, by omega⟩) (p.vertex ⟨j.val + 1, by omega⟩) := by
            simpa only [hjeq, hnext, last] using hprop
          exact hjb.2 hprop'
      · obtain ⟨hpo, houter⟩ := p.dishonest_last_predecessor_outer hp t hpt hpos hpred
        have hlow : ∃ s, tenacity M (p.vertex pred) = some s ∧ s < t := by
          by_cases hhigh : levelLE (some t) (tenacity M (p.vertex pred))
          · exact False.elim (hpred (p.limited_bfs_honesty hp pred (by rw [hpt]; exact hhigh)).1)
          · cases hs : tenacity M (p.vertex pred) with
            | none => exact False.elim (hhigh (by rw [hs]; trivial))
            | some s =>
              refine ⟨s, rfl, ?_⟩
              have hn : ¬t ≤ s := by simpa only [hs, levelLE] using hhigh
              omega
        obtain ⟨s, hs, hst⟩ := hlow
        have hsodd := tenacity_odd M (p.vertex pred) s hs
        have hmember := (p.dishonest_outer_predecessor_base hp hpo houter t s hpt hs hst
          (hexists (p.vertex pred) s hs (by omega)) hpred).2
        have hc : levelLT (some (t - 2)) (tenacity M p.last) := by rw [hpt]; change t - 2 < t; omega
        obtain ⟨D, hDo, hDmem, hfirst, htail, _⟩ := p.exists_first_entry_confined_tail hp hpo (t - 2) hc
          (by intro v hv q hq hqf hql; exact hconf p.last v hv hc q hq hqf hql) ⟨pred, hmember⟩
        have hprefix := p.first_entry_prefix_honest hp hpo t hpt hexists hconf D hDo hDmem hfirst htail
        have hentry := p.first_entry_edge_tenacity hp hpo t hpt D hDo hDmem htail hprefix
        let I : Fin p.length := ⟨D.val - 1, by have := D.isLt; omega⟩
        let r := p.take I.val (by omega)
        have hrLast : r.last = p.vertex ⟨D.val - 1, by omega⟩ := rfl
        have hre : r.length % 2 = 0 := by change (D.val - 1) % 2 = 0; omega
        have hnext : D.val - 1 + 1 = D.val := by omega
        have htailno : ∀ j : Fin p.length, I.val < j.val →
            Bridge M (p.vertex ⟨j.val, by omega⟩) (p.vertex ⟨j.val + 1, by omega⟩) →
            edgeTenacity M (p.vertex ⟨j.val, by omega⟩) (p.vertex ⟨j.val + 1, by omega⟩) ≠ some t := by
          intro j hj _
          exact p.first_entry_tail_edge_ne hpo t hpt hedge D hDmem htail j (by change D.val - 1 < j.val at hj; omega)
        by_cases hprop : PropEdge M r.last (p.vertex D)
        · obtain ⟨hrten, hrmax⟩ := p.first_entry_prop_prefix_maxlevel hp hpo t hpt hconf D hDo hDmem
            hfirst htail hprefix hprop
          have hprefixunique := ih r.length (by change D.val - 1 < L; have := D.isLt; omega) r rfl hrten hrmax
          apply p.unique_bridge_of_prefix t I.val (by omega) hprefixunique
          intro j hj hjb hjt
          by_cases hij : I.val < j.val
          · exact htailno j hij hjb hjt
          · have hjeq : j.val = I.val := by omega
            have hprop' : PropEdge M (p.vertex ⟨j.val, by omega⟩) (p.vertex ⟨j.val + 1, by omega⟩) := by
              simpa only [hjeq, I, hnext, hrLast] using hprop
            exact hjb.2 hprop'
        · have hadj : G.Adj r.last (p.vertex D) := by
            have hh := p.adjacent I
            simpa only [I, hnext, hrLast] using hh
          have hbridge : Bridge M r.last (p.vertex D) := ⟨hadj, hprop⟩
          have hm : M.mate r.last ≠ some (p.vertex D) := by
            intro hm
            have hh := (p.alternating I).1 (by simpa only [I, hnext, hrLast] using hm)
            change (D.val - 1) % 2 = 1 at hh
            omega
          have hcase := r.bridge_even_prefix_lower_or_short hprefix hre (p.vertex D) hbridge hm t hentry
          apply p.unique_bridge_at_split t I (no_bridge r hprefix hcase)
          · simpa only [I, hnext, hrLast] using hbridge
          · simpa only [I, hnext] using hentry
          · exact htailno
  exact aux p.length p rfl hpt hmax

/-- Every maxlevel path of tenacity at most the shortest augmenting-path
length contains exactly one bridge of that tenacity. This includes equality
with the shortest augmenting-path length and assumes no structural oracle. -/
theorem general_maxlevel_path_unique_bridge (p : AltPath M) (t : Nat)
    (ht : AtMostShortestAugmenting M t) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length) : p.UniqueBridgeOfTenacity t := by
  have htodd := tenacity_odd M p.last t hpt
  have hcutlt : t - 2 < t := by omega
  have hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b := by
    intro v s hs hst
    have helig : EligibleTenacity M s := by
      refine ⟨tenacity_odd M v s hs, ⟨v, ?_⟩, ?_⟩
      · rw [hs]
        exact Nat.le_refl _
      · intro q hq
        have hbound := ht q hq
        omega
    obtain ⟨b, hb, _⟩ := general_unique_base M s helig v hs
    exact ⟨b, s, hs, hb⟩
  have lowerEligible (b v : V) (hv : Blossom M (t - 2) b v) : EligibleTenacity M (t - 2) := by
    obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound (t - 2) b v hv
    have hsodd := tenacity_odd M v s hs
    refine ⟨by omega, ⟨v, ?_⟩, ?_⟩
    · rw [hs]
      exact hst
    · intro q hq
      have hbound := ht q hq
      omega
  apply unique_bridge_maxlevel_of_lower t htodd hexists
  · intro b v hv hb q hq hqb hqv
    exact general_blossom_relative_confined M (t - 2) (lowerEligible b v hv) b v hv hb q hq hqb hqv
  · intro b v hv hb q hq hqb hqv k
    exact general_blossom_relative_edge_bound M (t - 2) (lowerEligible b v hv) b v hv hb q hq hqb hqv k
  · exact hpt
  · exact hmax

end MaximumMatching.AltPath
