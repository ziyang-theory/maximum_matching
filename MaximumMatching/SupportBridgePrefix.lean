import MaximumMatching.GeneralBridge

/-! The first endpoint of the unique current-tenacity bridge on an actual
maximum-level path has an honest prefix, including when that endpoint lies
inside a lower blossom. This follows the proved terminal/first-entry
decomposition, rather than assuming honesty at low vertices. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

theorem current_bridge_prefix_honest (p : AltPath M) (t : Nat)
    (ht : AtMostShortestAugmenting M t) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length) (I : Fin p.length)
    (hIb : Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩))
    (hIt : edgeTenacity M (p.vertex ⟨I.val, by omega⟩)
      (p.vertex ⟨I.val + 1, by omega⟩) = some t) : p.BFSHonest ⟨I.val, by omega⟩ := by
  have htodd := tenacity_odd M p.last t hpt
  have hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b := by
    intro v s hs hst
    have helig : EligibleTenacity M s := by
      refine ⟨tenacity_odd M v s hs, ⟨v, ?_⟩, ?_⟩
      · rw [hs]; exact Nat.le_refl _
      · intro q hq; have := ht q hq; omega
    obtain ⟨b, hb, _⟩ := general_unique_base M s helig v hs
    exact ⟨b, s, hs, hb⟩
  have hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w := by
    intro b v hv hb q hq hqb hqv
    obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound (t - 2) b v hv
    have hsodd := tenacity_odd M v s hs
    have helig : EligibleTenacity M (t - 2) := by
      refine ⟨by omega, ⟨v, ?_⟩, ?_⟩
      · rw [hs]; exact hst
      · intro r hr; have := ht r hr; omega
    exact general_blossom_relative_confined M (t - 2) helig b v hv hb q hq hqb hqv
  have aux : ∀ L (p : AltPath M), p.length = L → tenacity M p.last = some t →
      maxlevel M p.last = some p.length → ∀ I : Fin p.length,
      Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩) →
      edgeTenacity M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩) = some t →
      p.BFSHonest ⟨I.val, by omega⟩ := by
    intro L
    induction L using Nat.strongRecOn with
    | ind L ih =>
      intro p hpL hpt hmax I hIb hIt
      have hp := p.shortest_of_maxlevel hmax
      have hpos : 0 < p.length := by have := I.isLt; omega
      obtain ⟨Z, _, _, huniq⟩ := p.general_maxlevel_path_unique_bridge t ht hpt hmax
      have unique (J : Fin p.length)
          (hJb : Bridge M (p.vertex ⟨J.val, by omega⟩) (p.vertex ⟨J.val + 1, by omega⟩))
          (hJt : edgeTenacity M (p.vertex ⟨J.val, by omega⟩) (p.vertex ⟨J.val + 1, by omega⟩) = some t) :
          I.val = J.val := congrArg Fin.val ((huniq I hIb hIt).trans (huniq J hJb hJt).symm)
      have recurse (K : Nat) (hK : K < p.length)
          (hKt : tenacity M (p.vertex ⟨K, by omega⟩) = some t)
          (hKm : maxlevel M (p.vertex ⟨K, by omega⟩) = some K) : p.BFSHonest ⟨I.val, by omega⟩ := by
        let r := p.take K (by omega)
        obtain ⟨J, hJb, hJt, _⟩ := r.general_maxlevel_path_unique_bridge t ht hKt hKm
        have hJp : J.val < p.length := by have := J.isLt; change J.val < K at this; omega
        have hIJ := unique ⟨J.val, hJp⟩ hJb hJt
        have hrhon := ih K (by omega) r rfl hKt hKm J hJb hJt
        apply (p.honest_iff_level ⟨I.val, by omega⟩).2
        have hh := (r.honest_iff_level ⟨J.val, by omega⟩).1 hrhon
        change level M (J.val % 2) (p.vertex ⟨J.val, by omega⟩) = some J.val at hh
        simpa only [hIJ] using hh
      let pred : Fin (p.length + 1) := ⟨p.length - 1, by omega⟩
      by_cases hpred : p.BFSHonest pred
      · obtain ⟨hfinal, hcases⟩ := p.honest_terminal_bridge_cases hp t hpt hmax hpos hpred
        have hnext : p.length - 1 + 1 = p.length := by omega
        rcases hcases with ⟨hbridge, _⟩ | ⟨_, hten, hmaxpred⟩
        · have hI := unique ⟨p.length - 1, by omega⟩
            (by simpa only [hnext, last] using hbridge) (by simpa only [hnext, last] using hfinal)
          have hiFin : (⟨I.val, by omega⟩ : Fin (p.length + 1)) = pred := Fin.ext hI
          simpa only [hiFin] using hpred
        · exact recurse (p.length - 1) (by omega) hten hmaxpred
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
        have hnext : D.val - 1 + 1 = D.val := by omega
        let r := p.take (D.val - 1) (by have := D.isLt; omega)
        have hrLast : r.last = p.vertex ⟨D.val - 1, by omega⟩ := rfl
        by_cases hprop : PropEdge M r.last (p.vertex D)
        · obtain ⟨hrten, hrmax⟩ := p.first_entry_prop_prefix_maxlevel hp hpo t hpt hconf D hDo hDmem
            hfirst htail hprefix hprop
          exact recurse (D.val - 1) (by have := D.isLt; omega) hrten hrmax
        · have hadj : G.Adj r.last (p.vertex D) := by
            have hh := p.adjacent ⟨D.val - 1, by have := D.isLt; omega⟩
            simpa only [hnext, hrLast, Fin.eta] using hh
          have hI := unique ⟨D.val - 1, by have := D.isLt; omega⟩
            (by simpa only [hnext, hrLast, Fin.eta] using (show Bridge M r.last (p.vertex D) from ⟨hadj, hprop⟩))
            (by simpa only [hnext] using hentry)
          have hiFin : (⟨I.val, by omega⟩ : Fin (p.length + 1)) = ⟨D.val - 1, by omega⟩ := Fin.ext hI
          simpa only [hiFin] using hprefix
  exact aux p.length p rfl hpt hmax I hIb hIt

end MaximumMatching.AltPath
