import MaximumMatching.GeneralBridge

/-! The interval after a current-tenacity bridge lies in the lower blossom
of its next high vertex. The actual terminal/first-entry decomposition
identifies that boundary without reversing a crossing-midpoint stretch. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

theorem current_bridge_right_blossom (p : AltPath M) (t : Nat)
    (ht : AtMostShortestAugmenting M t) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length) (I : Fin p.length)
    (hIb : Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩))
    (hIt : edgeTenacity M (p.vertex ⟨I.val, by omega⟩)
      (p.vertex ⟨I.val + 1, by omega⟩) = some t) : ∃ J : Fin (p.length + 1), I.val < J.val ∧ tenacity M (p.vertex J) = some t ∧
        ∀ K : Fin (p.length + 1), I.val < K.val → K.val < J.val →
          Blossom M (t - 2) (p.vertex J) (p.vertex K) := by
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
      ∃ J : Fin (p.length + 1), I.val < J.val ∧ tenacity M (p.vertex J) = some t ∧
        ∀ K : Fin (p.length + 1), I.val < K.val → K.val < J.val →
          Blossom M (t - 2) (p.vertex J) (p.vertex K) := by
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
          (hKm : maxlevel M (p.vertex ⟨K, by omega⟩) = some K) : ∃ J : Fin (p.length + 1), I.val < J.val ∧ tenacity M (p.vertex J) = some t ∧
        ∀ K : Fin (p.length + 1), I.val < K.val → K.val < J.val →
          Blossom M (t - 2) (p.vertex J) (p.vertex K) := by
        let r := p.take K (by omega)
        obtain ⟨J, hJb, hJt, _⟩ := r.general_maxlevel_path_unique_bridge t ht hKt hKm
        have hJp : J.val < p.length := by have := J.isLt; change J.val < K at this; omega
        have hIJ := unique ⟨J.val, hJp⟩ hJb hJt
        change I.val = J.val at hIJ
        obtain ⟨Q, hJQ, hQt, hQbl⟩ := ih K (by omega) r rfl hKt hKm J hJb hJt
        have hQbound : Q.val ≤ K := by have := Q.isLt; change Q.val < K + 1 at this; omega
        refine ⟨⟨Q.val, by omega⟩, by change I.val < Q.val; omega, hQt, ?_⟩
        intro A hIA hAQ
        change A.val < Q.val at hAQ
        exact hQbl ⟨A.val, by change A.val < K + 1; omega⟩
          (by change J.val < A.val; omega) hAQ
      let pred : Fin (p.length + 1) := ⟨p.length - 1, by omega⟩
      by_cases hpred : p.BFSHonest pred
      · obtain ⟨hfinal, hcases⟩ := p.honest_terminal_bridge_cases hp t hpt hmax hpos hpred
        have hnext : p.length - 1 + 1 = p.length := by omega
        rcases hcases with ⟨hbridge, _⟩ | ⟨_, hten, hmaxpred⟩
        · have hI := unique ⟨p.length - 1, by omega⟩
            (by simpa only [hnext, last] using hbridge) (by simpa only [hnext, last] using hfinal)
          change I.val = p.length - 1 at hI
          refine ⟨⟨p.length, by omega⟩, by have := I.isLt; omega, hpt, ?_⟩
          intro K hIK hKL
          change K.val < p.length at hKL
          omega
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
        obtain ⟨D, hDo, hDmem, hfirst, htail, htailmem⟩ := p.exists_first_entry_confined_tail hp hpo (t - 2) hc
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
          change I.val = D.val - 1 at hI
          refine ⟨⟨p.length, by omega⟩, by have := I.isLt; omega, hpt, ?_⟩
          intro K hIK hKL
          change K.val < p.length at hKL
          rcases htailmem K (by omega) with hKeq | hKbl
          · have hh := congrArg Fin.val (p.injective K ⟨p.length, by omega⟩ hKeq)
            dsimp only at hh
            omega
          · exact hKbl
  exact aux p.length p rfl hpt hmax I hIb hIt

/-- The boundary constructed above is precisely any independently selected
first high vertex after the bridge, so the entire initial low stretch has
that actual lower-blossom boundary. -/
theorem current_bridge_first_high_right (p : AltPath M) (t : Nat)
    (ht : AtMostShortestAugmenting M t) (hpt : tenacity M p.last = some t)
    (hmax : maxlevel M p.last = some p.length) (I : Fin p.length)
    (hIb : Bridge M (p.vertex ⟨I.val, by omega⟩) (p.vertex ⟨I.val + 1, by omega⟩))
    (hIt : edgeTenacity M (p.vertex ⟨I.val, by omega⟩)
      (p.vertex ⟨I.val + 1, by omega⟩) = some t)
    (J : Fin (p.length + 1)) (hIJ : I.val < J.val)
    (hJ : levelLT (some (t - 2)) (tenacity M (p.vertex J)))
    (hfirst : ∀ K : Fin (p.length + 1), I.val < K.val → K.val < J.val →
      levelLE (tenacity M (p.vertex K)) (some (t - 2))) :
    tenacity M (p.vertex J) = some t ∧
      ∀ K : Fin (p.length + 1), I.val < K.val → K.val < J.val →
        Blossom M (t - 2) (p.vertex J) (p.vertex K) := by
  obtain ⟨L, hIL, hLt, hLbl⟩ := p.current_bridge_right_blossom t ht hpt hmax I hIb hIt
  have htodd := tenacity_odd M p.last t hpt
  have hJL : J.val = L.val := by
    by_cases hlt : J.val < L.val
    · obtain ⟨s, hs, hsc⟩ := blossom_tenacity_bound (t - 2) (p.vertex L) (p.vertex J) (hLbl J hIJ hlt)
      rw [hs] at hJ
      change t - 2 < s at hJ
      omega
    · by_cases hgt : L.val < J.val
      · have hh := hfirst L hIL hgt
        rw [hLt] at hh
        change t ≤ t - 2 at hh
        omega
      · omega
  have heq : J = L := Fin.ext hJL
  rw [heq]
  exact ⟨hLt, hLbl⟩

end MaximumMatching.AltPath
