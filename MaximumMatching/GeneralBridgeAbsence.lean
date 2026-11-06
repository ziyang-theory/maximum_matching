import MaximumMatching.MinCorrectness
import MaximumMatching.GeneralBlossomJoin
import MaximumMatching.GeneralBlossomMembership

/-! Absence of a specified bridge tenacity on short or lower-tenacity shortest
paths, using only relative edge bounds at the preceding odd cutoff. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Excludes only bridges of the specified tenacity; lower bridges may remain. -/
def NoBridgeOfTenacity (p : AltPath M) (t : Nat) : Prop :=
  ∀ i : Fin p.length, Bridge M (p.vertex ⟨i.val, by omega⟩) (p.vertex ⟨i.val + 1, by omega⟩) →
    edgeTenacity M (p.vertex ⟨i.val, by omega⟩) (p.vertex ⟨i.val + 1, by omega⟩) ≠ some t

/-- An actual lower-blossom suffix cannot contain an edge of the current
threshold. The proof transfers an original edge into the shortest segment. -/
theorem lower_relative_edge_ne (p : AltPath M) (t : Nat)
    (hedge : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ i : Fin q.length, levelLE (edgeTenacity M (q.vertex ⟨i.val, by omega⟩)
          (q.vertex ⟨i.val + 1, by omega⟩)) (some (t - 2)))
    (b : V) (hmem : Blossom M (t - 2) b p.last)
    (hb : levelLT (some (t - 2)) (tenacity M b))
    (A : Fin (p.length + 1)) (hAe : A.val % 2 = 0) (hA : p.vertex A = b)
    (hseg : (p.segment A.val (by omega) hAe).Shortest)
    (htpos : 0 < t) (i : Fin p.length) (hAi : A.val ≤ i.val) :
    edgeTenacity M (p.vertex ⟨i.val, by omega⟩) (p.vertex ⟨i.val + 1, by omega⟩) ≠ some t := by
  let q := p.segment A.val (by omega) hAe
  have hbound := hedge b p.last hmem hb q hseg
    ((p.segment_first _ _ _).trans hA) (p.segment_last _ _ _)
    ⟨i.val - A.val, by change i.val - A.val < p.length - A.val; omega⟩
  have hleft : q.vertex ⟨i.val - A.val, by change i.val - A.val < p.length - A.val + 1; omega⟩ =
      p.vertex ⟨i.val, by omega⟩ := by
    change p.vertex ⟨A.val + (i.val - A.val), _⟩ = _
    congr 1
    apply Fin.ext
    change A.val + (i.val - A.val) = i.val
    omega
  have hright : q.vertex ⟨i.val - A.val + 1, by change i.val - A.val + 1 < p.length - A.val + 1; omega⟩ =
      p.vertex ⟨i.val + 1, by omega⟩ := by
    change p.vertex ⟨A.val + (i.val - A.val + 1), _⟩ = _
    congr 1
    apply Fin.ext
    change A.val + (i.val - A.val + 1) = i.val + 1
    omega
  rw [hleft, hright] at hbound
  intro he
  rw [he] at hbound
  change t ≤ t - 2 at hbound
  omega

/-- A shortest path shorter than half the threshold has no bridge of that
threshold. Low blossoms may occur anywhere on the path. -/
theorem short_shortest_no_bridge (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b)
    (hedge : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ i : Fin q.length, levelLE (edgeTenacity M (q.vertex ⟨i.val, by omega⟩)
          (q.vertex ⟨i.val + 1, by omega⟩)) (some (t - 2)))
    (p : AltPath M) (hp : p.Shortest) (hlen : 2 * p.length < t) : p.NoBridgeOfTenacity t := by
  have aux : ∀ L (p : AltPath M), p.length = L → p.Shortest → 2 * p.length < t →
      p.NoBridgeOfTenacity t := by
    intro L
    induction L using Nat.strongRecOn with
    | ind L ih =>
      intro p hpL hp hlen i hib hit
      have hpos : 0 < p.length := by have := i.isLt; omega
      have htlow : (t - 2) % 2 = 1 := by omega
      by_cases hhigh : levelLE (some t) (tenacity M p.last)
      · have hmin : minlevel M p.last = some p.length := minlevel_of_below_half p.last p.length t
          ((level_eq_some_iff M (p.length % 2) p.last p.length).2 hp) hlen hhigh
        have hpred := p.minlevel_last_predecessor_honest hmin hpos
        by_cases hi : i.val < p.length - 1
        · exact ih (p.length - 1) (by omega) (p.take (p.length - 1) (by omega)) rfl hpred
            (by change 2 * (p.length - 1) < t; omega) ⟨i.val, hi⟩ hib hit
        · have hieq : i.val = p.length - 1 := by have := i.isLt; omega
          have hv : p.vertex ⟨i.val + 1, by omega⟩ = p.last := by
            congr 1
            apply Fin.ext
            change i.val + 1 = p.length
            omega
          apply hib.2
          apply Or.inl
          refine ⟨p, hv.symm, ?_, hpos, ?_⟩
          · rw [hv]
            exact hmin
          · congr 1
            exact Fin.ext hieq.symm
      · have hlow : ∃ s, tenacity M p.last = some s ∧ s ≤ t - 2 := by
          cases hs : tenacity M p.last with
          | none => exact False.elim (hhigh (by rw [hs]; trivial))
          | some s =>
            have hsodd := tenacity_odd M p.last s hs
            have hn : ¬t ≤ s := by simpa only [hs, levelLE] using hhigh
            exact ⟨s, rfl, by omega⟩
        obtain ⟨s, hs, hst⟩ := hlow
        obtain ⟨b, hb, hmem⟩ := blossom_cover_of_base_existence (t - 2) htlow hexists p.last s hs hst
        obtain ⟨A, hAe, hA, hprefix, hseg⟩ := blossom_shortest_relative (t - 2) b p.last hmem hb p rfl hp
        have hAlt : A.val < p.length := by
          by_cases he : A.val = p.length
          · have hA' : A = ⟨p.length, by omega⟩ := Fin.ext he
            have hbend : p.last = b := by simpa only [hA', last] using hA
            exact False.elim (blossom_excludes_base (t - 2) b hb (hbend ▸ hmem))
          · have := A.isLt
            omega
        by_cases hi : i.val < A.val
        · exact ih A.val (by omega) (p.take A.val (by omega)) rfl hprefix
            (by change 2 * A.val < t; omega) ⟨i.val, hi⟩ hib hit
        · exact p.lower_relative_edge_ne t hedge b hmem hb A hAe hA hseg (by omega) i (by omega) hit
  exact aux p.length p rfl hp hlen

/-- A shortest path to a lower-tenacity endpoint has no bridge of the current
threshold. Its prefix to the lower boundary is short; its suffix uses lower
relative edge bounds. -/
theorem lower_shortest_no_bridge (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b)
    (hedge : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ i : Fin q.length, levelLE (edgeTenacity M (q.vertex ⟨i.val, by omega⟩)
          (q.vertex ⟨i.val + 1, by omega⟩)) (some (t - 2)))
    (p : AltPath M) (hp : p.Shortest) (s : Nat) (hs : tenacity M p.last = some s) (hst : s < t) :
    p.NoBridgeOfTenacity t := by
  have hsodd := tenacity_odd M p.last s hs
  have htlow : (t - 2) % 2 = 1 := by omega
  obtain ⟨b, hb, hmem⟩ := blossom_cover_of_base_existence (t - 2) htlow hexists p.last s hs (by omega)
  obtain ⟨A, hAe, hA, hprefix, hseg⟩ := blossom_shortest_relative (t - 2) b p.last hmem hb p rfl hp
  let q := p.take A.val (by omega)
  let r := p.segment A.val (by omega) hAe
  have hrfirst : r.first = b := (p.segment_first _ _ _).trans hA
  have hrlast : r.last = p.last := p.segment_last _ _ _
  have hbound := (blossom_relative_length_formula (t - 2) b p.last hmem hb q hprefix hAe hA
    r hseg hrfirst hrlast s hs).2
  change 2 * A.val + (p.length - A.val) ≤ s at hbound
  have hshort : 2 * A.val < t := by have := A.isLt; omega
  have hprefixno := short_shortest_no_bridge t ht hexists hedge q hprefix hshort
  intro i hib hit
  by_cases hi : i.val < A.val
  · exact hprefixno ⟨i.val, hi⟩ hib hit
  · exact p.lower_relative_edge_ne t hedge b hmem hb A hAe hA hseg (by omega) i (by omega) hit

end MaximumMatching.AltPath
