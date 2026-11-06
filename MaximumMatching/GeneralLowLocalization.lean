import MaximumMatching.GeneralWeightedEdges

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
