import MaximumMatching.BlossomLaminar
import MaximumMatching.Segment

/-! Disjointness of actual paths represented by compressed lower-blossom edges.
The premises are local containment and high endpoints, not a disjoint-path oracle. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A compressed edge is realized by a genuine alternating segment whose
internal vertices belong to the lower-tenacity blossom of its first endpoint.
Its final edge leaves that blossom for another high-tenacity vertex. -/
def BlossomEdgeExpansion (M : Matching G) (t : Nat) (s : AltSegment M) : Prop :=
  levelLT (some t) (tenacity M s.first) ∧
  levelLT (some t) (tenacity M s.last) ∧
  ∀ i : Fin (s.length + 1), 0 < i.val → i.val < s.length →
    Blossom M t s.first (s.vertex i)

namespace BlossomEdgeExpansion

theorem internal_tenacity_bound {t : Nat} {s : AltSegment M}
    (h : BlossomEdgeExpansion M t s) (i : Fin (s.length + 1))
    (hi : 0 < i.val) (hil : i.val < s.length) :
    ∃ k, tenacity M (s.vertex i) = some k ∧ k ≤ t :=
  blossom_tenacity_bound t s.first (s.vertex i) (h.2.2 i hi hil)

/-- An interior vertex cannot equal any vertex above the contraction threshold. -/
theorem internal_ne_high {t : Nat} {s : AltSegment M}
    (h : BlossomEdgeExpansion M t s) (i : Fin (s.length + 1))
    (hi : 0 < i.val) (hil : i.val < s.length) (v : V)
    (hv : levelLT (some t) (tenacity M v)) : s.vertex i ≠ v := by
  intro he
  obtain ⟨k, hk, hkt⟩ := h.internal_tenacity_bound i hi hil
  rw [he] at hk
  rw [hk] at hv
  change t < k at hv
  omega

/-- Distinct compressed-edge bases force their internal expansions to be
mutually disjoint, and also disjoint from each other's high endpoints. -/
theorem internal_disjoint {t : Nat} {s q : AltSegment M}
    (hs : BlossomEdgeExpansion M t s) (hq : BlossomEdgeExpansion M t q)
    (hb : s.first ≠ q.first) (i : Fin (s.length + 1))
    (hi : 0 < i.val) (hil : i.val < s.length) (j : Fin (q.length + 1)) :
    s.vertex i ≠ q.vertex j := by
  by_cases hj0 : j.val = 0
  · have hj : j = ⟨0, by omega⟩ := Fin.ext hj0
    rw [hj]
    exact hs.internal_ne_high i hi hil q.first hq.1
  · by_cases hjl : j.val = q.length
    · have hj : j = ⟨q.length, by omega⟩ := Fin.ext hjl
      rw [hj]
      exact hs.internal_ne_high i hi hil q.last hq.2.1
    · intro he
      have hsi := hs.2.2 i hi hil
      have hqj := hq.2.2 j (by omega) (by omega)
      apply blossoms_disjoint_same_tenacity t s.first q.first hs.1 hq.1 hb (s.vertex i)
      exact ⟨hsi, he.symm ▸ hqj⟩

/-- Any intersection of expansions with distinct bases comes from an
intersection of the original compressed-edge endpoints. -/
theorem intersection_at_endpoints {t : Nat} {s q : AltSegment M}
    (hs : BlossomEdgeExpansion M t s) (hq : BlossomEdgeExpansion M t q)
    (hb : s.first ≠ q.first) (i : Fin (s.length + 1)) (j : Fin (q.length + 1))
    (he : s.vertex i = q.vertex j) :
    (i.val = 0 ∨ i.val = s.length) ∧ (j.val = 0 ∨ j.val = q.length) := by
  constructor
  · by_cases hi0 : i.val = 0
    · exact Or.inl hi0
    · by_cases hil : i.val = s.length
      · exact Or.inr hil
      · exact False.elim (hs.internal_disjoint hq hb i (by omega) (by omega) j he)
  · by_cases hj0 : j.val = 0
    · exact Or.inl hj0
    · by_cases hjl : j.val = q.length
      · exact Or.inr hjl
      · exact False.elim (hq.internal_disjoint hs (Ne.symm hb) j (by omega) (by omega) i he.symm)

/-- Vertex-disjoint compressed edges expand to vertex-disjoint actual
alternating paths. This is the separation step used in the H_v correspondence. -/
theorem disjoint_of_endpoints {t : Nat} {s q : AltSegment M}
    (hs : BlossomEdgeExpansion M t s) (hq : BlossomEdgeExpansion M t q)
    (hff : s.first ≠ q.first) (hfl : s.first ≠ q.last)
    (hlf : s.last ≠ q.first) (hll : s.last ≠ q.last) :
    ∀ i j, s.vertex i ≠ q.vertex j := by
  intro i j he
  obtain ⟨hi, hj⟩ := hs.intersection_at_endpoints hq hff i j he
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · have hi' : i = ⟨0, by omega⟩ := Fin.ext hi
    have hj' : j = ⟨0, by omega⟩ := Fin.ext hj
    exact hff (by simpa only [hi', hj', AltSegment.first, AltSegment.last] using he)
  · have hi' : i = ⟨0, by omega⟩ := Fin.ext hi
    have hj' : j = ⟨q.length, by omega⟩ := Fin.ext hj
    exact hfl (by simpa only [hi', hj', AltSegment.first, AltSegment.last] using he)
  · have hi' : i = ⟨s.length, by omega⟩ := Fin.ext hi
    have hj' : j = ⟨0, by omega⟩ := Fin.ext hj
    exact hlf (by simpa only [hi', hj', AltSegment.first, AltSegment.last] using he)
  · have hi' : i = ⟨s.length, by omega⟩ := Fin.ext hi
    have hj' : j = ⟨q.length, by omega⟩ := Fin.ext hj
    exact hll (by simpa only [hi', hj', AltSegment.first, AltSegment.last] using he)

end BlossomEdgeExpansion

/-- Expand a set of high-tenacity core vertices by their contracted blossoms.
Low-tenacity artificial top vertices are represented by their actual membership
in one of these blossoms; no equality with the core's layer number is asserted. -/
def BlossomHull (M : Matching G) (t : Nat) (core : V → Prop) (v : V) : Prop :=
  core v ∨ ∃ b, core b ∧ Blossom M t b v

/-- Disjoint high-tenacity cores have disjoint expansions. This applies to the
complete vertex sets of two DDFS paths, including their low-tenacity expansions. -/
theorem blossom_hulls_disjoint (t : Nat) (core₁ core₂ : V → Prop)
    (hh₁ : ∀ v, core₁ v → levelLT (some t) (tenacity M v))
    (hh₂ : ∀ v, core₂ v → levelLT (some t) (tenacity M v))
    (hdisj : ∀ v, ¬(core₁ v ∧ core₂ v)) :
    ∀ v, ¬(BlossomHull M t core₁ v ∧ BlossomHull M t core₂ v) := by
  rintro v ⟨hv₁, hv₂⟩
  rcases hv₁ with hv₁ | ⟨b, hb, hbl⟩
  · rcases hv₂ with hv₂ | ⟨c, hc, hcl⟩
    · exact hdisj v ⟨hv₁, hv₂⟩
    · have hhigh := hh₁ v hv₁
      obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound t c v hcl
      rw [hs] at hhigh
      change t < s at hhigh
      omega
  · rcases hv₂ with hv₂ | ⟨c, hc, hcl⟩
    · have hhigh := hh₂ v hv₂
      obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound t b v hbl
      rw [hs] at hhigh
      change t < s at hhigh
      omega
    · have hbc : b ≠ c := by
        intro he
        exact hdisj b ⟨hb, he.symm ▸ hc⟩
      exact blossoms_disjoint_same_tenacity t b c (hh₁ b hb) (hh₂ c hc) hbc v ⟨hbl, hcl⟩

/-- Actual alternating segment realizations contained in disjoint expanded
cores inherit vertex disjointness. The paths themselves retain their verified
simplicity, adjacency and alternation; only their separation is concluded here. -/
theorem alternating_realizations_disjoint (t : Nat) (core₁ core₂ : V → Prop)
    (hh₁ : ∀ v, core₁ v → levelLT (some t) (tenacity M v))
    (hh₂ : ∀ v, core₂ v → levelLT (some t) (tenacity M v))
    (hdisj : ∀ v, ¬(core₁ v ∧ core₂ v)) (p q : AltSegment M)
    (hp : ∀ i, BlossomHull M t core₁ (p.vertex i))
    (hq : ∀ j, BlossomHull M t core₂ (q.vertex j)) :
    ∀ i j, p.vertex i ≠ q.vertex j := by
  intro i j he
  exact blossom_hulls_disjoint t core₁ core₂ hh₁ hh₂ hdisj (p.vertex i)
    ⟨hp i, he.symm ▸ hq j⟩

end MaximumMatching
