import MaximumMatching.BlossomStructure
import MaximumMatching.DDFSPaths
import MaximumMatching.GeneralBaseStructure
import MaximumMatching.RelativePaths

section BlossomExpansion

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

end BlossomExpansion

section WeightedExpansion

/-! Weighted expansion of layered paths through disjoint lower blossoms.

A directed edge carries an actual simple alternating segment. Its length is
independent of the layered graph's edge count. The concatenation below derives
simplicity from blossom separation and strict layer descent, and retains the
sum of the supplied edge lengths. Selecting these segments for the source's
higher-tenacity graph remains a separate construction obligation.
-/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A simple alternating segment with an explicit starting phase. A phase of
zero gives the usual unmatched-first convention; phase one starts matched. -/
structure ParitySegment (M : Matching G) where
  phase : Nat
  length : Nat
  vertex : Fin (length + 1) → V
  injective : ∀ i j, vertex i = vertex j → i = j
  adjacent : ∀ i : Fin length,
    G.Adj (vertex ⟨i.val, by omega⟩) (vertex ⟨i.val + 1, by omega⟩)
  alternating : ∀ i : Fin length,
    (M.mate (vertex ⟨i.val, by omega⟩) = some (vertex ⟨i.val + 1, by omega⟩)) ↔
      (phase + i.val) % 2 = 1

namespace ParitySegment

def first (s : ParitySegment M) : V := s.vertex ⟨0, by omega⟩
def last (s : ParitySegment M) : V := s.vertex ⟨s.length, by omega⟩
def Contains (s : ParitySegment M) (v : V) : Prop := ∃ i, s.vertex i = v

def trivial (M : Matching G) (v : V) (phase : Nat) : ParitySegment M where
  phase := phase
  length := 0
  vertex := fun _ => v
  injective := by intro i j _; apply Fin.ext; omega
  adjacent := by intro i; exact Fin.elim0 i
  alternating := by intro i; exact Fin.elim0 i

def ofAltSegment (s : AltSegment M) : ParitySegment M where
  phase := 0
  length := s.length
  vertex := s.vertex
  injective := s.injective
  adjacent := s.adjacent
  alternating := by simpa using s.alternating

/-- Recover the existing unmatched-first segment interface. -/
def toAltSegment (s : ParitySegment M) (hp : s.phase % 2 = 0) : AltSegment M where
  length := s.length
  vertex := s.vertex
  injective := s.injective
  adjacent := s.adjacent
  alternating := by
    intro i
    have hh := s.alternating i
    have he : (s.phase + i.val) % 2 = i.val % 2 := by omega
    simpa only [he] using hh

/-- A genuine graph edge with the specified matching phase. -/
def ofEdge (u v : V) (phase : Nat) (hadj : G.Adj u v)
    (hmatch : (M.mate u = some v) ↔ phase % 2 = 1) : ParitySegment M where
  phase := phase
  length := 1
  vertex i := if i.val = 0 then u else v
  injective := by
    intro i j hij
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
    · exact Fin.ext (hi.trans hj.symm)
    · have huv : u = v := by simpa only [hi, hj, ite_true, ite_false] using hij
      exact False.elim (G.loopless v (huv ▸ hadj))
    · have hvu : v = u := by simpa only [hi, hj, ite_true, ite_false] using hij
      exact False.elim (G.loopless u (hvu ▸ hadj))
    · apply Fin.ext; omega
  adjacent := by
    intro i
    have hi : i.val = 0 := by omega
    simpa only [hi, Nat.zero_add, ite_true, ite_false, Nat.one_ne_zero] using hadj
  alternating := by
    intro i
    have hi : i.val = 0 := by omega
    simpa only [hi, Nat.zero_add, Nat.add_zero, ite_true, ite_false, Nat.one_ne_zero] using hmatch

@[simp] theorem ofEdge_first (u v : V) (phase : Nat) (hadj : G.Adj u v)
    (hm : (M.mate u = some v) ↔ phase % 2 = 1) :
    (ofEdge u v phase hadj hm).first = u := rfl

@[simp] theorem ofEdge_last (u v : V) (phase : Nat) (hadj : G.Adj u v)
    (hm : (M.mate u = some v) ↔ phase % 2 = 1) :
    (ofEdge u v phase hadj hm).last = v := rfl

/-- Append two actual segments whose phases agree at their common endpoint.
Only the endpoint may be shared. -/
def append (p q : ParitySegment M)
    (hphase : (p.phase + p.length) % 2 = q.phase % 2)
    (hjoin : p.last = q.first)
    (hdis : ∀ (i : Fin (p.length + 1)) (j : Fin (q.length + 1)),
      0 < j.val → p.vertex i ≠ q.vertex j) : ParitySegment M where
  phase := p.phase
  length := p.length + q.length
  vertex i := if h : i.val ≤ p.length then p.vertex ⟨i.val, by omega⟩
    else q.vertex ⟨i.val - p.length, by omega⟩
  injective := by
    intro i j hij
    split at hij <;> split at hij
    · have hh := congrArg (fun x : Fin (p.length + 1) => x.val) (p.injective _ _ hij)
      exact Fin.ext hh
    · exact False.elim (hdis ⟨i.val, by omega⟩ ⟨j.val - p.length, by omega⟩
        (by change 0 < j.val - p.length; omega) hij)
    · exact False.elim (hdis ⟨j.val, by omega⟩ ⟨i.val - p.length, by omega⟩
        (by change 0 < i.val - p.length; omega) hij.symm)
    · have hh := congrArg (fun x : Fin (q.length + 1) => x.val) (q.injective _ _ hij)
      apply Fin.ext
      dsimp only at hh
      omega
  adjacent := by
    intro i
    by_cases hi : i.val < p.length
    · simpa only [dite_eq_left (show i.val ≤ p.length by omega),
        dite_eq_left (show i.val + 1 ≤ p.length by omega)] using p.adjacent ⟨i.val, hi⟩
    · have hs := q.adjacent ⟨i.val - p.length, by omega⟩
      by_cases he : i.val = p.length
      · simp only [he, Nat.le_refl, dite_true, show ¬p.length + 1 ≤ p.length by omega, dite_false]
        change G.Adj p.last (q.vertex ⟨p.length + 1 - p.length, by omega⟩)
        rw [hjoin]
        simpa only [he, Nat.sub_self, Nat.zero_add, Nat.add_sub_cancel_left, first] using hs
      · simpa only [dite_eq_right (show ¬i.val ≤ p.length by omega),
          dite_eq_right (show ¬i.val + 1 ≤ p.length by omega),
          show i.val - p.length + 1 = i.val + 1 - p.length by omega] using hs
  alternating := by
    intro i
    by_cases hi : i.val < p.length
    · simpa only [dite_eq_left (show i.val ≤ p.length by omega),
        dite_eq_left (show i.val + 1 ≤ p.length by omega)] using p.alternating ⟨i.val, hi⟩
    · have hs := q.alternating ⟨i.val - p.length, by omega⟩
      have hpar : (q.phase + (i.val - p.length)) % 2 = (p.phase + i.val) % 2 := by omega
      by_cases he : i.val = p.length
      · simp only [he, Nat.le_refl, dite_true, show ¬p.length + 1 ≤ p.length by omega, dite_false]
        change (M.mate p.last = some (q.vertex ⟨p.length + 1 - p.length, by omega⟩)) ↔
          (p.phase + p.length) % 2 = 1
        rw [hjoin]
        simpa only [he, Nat.sub_self, Nat.zero_add, Nat.add_zero, Nat.add_sub_cancel_left, first, ← hphase] using hs
      · simpa only [dite_eq_right (show ¬i.val ≤ p.length by omega),
          dite_eq_right (show ¬i.val + 1 ≤ p.length by omega), hpar,
          show i.val - p.length + 1 = i.val + 1 - p.length by omega] using hs

@[simp] theorem append_phase (p q : ParitySegment M) (hp) (hj) (hd) :
    (p.append q hp hj hd).phase = p.phase := rfl

@[simp] theorem append_length (p q : ParitySegment M) (hp) (hj) (hd) :
    (p.append q hp hj hd).length = p.length + q.length := rfl

@[simp] theorem append_first (p q : ParitySegment M) (hp) (hj) (hd) :
    (p.append q hp hj hd).first = p.first := by simp [first, append]

@[simp] theorem append_last (p q : ParitySegment M) (hp) (hj) (hd) :
    (p.append q hp hj hd).last = q.last := by
  by_cases hz : q.length = 0
  · have hqe : q.first = q.last := congrArg q.vertex (Fin.ext (by omega))
    simpa [last, append, hz] using hj.trans hqe
  · simp only [last, append, dite_eq_right (by omega : ¬p.length + q.length ≤ p.length),
      Nat.add_sub_cancel_left]

theorem contains_append_iff (p q : ParitySegment M) (hp) (hj) (hd) (v : V) :
    (p.append q hp hj hd).Contains v ↔ p.Contains v ∨ q.Contains v := by
  constructor
  · rintro ⟨i, hi⟩
    change (if h : i.val ≤ p.length then p.vertex ⟨i.val, _⟩ else q.vertex ⟨i.val - p.length, _⟩) = v at hi
    split at hi
    · exact Or.inl ⟨_, hi⟩
    · exact Or.inr ⟨_, hi⟩
  · rintro (⟨i, hi⟩ | ⟨j, hjv⟩)
    · refine ⟨⟨i.val, by change i.val < p.length + q.length + 1; omega⟩, ?_⟩
      simpa [append, show i.val ≤ p.length by omega] using hi
    · refine ⟨⟨p.length + j.val, by change p.length + j.val < p.length + q.length + 1; omega⟩, ?_⟩
      by_cases hj0 : j.val = 0
      · have hjfirst : q.first = v := by
          have he : j = ⟨0, by omega⟩ := Fin.ext hj0
          rw [he] at hjv
          exact hjv
        simpa [append, hj0, last] using hj.trans hjfirst
      · simpa [append, show ¬p.length + j.val ≤ p.length by omega] using hjv

/-- Reversal changes the starting phase according to the actual segment
length, including when that length differs from the compressed edge count. -/
def reverse (s : ParitySegment M) : ParitySegment M where
  phase := s.phase + s.length + 1
  length := s.length
  vertex i := s.vertex ⟨s.length - i.val, by omega⟩
  injective := by
    intro i j h
    have hh := congrArg Fin.val (s.injective _ _ h)
    apply Fin.ext
    change s.length - i.val = s.length - j.val at hh
    omega
  adjacent i := by
    have h := G.symm (s.adjacent ⟨s.length - i.val - 1, by omega⟩)
    simpa only [show s.length - i.val - 1 = s.length - (i.val + 1) by omega,
      show s.length - (i.val + 1) + 1 = s.length - i.val by omega] using h
  alternating i := by
    have h := s.alternating ⟨s.length - i.val - 1, by omega⟩
    have he : s.length - i.val - 1 = s.length - (i.val + 1) := by omega
    have hp : (s.phase + (s.length - i.val - 1)) % 2 =
        (s.phase + s.length + 1 + i.val) % 2 := by omega
    rw [hp] at h
    have h' : (M.mate (s.vertex ⟨s.length - (i.val + 1), by omega⟩) =
        some (s.vertex ⟨s.length - i.val, by omega⟩)) ↔
        (s.phase + s.length + 1 + i.val) % 2 = 1 := by
      simpa only [he, show s.length - (i.val + 1) + 1 = s.length - i.val by omega] using h
    exact ⟨fun hm => h'.1 (M.symm hm), fun hi => M.symm (h'.2 hi)⟩

@[simp] theorem reverse_first (s : ParitySegment M) : s.reverse.first = s.last := by
  simp [reverse, first, last]

@[simp] theorem reverse_last (s : ParitySegment M) : s.reverse.last = s.first := by
  simp [reverse, first, last]

theorem contains_reverse_iff (s : ParitySegment M) (v : V) :
    s.reverse.Contains v ↔ s.Contains v := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨⟨s.length - i.val, by omega⟩, hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨⟨s.length - i.val, by change s.length - i.val < s.length + 1; omega⟩, ?_⟩
    change s.vertex ⟨s.length - (s.length - i.val), _⟩ = v
    simpa only [show s.length - (s.length - i.val) = i.val by omega, Fin.eta] using hi

end ParitySegment

namespace DDFS
variable {H : LayeredGraph V}

/-- The final edge of a nonempty directed path, with endpoints written as
its prefix's last vertex and its own last vertex. -/
theorem Path.last_edge (q : Path H) (hq : 0 < q.length) :
    H.Edge (q.take (q.length - 1) (by omega)).last q.last := by
  have he := q.adjacent ⟨q.length - 1, by omega⟩
  change H.Edge (q.vertex ⟨q.length - 1, _⟩) (q.vertex ⟨q.length, _⟩)
  simpa only [show q.length - 1 + 1 = q.length by omega] using he

/-- Local input for weighted expansion. The segments are actual paths in the
matching graph. The phase is unrelated to the assigned DDFS layer. Interior
containment is in the target blossom, as for a downward edge that reverses
a blossom-base-to-exit segment; global path simplicity is derived. -/
structure BlossomWeightedMatching (M : Matching G) (H : LayeredGraph V) (t : Nat) where
  phase : V → Nat
  segment : ∀ {u v}, H.Edge u v → ParitySegment M
  first : ∀ {u v} (he : H.Edge u v), (segment he).first = u
  last : ∀ {u v} (he : H.Edge u v), (segment he).last = v
  start_phase : ∀ {u v} (he : H.Edge u v), (segment he).phase % 2 = phase u % 2
  end_phase : ∀ {u v} (he : H.Edge u v),
    ((segment he).phase + (segment he).length) % 2 = phase v % 2
  interior : ∀ {u v} (he : H.Edge u v) (i : Fin ((segment he).length + 1)),
    0 < i.val → i.val < (segment he).length → Blossom M t v ((segment he).vertex i)

namespace BlossomWeightedMatching
variable {t : Nat}

/-- The sum of the actual edge-realization lengths, not the number of
compressed edges or the difference between assigned DDFS layers. -/
def weight (W : BlossomWeightedMatching M H t) (q : Path H) : Nat :=
  if h : q.length = 0 then 0
  else W.weight (q.take (q.length - 1) (by omega)) +
    (W.segment (q.last_edge (by omega))).length
termination_by q.length
decreasing_by simp only [Path.take]; omega

private theorem hull_mono {core core' : V → Prop}
    (h : ∀ v, core v → core' v) {v : V} :
    BlossomHull M t core v → BlossomHull M t core' v := by
  rintro (hv | ⟨b, hb, hbl⟩)
  · exact Or.inl (h v hv)
  · exact Or.inr ⟨b, h b hb, hbl⟩

/-- Construct a simple alternating realization of a weighted directed path.
No cross-segment avoidance premise is assumed: it follows from the path's
strict layer descent and disjointness of equal-threshold blossoms. -/
theorem realize (W : BlossomWeightedMatching M H t) (q : Path H)
    (hhigh : ∀ v, q.Contains v → levelLT (some t) (tenacity M v)) :
    ∃ s : ParitySegment M, s.first = q.first ∧ s.last = q.last ∧
      s.length = W.weight q ∧ s.phase % 2 = W.phase q.first % 2 ∧
      (s.phase + s.length) % 2 = W.phase q.last % 2 ∧
      (∀ v, s.Contains v → BlossomHull M t q.Contains v) := by
  by_cases hz : q.length = 0
  · let s := ParitySegment.trivial M q.first (W.phase q.first)
    have hq : q.first = q.last := congrArg q.vertex (Fin.ext (by omega))
    refine ⟨s, rfl, hq, ?_, rfl, ?_, ?_⟩
    · simp [s, weight, hz, ParitySegment.trivial]
    · change (W.phase q.first + 0) % 2 = W.phase q.last % 2
      simp only [Nat.add_zero, hq]
    · rintro v ⟨i, hi⟩
      change q.first = v at hi
      exact Or.inl (hi ▸ q.contains_first)
  · let initial := q.take (q.length - 1) (by omega)
    let he : H.Edge initial.last q.last := q.last_edge (by omega)
    let a := W.segment he
    obtain ⟨s, hsf, hsl, hslen, hsphase, hsend, hshull⟩ := W.realize initial
      (fun v hv => hhigh v (q.contains_take (q.length - 1) (by omega) hv))
    have hjoin : s.last = a.first := hsl.trans (W.first he).symm
    have hphase : (s.phase + s.length) % 2 = a.phase % 2 := hsend.trans (W.start_phase he).symm
    have hcores : ∀ v, ¬(initial.Contains v ∧ v = q.last) := by
      rintro v ⟨⟨i, hi⟩, rfl⟩
      change q.vertex ⟨i.val, _⟩ = q.last at hi
      have hidx := congrArg Fin.val (q.injective _ ⟨q.length, by omega⟩ hi)
      have hib := i.isLt
      change i.val < q.length - 1 + 1 at hib
      dsimp only at hidx
      omega
    have hsep := blossom_hulls_disjoint t initial.Contains (fun v => v = q.last)
      (fun v hv => hhigh v (q.contains_take (q.length - 1) (by omega) hv))
      (fun v hv => hv.symm ▸ hhigh q.last q.contains_last) hcores
    have hdis : ∀ (i : Fin (s.length + 1)) (j : Fin (a.length + 1)),
        0 < j.val → s.vertex i ≠ a.vertex j := by
      intro i j hj hij
      have haj : BlossomHull M t (fun v => v = q.last) (a.vertex j) := by
        by_cases hjl : j.val = a.length
        · exact Or.inl ((congrArg a.vertex (Fin.ext hjl)).trans (W.last he))
        · exact Or.inr ⟨q.last, rfl,
            W.interior he j hj (show j.val < a.length by omega)⟩
      exact hsep (s.vertex i) ⟨hshull (s.vertex i) ⟨i, rfl⟩, hij.symm ▸ haj⟩
    let r := s.append a hphase hjoin hdis
    refine ⟨r, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (s.append_first a hphase hjoin hdis).trans hsf
    · exact (s.append_last a hphase hjoin hdis).trans (W.last he)
    · change s.length + a.length = W.weight q
      rw [weight, dite_eq_right hz, ← hslen]
    · exact hsphase
    · have haend := W.end_phase he
      change (a.phase + a.length) % 2 = W.phase q.last % 2 at haend
      change (s.phase + (s.length + a.length)) % 2 = W.phase q.last % 2
      omega
    · intro v hv
      rcases (s.contains_append_iff a hphase hjoin hdis v).1 hv with hs | ha
      · exact hull_mono (fun _ hv => q.contains_take (q.length - 1) (by omega) hv) (hshull v hs)
      · obtain ⟨i, hi⟩ := ha
        by_cases hi0 : i.val = 0
        · have heq : a.vertex i = initial.last :=
            (congrArg a.vertex (Fin.ext hi0)).trans (W.first he)
          have hh := q.contains_take (q.length - 1) (by omega) initial.contains_last
          exact Or.inl ((hi.symm.trans heq).symm ▸ hh)
        · by_cases hil : i.val = a.length
          · have heq : a.vertex i = q.last :=
              (congrArg a.vertex (Fin.ext hil)).trans (W.last he)
            exact Or.inl ((hi.symm.trans heq).symm ▸ q.contains_last)
          · exact Or.inr ⟨q.last, q.contains_last,
              hi ▸ W.interior he i (by omega) (show i.val < a.length by omega)⟩
termination_by q.length
decreasing_by change q.length - 1 < q.length; omega

/-- Every compressed edge has a positive-length realization: a zero-length
segment would identify endpoints of a strictly descending edge. -/
theorem segment_pos (W : BlossomWeightedMatching M H t) {u v : V} (he : H.Edge u v) :
    0 < (W.segment he).length := by
  by_cases hz : (W.segment he).length = 0
  · have hends : (W.segment he).first = (W.segment he).last :=
      congrArg (W.segment he).vertex (Fin.ext (by omega))
    rw [W.first he, W.last he] at hends
    have hd := H.decreases he
    rw [hends] at hd
    omega
  · omega

/-- The actual path has at least as many edges as its compressed path. -/
theorem length_le_weight (W : BlossomWeightedMatching M H t) (q : Path H) :
    q.length ≤ W.weight q := by
  by_cases hz : q.length = 0
  · simp [hz, weight]
  · have ih := W.length_le_weight (q.take (q.length - 1) (by omega))
    have hp := W.segment_pos (q.last_edge (by omega))
    rw [weight, dite_eq_right hz]
    change q.length - 1 ≤ W.weight (q.take (q.length - 1) (by omega)) at ih
    omega
termination_by q.length
decreasing_by change q.length - 1 < q.length; omega

/-- Two vertex-disjoint high-tenacity core paths have actual, simple,
vertex-disjoint weighted realizations. Their respective lengths are the sums
of their own edge lengths. -/
theorem realize_disjoint (W : BlossomWeightedMatching M H t) (p q : Path H)
    (hp : ∀ v, p.Contains v → levelLT (some t) (tenacity M v))
    (hq : ∀ v, q.Contains v → levelLT (some t) (tenacity M v))
    (hdis : p.Disjoint q) :
    ∃ s r : ParitySegment M,
      s.first = p.first ∧ s.last = p.last ∧ s.length = W.weight p ∧
      r.first = q.first ∧ r.last = q.last ∧ r.length = W.weight q ∧
      s.phase % 2 = W.phase p.first % 2 ∧ r.phase % 2 = W.phase q.first % 2 ∧
      (∀ i j, s.vertex i ≠ r.vertex j) := by
  obtain ⟨s, hsf, hsl, hsn, hsp, _, hsh⟩ := W.realize p hp
  obtain ⟨r, hrf, hrl, hrn, hrp, _, hrh⟩ := W.realize q hq
  refine ⟨s, r, hsf, hsl, hsn, hrf, hrl, hrn, hsp, hrp, ?_⟩
  intro i j he
  exact blossom_hulls_disjoint t p.Contains q.Contains hp hq
    (fun v h => hdis v h.1 h.2) (s.vertex i)
    ⟨hsh (s.vertex i) ⟨i, rfl⟩, he.symm ▸ hrh (r.vertex j) ⟨j, rfl⟩⟩

/-- An even starting phase exposes the realized path through the existing
unmatched-first relative-path interface. -/
theorem realize_altSegment (W : BlossomWeightedMatching M H t) (q : Path H)
    (hhigh : ∀ v, q.Contains v → levelLT (some t) (tenacity M v))
    (hphase : W.phase q.first % 2 = 0) :
    ∃ s : AltSegment M, s.first = q.first ∧ s.last = q.last ∧
      s.length = W.weight q ∧
      (∀ v, s.Contains v → BlossomHull M t q.Contains v) := by
  obtain ⟨s, hsf, hsl, hsn, hsp, _, hsh⟩ := W.realize q hhigh
  refine ⟨s.toAltSegment (hsp.trans hphase), hsf, hsl, hsn, hsh⟩

/-- When the end phase is odd, the reversed weighted path starts unmatched.
The first vertex is the original directed path's last vertex. -/
theorem realize_reverse_altSegment (W : BlossomWeightedMatching M H t) (q : Path H)
    (hhigh : ∀ v, q.Contains v → levelLT (some t) (tenacity M v))
    (hphase : W.phase q.last % 2 = 1) :
    ∃ s : AltSegment M, s.first = q.last ∧ s.last = q.first ∧
      s.length = W.weight q ∧
      (∀ v, s.Contains v → BlossomHull M t q.Contains v) := by
  obtain ⟨s, hsf, hsl, hsn, _, hsp, hsh⟩ := W.realize q hhigh
  have he : s.reverse.phase % 2 = 0 := by
    change (s.phase + s.length + 1) % 2 = 0
    omega
  refine ⟨s.reverse.toAltSegment he, ?_, ?_, hsn, ?_⟩
  · exact s.reverse_first.trans hsl
  · exact s.reverse_last.trans hsf
  · intro v hv
    exact hsh v ((s.contains_reverse_iff v).1 hv)

end BlossomWeightedMatching
end DDFS
end MaximumMatching

end WeightedExpansion

section MinimumWeightedExpansion

/-! Construct compressed-edge realizations from actual minimum-tenacity
blossom paths and an exit edge. Freshness follows from the blossom's tenacity
bound; it is not an input disjointness premise. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A shortest relative path in a minimum-tenacity blossom extends through
any phase-compatible exit edge to a different high-tenacity vertex. -/
theorem IsBase.minimum_exit_segment {u b v : V} (hb : IsBase M u b)
    (t : Nat) (ht : EligibleTenacity M t) (hut : tenacity M u = some t)
    (hmin : ∀ w : V, levelLE (some t) (tenacity M w))
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqu : q.last = u)
    (hv : levelLT (some t) (tenacity M v)) (hvb : v ≠ b)
    (hadj : G.Adj u v) (hmatch : (M.mate u = some v) ↔ q.length % 2 = 1) :
    ∃ s : AltSegment M, s.first = b ∧ s.last = v ∧ s.length = q.length + 1 ∧
      BlossomEdgeExpansion M t s := by
  let a := ParitySegment.ofAltSegment q
  let e := ParitySegment.ofEdge u v q.length hadj hmatch
  have hphase : (a.phase + a.length) % 2 = e.phase % 2 := by
    simp [a, e, ParitySegment.ofAltSegment, ParitySegment.ofEdge]
  have hjoin : a.last = e.first := hqu
  have hfresh (i : Fin (q.length + 1)) : q.vertex i ≠ v := by
    intro he
    have hc := hb.minimum_relative_confined t ht hut hmin q hq hqb hqu
      (q.vertex i) ⟨i, rfl⟩
    rcases hc with hc | hc
    · exact hvb (he.symm.trans hc)
    · obtain ⟨k, hk, hkt⟩ := blossom_tenacity_bound t b (q.vertex i) hc
      rw [he] at hk
      rw [hk] at hv
      change t < k at hv
      omega
  have hdis : ∀ (i : Fin (a.length + 1)) (j : Fin (e.length + 1)),
      0 < j.val → a.vertex i ≠ e.vertex j := by
    intro i j hj
    change q.vertex i ≠ (if j.val = 0 then u else v)
    simpa only [ite_eq_right (show ¬j.val = 0 by omega)] using hfresh i
  let r := a.append e hphase hjoin hdis
  let s := r.toAltSegment (by rfl)
  have hsf : s.first = b := (a.append_first e hphase hjoin hdis).trans hqb
  have hsl : s.last = v := (a.append_last e hphase hjoin hdis).trans rfl
  have hsn : s.length = q.length + 1 := rfl
  refine ⟨s, hsf, hsl, hsn, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hsf]
    simpa only [hut] using hb.high
  · rw [hsl]
    exact hv
  · intro i hi hil
    have hil' : i.val ≤ q.length := by change i.val < q.length + 1 at hil; omega
    have hc := (hb.minimum_relative_properties t ht hut hmin q hq hqb hqu).1
      ⟨i.val, by omega⟩ hi
    change Blossom M t s.first (r.vertex i)
    rw [hsf]
    simpa only [r, ParitySegment.append, dite_eq_left hil', a, ParitySegment.ofAltSegment] using hc

/-- Reverse the constructed base-to-exit path. The lower blossom is now at
the target of the directed edge, as required by ordinary downward H_v edges.
The starting matching phase uses the actual expanded length. -/
theorem IsBase.minimum_exit_reverse {u b v : V} (hb : IsBase M u b)
    (t : Nat) (ht : EligibleTenacity M t) (hut : tenacity M u = some t)
    (hmin : ∀ w : V, levelLE (some t) (tenacity M w))
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqu : q.last = u)
    (hv : levelLT (some t) (tenacity M v)) (hvb : v ≠ b)
    (hadj : G.Adj u v) (hmatch : (M.mate u = some v) ↔ q.length % 2 = 1) :
    ∃ s : ParitySegment M, s.first = v ∧ s.last = b ∧ s.length = q.length + 1 ∧
      s.phase % 2 = (q.length + 2) % 2 ∧
      (∀ i : Fin (s.length + 1), 0 < i.val → i.val < s.length →
        Blossom M t b (s.vertex i)) := by
  obtain ⟨a, haf, hal, han, hax⟩ :=
    hb.minimum_exit_segment t ht hut hmin q hq hqb hqu hv hvb hadj hmatch
  let s := (ParitySegment.ofAltSegment a).reverse
  refine ⟨s, ?_, ?_, han, ?_, ?_⟩
  · exact (ParitySegment.ofAltSegment a).reverse_first.trans hal
  · exact (ParitySegment.ofAltSegment a).reverse_last.trans haf
  · change (0 + a.length + 1) % 2 = (q.length + 2) % 2
    rw [han]
    omega
  · intro i hi hil
    have hi' : i.val < a.length := hil
    have hpos : 0 < a.length - i.val := by omega
    have hlt : a.length - i.val < a.length := by omega
    have ha := hax.2.2 ⟨a.length - i.val, by omega⟩ hpos hlt
    rw [haf] at ha
    exact ha

end MaximumMatching

end MinimumWeightedExpansion

section WeightedTopExpansion

/-! Weighted paths with a low-tenacity artificial top vertex. The actual
initial segment is kept separate from assigned DDFS layers. Simplicity is
derived by showing that a descending high-core realization never reenters
its first vertex's contracted blossom. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}
namespace DDFS
variable {H : LayeredGraph V} {t : Nat}
namespace BlossomWeightedMatching

private theorem top_hull_mono {core core' : V → Prop}
    (h : ∀ v, core v → core' v) {v : V} :
    BlossomHull M t core v → BlossomHull M t core' v := by
  rintro (hv | ⟨b, hb, hbl⟩)
  · exact Or.inl (h v hv)
  · exact Or.inr ⟨b, h b hb, hbl⟩

/-- Actual edge lengths telescope against an endpoint potential. The potential
need not equal the assigned DDFS layer; this is needed for artificial top edges. -/
theorem weight_add_potential (W : BlossomWeightedMatching M H t) (height : V → Nat)
    (hdrop : ∀ {u v} (he : H.Edge u v),
      (W.segment he).length + height v = height u) (q : Path H) :
    W.weight q + height q.last = height q.first := by
  by_cases hz : q.length = 0
  · have he : q.last = q.first := congrArg q.vertex (Fin.ext (by omega))
    simp [weight, hz, he]
  · let p := q.take (q.length - 1) (by omega)
    have ih := W.weight_add_potential height hdrop p
    have hd := hdrop (q.last_edge (by omega))
    change (W.segment (q.last_edge (by omega))).length + height q.last = height p.last at hd
    change W.weight p + height p.last = height q.first at ih
    rw [weight, dite_eq_right hz]
    change W.weight p + (W.segment (q.last_edge (by omega))).length + height q.last = _
    omega
termination_by q.length
decreasing_by change q.length - 1 < q.length; omega

/-- A high-core realization avoids the entire blossom attached to its initial
vertex: only targets of descending edges contribute interior blossom vertices. -/
theorem realize_avoiding_initial_blossom (W : BlossomWeightedMatching M H t) (q : Path H)
    (hhigh : ∀ v, q.Contains v → levelLT (some t) (tenacity M v)) :
    ∃ s : ParitySegment M, s.first = q.first ∧ s.last = q.last ∧
      s.length = W.weight q ∧ s.phase % 2 = W.phase q.first % 2 ∧
      (s.phase + s.length) % 2 = W.phase q.last % 2 ∧
      (∀ v, s.Contains v → BlossomHull M t q.Contains v) ∧
      (∀ v, s.Contains v → ¬Blossom M t q.first v) := by
  by_cases hz : q.length = 0
  · let s := ParitySegment.trivial M q.first (W.phase q.first)
    have hq : q.first = q.last := congrArg q.vertex (Fin.ext (by omega))
    refine ⟨s, rfl, hq, ?_, rfl, ?_, ?_, ?_⟩
    · simp [s, weight, hz, ParitySegment.trivial]
    · change (W.phase q.first + 0) % 2 = W.phase q.last % 2
      simp only [Nat.add_zero, hq]
    · rintro v ⟨i, hi⟩
      change q.first = v at hi
      exact Or.inl (hi ▸ q.contains_first)
    · rintro v ⟨i, hi⟩ hbl
      change q.first = v at hi
      obtain ⟨k, hk, hkt⟩ := blossom_tenacity_bound t q.first v hbl
      have hh := hhigh v (hi ▸ q.contains_first)
      rw [hk] at hh
      change t < k at hh
      omega
  · let initial := q.take (q.length - 1) (by omega)
    let he : H.Edge initial.last q.last := q.last_edge (by omega)
    let a := W.segment he
    obtain ⟨s, hsf, hsl, hslen, hsphase, hsend, hshull, hsavoid⟩ := W.realize_avoiding_initial_blossom initial
      (fun v hv => hhigh v (q.contains_take (q.length - 1) (by omega) hv))
    have hjoin : s.last = a.first := hsl.trans (W.first he).symm
    have hphase : (s.phase + s.length) % 2 = a.phase % 2 := hsend.trans (W.start_phase he).symm
    have hcores : ∀ v, ¬(initial.Contains v ∧ v = q.last) := by
      rintro v ⟨⟨i, hi⟩, rfl⟩
      change q.vertex ⟨i.val, _⟩ = q.last at hi
      have hidx := congrArg Fin.val (q.injective _ ⟨q.length, by omega⟩ hi)
      have hib := i.isLt
      change i.val < q.length - 1 + 1 at hib
      dsimp only at hidx
      omega
    have hsep := blossom_hulls_disjoint t initial.Contains (fun v => v = q.last)
      (fun v hv => hhigh v (q.contains_take (q.length - 1) (by omega) hv))
      (fun v hv => hv.symm ▸ hhigh q.last q.contains_last) hcores
    have hdis : ∀ (i : Fin (s.length + 1)) (j : Fin (a.length + 1)),
        0 < j.val → s.vertex i ≠ a.vertex j := by
      intro i j hj hij
      have haj : BlossomHull M t (fun v => v = q.last) (a.vertex j) := by
        by_cases hjl : j.val = a.length
        · exact Or.inl ((congrArg a.vertex (Fin.ext hjl)).trans (W.last he))
        · exact Or.inr ⟨q.last, rfl,
            W.interior he j hj (show j.val < a.length by omega)⟩
      exact hsep (s.vertex i) ⟨hshull (s.vertex i) ⟨i, rfl⟩, hij.symm ▸ haj⟩
    let r := s.append a hphase hjoin hdis
    refine ⟨r, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (s.append_first a hphase hjoin hdis).trans hsf
    · exact (s.append_last a hphase hjoin hdis).trans (W.last he)
    · change s.length + a.length = W.weight q
      rw [weight, dite_eq_right hz, ← hslen]
    · exact hsphase
    · have haend := W.end_phase he
      change (a.phase + a.length) % 2 = W.phase q.last % 2 at haend
      change (s.phase + (s.length + a.length)) % 2 = W.phase q.last % 2
      omega
    · intro v hv
      rcases (s.contains_append_iff a hphase hjoin hdis v).1 hv with hs | ha
      · exact top_hull_mono (fun _ hv => q.contains_take (q.length - 1) (by omega) hv) (hshull v hs)
      · obtain ⟨i, hi⟩ := ha
        by_cases hi0 : i.val = 0
        · have heq : a.vertex i = initial.last :=
            (congrArg a.vertex (Fin.ext hi0)).trans (W.first he)
          have hh := q.contains_take (q.length - 1) (by omega) initial.contains_last
          exact Or.inl ((hi.symm.trans heq).symm ▸ hh)
        · by_cases hil : i.val = a.length
          · have heq : a.vertex i = q.last :=
              (congrArg a.vertex (Fin.ext hil)).trans (W.last he)
            exact Or.inl ((hi.symm.trans heq).symm ▸ q.contains_last)
          · exact Or.inr ⟨q.last, q.contains_last,
              hi ▸ W.interior he i (by omega) (show i.val < a.length by omega)⟩
    · intro v hv hbl
      rcases (s.contains_append_iff a hphase hjoin hdis v).1 hv with hs | ha
      · exact hsavoid v hs hbl
      · obtain ⟨i, hi⟩ := ha
        by_cases hi0 : i.val = 0
        · have hvhigh := hhigh initial.last
            (q.contains_take (q.length - 1) (by omega) initial.contains_last)
          have heq : a.vertex i = initial.last :=
            (congrArg a.vertex (Fin.ext hi0)).trans (W.first he)
          obtain ⟨k, hk, hkt⟩ := blossom_tenacity_bound t q.first v hbl
          rw [← heq, hi, hk] at hvhigh
          change t < k at hvhigh
          omega
        · by_cases hil : i.val = a.length
          · have hvhigh := hhigh q.last q.contains_last
            have heq : a.vertex i = q.last :=
              (congrArg a.vertex (Fin.ext hil)).trans (W.last he)
            obtain ⟨k, hk, hkt⟩ := blossom_tenacity_bound t q.first v hbl
            rw [← heq, hi, hk] at hvhigh
            change t < k at hvhigh
            omega
          · have hlastne : q.last ≠ q.first := by
              intro heq
              have hidx := congrArg Fin.val (q.injective ⟨q.length, by omega⟩ ⟨0, by omega⟩ heq)
              dsimp only at hidx
              omega
            exact blossoms_disjoint_same_tenacity t q.last q.first
              (hhigh _ q.contains_last) (hhigh _ q.contains_first) hlastne v
              ⟨hi ▸ W.interior he i (by omega) (by change i.val < a.length; omega), hbl⟩
termination_by q.length
decreasing_by change q.length - 1 < q.length; omega

/-- Prepend the actual descending segment from an artificial low top vertex.
The segment may lie in the first core vertex's blossom, which the rest of the
realization provably avoids. No cross-path freshness premise is required. -/
theorem realize_with_low_start (W : BlossomWeightedMatching M H t) (q : Path H)
    (hhigh : ∀ v, q.Contains v → levelLT (some t) (tenacity M v))
    (a : ParitySegment M) (ha : a.last = q.first)
    (hap : (a.phase + a.length) % 2 = W.phase q.first % 2)
    (hab : ∀ i : Fin (a.length + 1), i.val < a.length →
      Blossom M t q.first (a.vertex i)) :
    ∃ s : ParitySegment M, s.first = a.first ∧ s.last = q.last ∧
      s.length = a.length + W.weight q ∧ s.phase = a.phase ∧
      (s.phase + s.length) % 2 = W.phase q.last % 2 ∧
      (∀ v, s.Contains v → BlossomHull M t q.Contains v) := by
  obtain ⟨r, hrf, hrl, hrn, hrp, hre, hrh, hravoid⟩ :=
    W.realize_avoiding_initial_blossom q hhigh
  have hj : a.last = r.first := ha.trans hrf.symm
  have hp : (a.phase + a.length) % 2 = r.phase % 2 := hap.trans hrp.symm
  have hd : ∀ (i : Fin (a.length + 1)) (j : Fin (r.length + 1)),
      0 < j.val → a.vertex i ≠ r.vertex j := by
    intro i j hjp heq
    by_cases hi : i.val < a.length
    · exact hravoid (r.vertex j) ⟨j, rfl⟩ (heq ▸ hab i hi)
    · have hi' : i = ⟨a.length, by omega⟩ := Fin.ext (by change i.val = a.length; have := i.isLt; omega)
      have he : r.first = r.vertex j := hj.symm.trans ((congrArg a.vertex hi').symm.trans heq)
      have hv := congrArg Fin.val (r.injective ⟨0, by omega⟩ j he)
      dsimp only at hv
      omega
  refine ⟨a.append r hp hj hd, (a.append_first r hp hj hd),
    (a.append_last r hp hj hd).trans hrl, by simp [hrn], rfl, ?_, ?_⟩
  · change (a.phase + (a.length + r.length)) % 2 = _
    omega
  · intro v hv
    rcases (a.contains_append_iff r hp hj hd v).1 hv with hav | hrv
    · obtain ⟨i, hi⟩ := hav
      by_cases hil : i.val < a.length
      · exact Or.inr ⟨q.first, q.contains_first, hi ▸ hab i hil⟩
      · have he : i = ⟨a.length, by omega⟩ := Fin.ext (by change i.val = a.length; have := i.isLt; omega)
        have hh : v = q.first := hi.symm.trans ((congrArg a.vertex he).trans ha)
        exact Or.inl (hh.symm ▸ q.contains_first)
    · exact hrh v hrv

/-- Disjoint high-core paths retain disjointness after both actual low-top
segments are prepended. The two top vertices need not have high tenacity. -/
theorem realize_disjoint_low_starts (W : BlossomWeightedMatching M H t) (p q : Path H)
    (hp : ∀ v, p.Contains v → levelLT (some t) (tenacity M v))
    (hq : ∀ v, q.Contains v → levelLT (some t) (tenacity M v)) (hdis : p.Disjoint q)
    (a b : ParitySegment M) (ha : a.last = p.first) (hb : b.last = q.first)
    (hap : (a.phase + a.length) % 2 = W.phase p.first % 2)
    (hbp : (b.phase + b.length) % 2 = W.phase q.first % 2)
    (hab : ∀ i : Fin (a.length + 1), i.val < a.length → Blossom M t p.first (a.vertex i))
    (hbb : ∀ i : Fin (b.length + 1), i.val < b.length → Blossom M t q.first (b.vertex i)) :
    ∃ s r : ParitySegment M,
      s.first = a.first ∧ s.last = p.last ∧ s.length = a.length + W.weight p ∧
      r.first = b.first ∧ r.last = q.last ∧ r.length = b.length + W.weight q ∧
      s.phase = a.phase ∧ r.phase = b.phase ∧ (∀ i j, s.vertex i ≠ r.vertex j) := by
  obtain ⟨s, hsf, hsl, hsn, hsp, _, hsh⟩ := W.realize_with_low_start p hp a ha hap hab
  obtain ⟨r, hrf, hrl, hrn, hrp, _, hrh⟩ := W.realize_with_low_start q hq b hb hbp hbb
  refine ⟨s, r, hsf, hsl, hsn, hrf, hrl, hrn, hsp, hrp, ?_⟩
  intro i j he
  exact blossom_hulls_disjoint t p.Contains q.Contains hp hq
    (fun v h => hdis v h.1 h.2) (s.vertex i)
    ⟨hsh (s.vertex i) ⟨i, rfl⟩, he.symm ▸ hrh (r.vertex j) ⟨j, rfl⟩⟩


end BlossomWeightedMatching
end DDFS
end MaximumMatching

end WeightedTopExpansion

section ParityBridgeJoin

/-! Relative bridge joining inside a recorded petal, without requiring a
free boundary. Simplicity is derived from the two arms' actual disjointness. -/
namespace MaximumMatching.ParitySegment
variable {V : Type} {G : Graph V} {M : Matching G}

theorem bridge_join_segment (a b : ParitySegment M)
    (hdis : ∀ i j, b.vertex i ≠ a.vertex j)
    (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1) :
    ∃ z : ParitySegment M, z.first = b.last ∧ z.last = a.last ∧
      z.length = b.length + 1 + a.length ∧
      z.phase = b.phase + b.length + 1 ∧
      (∀ w, z.Contains w → a.Contains w ∨ b.Contains w) ∧
      ∃ i : Fin z.length, z.vertex ⟨i.val, by omega⟩ = b.first ∧
        z.vertex ⟨i.val + 1, by omega⟩ = a.first := by
  let e := ofEdge b.first a.first (b.phase + 1) hedge hmatch
  have hp : (b.reverse.phase + b.reverse.length) % 2 = e.phase % 2 := by
    change (b.phase + b.length + 1 + b.length) % 2 = (b.phase + 1) % 2
    omega
  have hj : b.reverse.last = e.first := b.reverse_last
  have hd : ∀ (i : Fin (b.reverse.length + 1)) (j : Fin (e.length + 1)),
      0 < j.val → b.reverse.vertex i ≠ e.vertex j := by
    intro i j hpos he
    have hj1 : j.val = 1 := by have hjb := j.isLt; change j.val < 1 + 1 at hjb; omega
    have he' : b.vertex ⟨b.length - i.val, by have hib := i.isLt; change i.val < b.length + 1 at hib; omega⟩ = a.first := by
      simpa only [e, ofEdge, hj1, Nat.one_ne_zero, ite_false, reverse] using he
    exact hdis _ ⟨0, by omega⟩ he'
  let c := b.reverse.append e hp hj hd
  have hcp : (c.phase + c.length) % 2 = a.phase % 2 := by
    change (b.phase + b.length + 1 + (b.length + 1)) % 2 = a.phase % 2
    omega
  have hcj : c.last = a.first := b.reverse.append_last e hp hj hd
  have hcd : ∀ (i : Fin (c.length + 1)) (j : Fin (a.length + 1)),
      0 < j.val → c.vertex i ≠ a.vertex j := by
    intro i j hpos he
    have hc : c.Contains (a.vertex j) := ⟨i, he⟩
    rcases (b.reverse.contains_append_iff e hp hj hd (a.vertex j)).mp hc with hb | he
    · obtain ⟨k, hk⟩ := (b.contains_reverse_iff _).mp hb
      exact hdis k j hk
    · obtain ⟨k, hk⟩ := he
      by_cases hk0 : k.val = 0
      · have hh : b.first = a.vertex j := by simpa [e, ofEdge, hk0] using hk
        exact hdis ⟨0, by omega⟩ j hh
      · have hh : a.first = a.vertex j := by simpa [e, ofEdge, hk0] using hk
        have hh' := congrArg Fin.val (a.injective ⟨0, by omega⟩ j hh)
        change 0 = j.val at hh'
        omega
  let d := c.append a hcp hcj hcd
  have hdf : d.first = b.last :=
    (c.append_first a hcp hcj hcd).trans ((b.reverse.append_first e hp hj hd).trans b.reverse_first)
  refine ⟨d, hdf, c.append_last a hcp hcj hcd, rfl, rfl, ?_, ?_⟩
  · intro w hw
    rcases (c.contains_append_iff a hcp hcj hcd w).1 hw with hcw | haw
    · rcases (b.reverse.contains_append_iff e hp hj hd w).1 hcw with hbw | hew
      · exact Or.inr ((b.contains_reverse_iff w).1 hbw)
      · obtain ⟨i, hi⟩ := hew
        by_cases hz : i.val = 0
        · have hbw : b.first = w := by simpa only [e, ofEdge, hz, ite_true] using hi
          exact Or.inr ⟨⟨0, by omega⟩, hbw⟩
        · have haw : a.first = w := by simpa only [e, ofEdge, hz, ite_false] using hi
          exact Or.inl ⟨⟨0, by omega⟩, haw⟩
    · exact Or.inl haw
  · refine ⟨⟨b.length, by change b.length < b.length + 1 + a.length; omega⟩, ?_, ?_⟩
    · change d.vertex ⟨b.length, _⟩ = b.first
      simp only [d, append, c, reverse, e, ofEdge, show b.length ≤ b.length + 1 by omega,
        dite_true, Nat.le_refl, Nat.sub_self, first]
    · change d.vertex ⟨b.length + 1, _⟩ = a.first
      simp only [d, append, c, reverse, e, ofEdge, Nat.le_refl, dite_true,
        show ¬b.length + 1 ≤ b.length by omega, dite_false,
        Nat.add_sub_cancel_left, Nat.one_ne_zero, ite_false]

/-- When the reverse arm starts unmatched at its boundary, the construction
is an ordinary relative alternating segment even if that boundary is matched. -/
theorem bridge_join_relative (a b : ParitySegment M)
    (hdis : ∀ i j, b.vertex i ≠ a.vertex j)
    (hphase : a.phase % 2 = b.phase % 2)
    (hedge : G.Adj b.first a.first)
    (hmatch : (M.mate b.first = some a.first) ↔ (b.phase + 1) % 2 = 1)
    (hboundary : (b.phase + b.length) % 2 = 1) :
    ∃ z : AltSegment M, z.first = b.last ∧ z.last = a.last ∧
      z.length = b.length + 1 + a.length ∧
      (∀ w, z.Contains w → a.Contains w ∨ b.Contains w) ∧
      ∃ i : Fin z.length, z.vertex ⟨i.val, by omega⟩ = b.first ∧
        z.vertex ⟨i.val + 1, by omega⟩ = a.first := by
  obtain ⟨z, hf, hl, hn, hp, hc, he⟩ := a.bridge_join_segment b hdis hphase hedge hmatch
  have hz : z.phase % 2 = 0 := by rw [hp]; omega
  exact ⟨z.toAltSegment hz, hf, hl, hn, hc, he⟩

end MaximumMatching.ParitySegment

end ParityBridgeJoin

section GeneralWeightedTop

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

end GeneralWeightedTop
