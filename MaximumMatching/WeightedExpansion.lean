import MaximumMatching.BlossomExpansion
import MaximumMatching.DDFSPaths

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
