import MaximumMatching.Honesty

namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The replacement path avoids the segment traversed in reverse. -/
def ReverseDisjoint (q p : AltPath M) (k j : Nat) : Prop :=
  ∀ (a : Fin (q.length + 1)) (b : Fin (p.length + 1)),
    k ≤ b.val → b.val < j → q.vertex a ≠ p.vertex b

/-- Join an odd-length path to an even-indexed vertex, then follow a segment backward. -/
def spliceReverse (q p : AltPath M) (k j : Nat) (hkj : k ≤ j) (hj : j ≤ p.length)
    (hjoin : q.last = p.vertex ⟨j, by omega⟩)
    (hqo : q.length % 2 = 1) (hje : j % 2 = 0)
    (hdisj : q.ReverseDisjoint p k j) : AltPath M where
  length := q.length + (j - k)
  vertex := fun a => if h : a.val ≤ q.length then q.vertex ⟨a.val, by omega⟩
    else p.vertex ⟨j - (a.val - q.length), by omega⟩
  injective := by
    intro a b he
    split at he <;> split at he
    · have hh := q.injective _ _ he
      apply Fin.ext
      exact congrArg (fun x : Fin (q.length + 1) => x.val) hh
    · exact False.elim (hdisj _ _ (by change k ≤ j - (b.val - q.length); omega)
        (by change j - (b.val - q.length) < j; omega) he)
    · exact False.elim (hdisj _ _ (by change k ≤ j - (a.val - q.length); omega)
        (by change j - (a.val - q.length) < j; omega) he.symm)
    · have hh := p.injective _ _ he
      have heq : j - (a.val - q.length) = j - (b.val - q.length) :=
        congrArg (fun x : Fin (p.length + 1) => x.val) hh
      apply Fin.ext
      omega
  adjacent := by
    intro a
    by_cases ha : a.val < q.length
    · simpa only [dite_eq_left (show a.val ≤ q.length by omega),
        dite_eq_left (show a.val + 1 ≤ q.length by omega)] using q.adjacent ⟨a.val, ha⟩
    · by_cases heq : a.val = q.length
      · simp only [heq, Nat.le_refl, dite_true,
          show ¬q.length + 1 ≤ q.length by omega, dite_false]
        change G.Adj q.last _
        rw [hjoin]
        have he : j - (q.length + 1 - q.length) = j - 1 := by omega
        have he' : j - 1 + 1 = j := by omega
        simpa only [he, he'] using G.symm (p.adjacent ⟨j - 1, by omega⟩)
      · simp only [dite_eq_right (show ¬a.val ≤ q.length by omega),
          dite_eq_right (show ¬a.val + 1 ≤ q.length by omega)]
        have he : j - (a.val + 1 - q.length) + 1 = j - (a.val - q.length) := by omega
        simpa only [he] using G.symm (p.adjacent ⟨j - (a.val + 1 - q.length), by omega⟩)
  start_free := by simpa using q.start_free
  alternating := by
    intro a
    by_cases ha : a.val < q.length
    · simpa only [dite_eq_left (show a.val ≤ q.length by omega),
        dite_eq_left (show a.val + 1 ≤ q.length by omega)] using q.alternating ⟨a.val, ha⟩
    · by_cases heq : a.val = q.length
      · simp only [heq, Nat.le_refl, dite_true,
          show ¬q.length + 1 ≤ q.length by omega, dite_false]
        change (M.mate q.last = some _) ↔ q.length % 2 = 1
        rw [hjoin]
        have hm := p.mate_previous j hj (by omega) hje
        have he : j - (q.length + 1 - q.length) = j - 1 := by omega
        constructor
        · intro _; exact hqo
        · intro _; simpa only [he] using hm
      · simp only [dite_eq_right (show ¬a.val ≤ q.length by omega),
          dite_eq_right (show ¬a.val + 1 ≤ q.length by omega)]
        have he : j - (a.val + 1 - q.length) + 1 = j - (a.val - q.length) := by omega
        have hpar : (j - (a.val + 1 - q.length)) % 2 = a.val % 2 := by omega
        have hh := p.alternating ⟨j - (a.val + 1 - q.length), by omega⟩
        rw [hpar] at hh
        constructor
        · intro hm
          apply hh.1
          simpa only [he] using M.symm hm
        · intro hp
          simpa only [he] using M.symm (hh.2 hp)

@[simp] theorem spliceReverse_length (q p : AltPath M) (k j : Nat)
    (hkj : k ≤ j) (hj : j ≤ p.length) (hjoin : q.last = p.vertex ⟨j, by omega⟩)
    (hqo : q.length % 2 = 1) (hje : j % 2 = 0) (hdisj : q.ReverseDisjoint p k j) :
    (q.spliceReverse p k j hkj hj hjoin hqo hje hdisj).length = q.length + (j - k) := rfl

@[simp] theorem spliceReverse_last (q p : AltPath M) (k j : Nat)
    (hkj : k ≤ j) (hj : j ≤ p.length) (hjoin : q.last = p.vertex ⟨j, by omega⟩)
    (hqo : q.length % 2 = 1) (hje : j % 2 = 0) (hdisj : q.ReverseDisjoint p k j) :
    (q.spliceReverse p k j hkj hj hjoin hqo hje hdisj).last = p.vertex ⟨k, by omega⟩ := by
  simp only [last, spliceReverse]
  split
  · have hlen : k = j := by omega
    have hnew : q.length + (j - k) = q.length := by omega
    simp only [hnew]
    exact hlen ▸ hjoin
  · have he : j - (q.length + (j - k) - q.length) = k := by omega
    congr 1
    exact Fin.ext he

/-- A first intersection of `q` with the suffix of `p` beginning at `cut`. -/
structure FirstHit (q p : AltPath M) (cut : Nat) where
  qi : Fin (q.length + 1)
  pi : Fin (p.length + 1)
  in_suffix : cut ≤ pi.val
  hit : q.vertex qi = p.vertex pi
  first : ∀ (a : Fin (q.length + 1)) (b : Fin (p.length + 1)),
    a.val < qi.val → cut ≤ b.val → q.vertex a ≠ p.vertex b

private theorem least_hit (P : Nat → Prop) (n : Nat) (hn : P n) :
    ∃ m, P m ∧ ∀ l, l < m → ¬P l := by
  classical
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hs : ∃ m, m < n ∧ P m
    · obtain ⟨m, hm, hp⟩ := hs
      exact ih m hm hp
    · refine ⟨n, hn, ?_⟩
      intro m hm hp
      exact hs ⟨m, hm, hp⟩

theorem firstHit_exists (q p : AltPath M) (cut : Nat)
    (h : ∃ (i : Fin (q.length + 1)) (j : Fin (p.length + 1)),
      cut ≤ j.val ∧ q.vertex i = p.vertex j) : Nonempty (FirstHit q p cut) := by
  classical
  let P (i : Nat) := ∃ (hi : i < q.length + 1) (j : Fin (p.length + 1)),
    cut ≤ j.val ∧ q.vertex ⟨i, hi⟩ = p.vertex j
  obtain ⟨i, j, hc, hh⟩ := h
  have hi : P i.val := ⟨i.isLt, j, hc, hh⟩
  obtain ⟨m, ⟨hm, j, hc, hh⟩, hmin⟩ := least_hit P i.val hi
  refine ⟨⟨⟨m, hm⟩, j, hc, hh, ?_⟩⟩
  intro a b ha hb he
  exact hmin a.val ha ⟨a.isLt, b, hb, he⟩

/-- In an even path, an odd-indexed suffix is a union of complete matched pairs. -/
theorem even_suffix_matched_closed (p : AltPath M) (he : p.length % 2 = 0)
    (cut : Nat) (hc : cut % 2 = 1) (j : Fin (p.length + 1)) (hj : cut ≤ j.val) :
    ∃ j' : Fin (p.length + 1), cut ≤ j'.val ∧ M.mate (p.vertex j) = some (p.vertex j') := by
  by_cases hje : j.val % 2 = 0
  · refine ⟨⟨j.val - 1, by omega⟩, ?_, ?_⟩
    · change cut ≤ j.val - 1
      omega
    · exact p.mate_previous j.val (by omega) (by omega) hje
  · refine ⟨⟨j.val + 1, by omega⟩, ?_, ?_⟩
    · change cut ≤ j.val + 1
      omega
    · exact p.mate_next j.val (by omega) (by omega)

/-- The first hit on a suffix consisting of matched pairs occurs at odd parity. -/
theorem FirstHit.odd {q p : AltPath M} {cut : Nat} (h : FirstHit q p cut)
    (he : p.length % 2 = 0) (hc : cut % 2 = 1) : h.qi.val % 2 = 1 := by
  obtain ⟨j, hj, hm⟩ := p.even_suffix_matched_closed he cut hc h.pi h.in_suffix
  have hq : M.mate (q.vertex h.qi) = some (p.vertex j) := by rw [h.hit]; exact hm
  by_cases hz : h.qi.val = 0
  · have hi : h.qi = ⟨0, by omega⟩ := Fin.ext hz
    rw [hi] at hq
    have hf := q.start_free
    unfold Matching.Free at hf
    rw [hf] at hq
    contradiction
  · by_cases heven : h.qi.val % 2 = 0
    · have hp := q.mate_previous h.qi.val (by omega) (by omega) heven
      have hv := M.mate_unique hp hq
      exact False.elim (h.first ⟨h.qi.val - 1, by omega⟩ j (by change h.qi.val - 1 < h.qi.val; omega) hj hv)
    · omega

/-- At a first hit, the prefix avoids every vertex strictly after the hit in `p`. -/
theorem FirstHit.forward_disjoint {q p : AltPath M} {cut : Nat} (h : FirstHit q p cut) :
    (q.take h.qi.val (by omega)).SuffixDisjoint p h.pi.val := by
  intro a b hb he
  change q.vertex ⟨a.val, _⟩ = p.vertex b at he
  have habound : a.val ≤ h.qi.val := by
    have ha := a.isLt
    change a.val < h.qi.val + 1 at ha
    omega
  by_cases ha : a.val < h.qi.val
  · exact h.first ⟨a.val, by omega⟩ b ha (by have := h.in_suffix; omega) he
  · have heq : a.val = h.qi.val := by omega
    have ha' : (⟨a.val, by omega⟩ : Fin (q.length + 1)) = h.qi := Fin.ext heq
    rw [ha', h.hit] at he
    have hi := p.injective _ _ he
    have hi' : h.pi.val = b.val := congrArg Fin.val hi
    omega

/-- At a first hit, the prefix avoids every earlier vertex in the suffix of `p`. -/
theorem FirstHit.reverse_disjoint {q p : AltPath M} {cut : Nat} (h : FirstHit q p cut)
    (k : Nat) (hk : cut ≤ k) :
    (q.take h.qi.val (by omega)).ReverseDisjoint p k h.pi.val := by
  intro a b hb hb' he
  change q.vertex ⟨a.val, _⟩ = p.vertex b at he
  have habound : a.val ≤ h.qi.val := by
    have ha := a.isLt
    change a.val < h.qi.val + 1 at ha
    omega
  by_cases ha : a.val < h.qi.val
  · exact h.first ⟨a.val, by omega⟩ b ha (by omega) he
  · have heq : a.val = h.qi.val := by omega
    have ha' : (⟨a.val, by omega⟩ : Fin (q.length + 1)) = h.qi := Fin.ext heq
    rw [ha', h.hit] at he
    have hi := p.injective _ _ he
    have hi' : h.pi.val = b.val := congrArg Fin.val hi
    omega

end AltPath
end MaximumMatching
