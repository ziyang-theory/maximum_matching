import MaximumMatching.Segment

/-! Simple splices into relative alternating paths. These generalize the
free-rooted splice operations: only the retained prefix needs a free root. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The replacement path does not meet the strict suffix being retained. -/
def SegmentSuffixDisjoint (q : AltPath M) (p : AltSegment M) (k : Nat) : Prop :=
  ∀ (i : Fin (q.length + 1)) (j : Fin (p.length + 1)),
    k < j.val → q.vertex i ≠ p.vertex j

/-- Replace a prefix by a same-parity path with the same endpoint, provided its
vertices avoid the retained suffix. The fresh start may be a different free vertex. -/
def spliceSegment (q : AltPath M) (p : AltSegment M) (k : Nat) (hk : k ≤ p.length)
    (hjoin : q.last = p.vertex ⟨k, by omega⟩)
    (hpar : q.length % 2 = k % 2) (hdisj : q.SegmentSuffixDisjoint p k) : AltPath M where
  length := q.length + (p.length - k)
  vertex := fun i => if h : i.val ≤ q.length then q.vertex ⟨i.val, by omega⟩
    else p.vertex ⟨i.val - q.length + k, by omega⟩
  injective := by
    intro i j he
    split at he <;> split at he
    · have hi := q.injective _ _ he
      apply Fin.ext
      exact congrArg (fun x : Fin (q.length + 1) => x.val) hi
    · exact False.elim (hdisj _ _ (by change k < j.val - q.length + k; omega) he)
    · exact False.elim (hdisj _ _ (by change k < i.val - q.length + k; omega) he.symm)
    · have hi := p.injective _ _ he
      have heq : i.val - q.length + k = j.val - q.length + k :=
        congrArg (fun x : Fin (p.length + 1) => x.val) hi
      apply Fin.ext
      omega
  adjacent := by
    intro i
    by_cases hi : i.val < q.length
    · simpa only [dite_eq_left (show i.val ≤ q.length by omega),
        dite_eq_left (show i.val + 1 ≤ q.length by omega)] using q.adjacent ⟨i.val, hi⟩
    · by_cases heq : i.val = q.length
      · simp only [heq, Nat.le_refl, dite_true,
          show ¬q.length + 1 ≤ q.length by omega, dite_false]
        change G.Adj q.last _
        rw [hjoin]
        have he : q.length + 1 - q.length + k = k + 1 := by omega
        simpa only [he] using p.adjacent ⟨k, by omega⟩
      · simp only [dite_eq_right (show ¬i.val ≤ q.length by omega),
          dite_eq_right (show ¬i.val + 1 ≤ q.length by omega)]
        have he : i.val + 1 - q.length + k = (i.val - q.length + k) + 1 := by omega
        simpa only [he] using p.adjacent ⟨i.val - q.length + k, by omega⟩
  start_free := by simpa using q.start_free
  alternating := by
    intro i
    by_cases hi : i.val < q.length
    · simpa only [dite_eq_left (show i.val ≤ q.length by omega),
        dite_eq_left (show i.val + 1 ≤ q.length by omega)] using q.alternating ⟨i.val, hi⟩
    · by_cases heq : i.val = q.length
      · simp only [heq, Nat.le_refl, dite_true,
          show ¬q.length + 1 ≤ q.length by omega, dite_false]
        change (M.mate q.last = some _) ↔ q.length % 2 = 1
        rw [hjoin, hpar]
        have he : q.length + 1 - q.length + k = k + 1 := by omega
        simpa only [he] using p.alternating ⟨k, by omega⟩
      · simp only [dite_eq_right (show ¬i.val ≤ q.length by omega),
          dite_eq_right (show ¬i.val + 1 ≤ q.length by omega)]
        have he : i.val + 1 - q.length + k = (i.val - q.length + k) + 1 := by omega
        have hp : (i.val - q.length + k) % 2 = i.val % 2 := by omega
        simpa only [he, hp] using p.alternating ⟨i.val - q.length + k, by omega⟩

@[simp] theorem spliceSegment_length (q : AltPath M) (p : AltSegment M) (k : Nat) (hk : k ≤ p.length)
    (hjoin : q.last = p.vertex ⟨k, by omega⟩)
    (hpar : q.length % 2 = k % 2) (hdisj : q.SegmentSuffixDisjoint p k) :
    (q.spliceSegment p k hk hjoin hpar hdisj).length = q.length + (p.length - k) := rfl

@[simp] theorem spliceSegment_last (q : AltPath M) (p : AltSegment M) (k : Nat) (hk : k ≤ p.length)
    (hjoin : q.last = p.vertex ⟨k, by omega⟩)
    (hpar : q.length % 2 = k % 2) (hdisj : q.SegmentSuffixDisjoint p k) :
    (q.spliceSegment p k hk hjoin hpar hdisj).last = p.last := by
  simp only [last, spliceSegment]
  split
  · rename_i h
    have hlen : k = p.length := by omega
    have hnew : q.length + (p.length - k) = q.length := by omega
    simp only [hnew]
    simpa only [last, AltSegment.last, hlen] using hjoin
  · have he : q.length + (p.length - k) - q.length + k = p.length := by omega
    congr 1
    exact Fin.ext he

theorem spliceSegment_parity (q : AltPath M) (p : AltSegment M) (k : Nat) (hk : k ≤ p.length)
    (hjoin : q.last = p.vertex ⟨k, by omega⟩)
    (hpar : q.length % 2 = k % 2) (hdisj : q.SegmentSuffixDisjoint p k) :
    (q.spliceSegment p k hk hjoin hpar hdisj).length % 2 = p.length % 2 := by
  simp only [spliceSegment_length]
  omega

/-- The replacement path avoids the segment traversed in reverse. -/
def SegmentReverseDisjoint (q : AltPath M) (p : AltSegment M) (k j : Nat) : Prop :=
  ∀ (a : Fin (q.length + 1)) (b : Fin (p.length + 1)),
    k ≤ b.val → b.val < j → q.vertex a ≠ p.vertex b

/-- Join an odd-length path to an even-indexed vertex, then follow a segment backward. -/
def spliceReverseSegment (q : AltPath M) (p : AltSegment M) (k j : Nat) (hkj : k ≤ j) (hj : j ≤ p.length)
    (hjoin : q.last = p.vertex ⟨j, by omega⟩)
    (hqo : q.length % 2 = 1) (hje : j % 2 = 0)
    (hdisj : q.SegmentReverseDisjoint p k j) : AltPath M where
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
        have hm : M.mate (p.vertex ⟨j, by omega⟩) = some (p.vertex ⟨j - 1, by omega⟩) := by
          have hh := (p.alternating ⟨j - 1, by omega⟩).2 (by change (j - 1) % 2 = 1; omega)
          have hh' := M.symm hh
          simpa only [show j - 1 + 1 = j by omega] using hh'
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

@[simp] theorem spliceReverseSegment_length (q : AltPath M) (p : AltSegment M) (k j : Nat)
    (hkj : k ≤ j) (hj : j ≤ p.length) (hjoin : q.last = p.vertex ⟨j, by omega⟩)
    (hqo : q.length % 2 = 1) (hje : j % 2 = 0) (hdisj : q.SegmentReverseDisjoint p k j) :
    (q.spliceReverseSegment p k j hkj hj hjoin hqo hje hdisj).length = q.length + (j - k) := rfl

@[simp] theorem spliceReverseSegment_last (q : AltPath M) (p : AltSegment M) (k j : Nat)
    (hkj : k ≤ j) (hj : j ≤ p.length) (hjoin : q.last = p.vertex ⟨j, by omega⟩)
    (hqo : q.length % 2 = 1) (hje : j % 2 = 0) (hdisj : q.SegmentReverseDisjoint p k j) :
    (q.spliceReverseSegment p k j hkj hj hjoin hqo hje hdisj).last = p.vertex ⟨k, by omega⟩ := by
  simp only [last, spliceReverseSegment]
  split
  · have hlen : k = j := by omega
    have hnew : q.length + (j - k) = q.length := by omega
    simp only [hnew]
    exact hlen ▸ hjoin
  · have he : j - (q.length + (j - k) - q.length) = k := by omega
    congr 1
    exact Fin.ext he


end MaximumMatching.AltPath
