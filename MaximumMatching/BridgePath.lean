import MaximumMatching.DDFSAltPath
import MaximumMatching.PathLemmas

namespace MaximumMatching
namespace DDFS
variable {V : Type} {G : Graph V} {M : Matching G} {H : LayeredGraph V}

/-- Unit layer drops identify the layer of each path vertex. -/
theorem Path.level_add_index (q : Path H)
    (hstep : ∀ {u v}, H.Edge u v → H.level u = H.level v + 1)
    (i : Fin (q.length + 1)) :
    H.level (q.vertex i) + i.val = H.level q.first := by
  have aux : ∀ k (hk : k < q.length + 1),
      H.level (q.vertex ⟨k, hk⟩) + k = H.level q.first := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hs := hstep (q.adjacent ⟨k, by omega⟩)
      dsimp only at hprev hs
      omega
  exact aux i.val i.isLt

/-- Extend an alternating path down a disjoint layered suffix. The layer parity
is reversed after crossing the horizontal bridge. -/
def appendDown (q : Path H) (p : AltPath M)
    (hedge : ∀ {u v}, H.Edge u v → G.Adj u v)
    (hstep : ∀ {u v}, H.Edge u v → H.level u = H.level v + 1)
    (hmatch : ∀ {u v}, H.Edge u v → ((M.mate v = some u) ↔ H.level v % 2 = 1))
    (hjoin : p.last = q.first)
    (hshift : p.length % 2 = (H.level q.first + 1) % 2)
    (hdisj : ∀ (i : Fin (p.length + 1)) (j : Fin (q.length + 1)),
      0 < j.val → p.vertex i ≠ q.vertex j) : AltPath M where
  length := p.length + q.length
  vertex := fun i => if hi : i.val ≤ p.length then p.vertex ⟨i.val, by omega⟩
    else q.vertex ⟨i.val - p.length, by omega⟩
  injective := by
    intro i j he
    split at he <;> split at he
    · have hi := p.injective _ _ he
      apply Fin.ext
      exact congrArg (fun x : Fin (p.length + 1) => x.val) hi
    · exact False.elim (hdisj _ _ (by change 0 < j.val - p.length; omega) he)
    · exact False.elim (hdisj _ _ (by change 0 < i.val - p.length; omega) he.symm)
    · have hi := q.injective _ _ he
      have hi' := congrArg Fin.val hi
      dsimp only at hi'
      apply Fin.ext
      omega
  adjacent := by
    intro i
    by_cases hi : i.val < p.length
    · simpa only [dite_eq_left (show i.val ≤ p.length by omega),
        dite_eq_left (show i.val + 1 ≤ p.length by omega)] using p.adjacent ⟨i.val, hi⟩
    · by_cases he : i.val = p.length
      · simp only [he, Nat.le_refl, dite_true,
          show ¬ p.length + 1 ≤ p.length by omega, dite_false]
        change G.Adj p.last _
        rw [hjoin]
        simpa only [Path.first, Nat.zero_add, show p.length + 1 - p.length = 1 by omega] using
          hedge (q.adjacent ⟨0, by omega⟩)
      · simp only [dite_eq_right (show ¬ i.val ≤ p.length by omega),
          dite_eq_right (show ¬ i.val + 1 ≤ p.length by omega)]
        simpa only [show i.val + 1 - p.length = (i.val - p.length) + 1 by omega] using
          hedge (q.adjacent ⟨i.val - p.length, by omega⟩)
  start_free := by simpa using p.start_free
  alternating := by
    intro i
    by_cases hi : i.val < p.length
    · simpa only [dite_eq_left (show i.val ≤ p.length by omega),
        dite_eq_left (show i.val + 1 ≤ p.length by omega)] using p.alternating ⟨i.val, hi⟩
    · have hbound : i.val - p.length < q.length := by omega
      have hs := hmatch (q.adjacent ⟨i.val - p.length, hbound⟩)
      have hl := q.level_add_index hstep ⟨i.val - p.length + 1, by omega⟩
      dsimp only at hl hs
      have hpar : H.level (q.vertex ⟨i.val - p.length + 1, by omega⟩) % 2 = i.val % 2 := by
        omega
      have hmat : (M.mate (q.vertex ⟨i.val - p.length, by omega⟩) =
          some (q.vertex ⟨i.val - p.length + 1, by omega⟩)) ↔ i.val % 2 = 1 := by
        constructor
        · intro hm
          rw [← hpar]
          exact hs.1 (M.symm hm)
        · intro hp
          exact M.symm (hs.2 (hpar.trans hp))
      by_cases he : i.val = p.length
      · simp only [he, Nat.le_refl, dite_true,
          show ¬ p.length + 1 ≤ p.length by omega, dite_false]
        change (M.mate p.last = some _) ↔ p.length % 2 = 1
        rw [hjoin]
        simpa only [Path.first, he, Nat.sub_self, Nat.zero_add, show p.length + 1 - p.length = 1 by omega] using hmat
      · simp only [dite_eq_right (show ¬ i.val ≤ p.length by omega),
          dite_eq_right (show ¬ i.val + 1 ≤ p.length by omega)]
        simpa only [show i.val + 1 - p.length = (i.val - p.length) + 1 by omega] using hmat

@[simp] theorem appendDown_length (q : Path H) (p : AltPath M)
    (hedge) (hstep) (hmatch) (hjoin) (hshift) (hdisj) :
    (appendDown q p hedge hstep hmatch hjoin hshift hdisj).length = p.length + q.length := rfl

@[simp] theorem appendDown_first (q : Path H) (p : AltPath M)
    (hedge) (hstep) (hmatch) (hjoin) (hshift) (hdisj) :
    (appendDown q p hedge hstep hmatch hjoin hshift hdisj).first = p.first := by
  simp only [AltPath.first, appendDown, Nat.zero_le, dite_true]

@[simp] theorem appendDown_last (q : Path H) (p : AltPath M)
    (hedge) (hstep) (hmatch) (hjoin) (hshift) (hdisj) :
    (appendDown q p hedge hstep hmatch hjoin hshift hdisj).last = q.last := by
  simp only [AltPath.last, appendDown]
  split
  next h =>
    have hzero : q.length = 0 := by omega
    have hlen : p.length + q.length = p.length := by omega
    simp only [hlen]
    change p.last = q.last
    rw [hjoin]
    exact congrArg q.vertex (Fin.ext (by exact hzero.symm))
  next h => congr 1; apply Fin.ext; change p.length + q.length - p.length = q.length; omega

/-- The bridge detour used by Claim 4 on p.25: lift the path from the
opposite bridge endpoint to the bottleneck, cross the bridge, and descend to
`w`. Layer separation and the DDFS certificate prove simplicity. -/
theorem bridge_detour (compat : LayeredMatching M H)
    (r g b w : V) (α : Nat)
    (hr : H.level r = α) (hg : H.level g = α)
    (hbridge : G.Adj g r) (hbridge_match : (M.mate g = some r) ↔ α % 2 = 1)
    (a q : Path H) (ha : a.first = r) (haw : a.last = w)
    (hq : q.first = g) (hqb : q.last = b) (hdisj : a.Disjoint q)
    (hw : H.level b < H.level w)
    (p : AltPath M) (hp : p.last = b)
    (hlevels : ∀ i, H.level (p.vertex i) = i.val) :
    ∃ z : AltPath M, z.first = p.first ∧ z.last = w ∧
      z.length = 2 * α + 1 - H.level w := by
  obtain ⟨s, hsfirst, hslast, hslen, _, hsmem⟩ := lift_path compat q p
    (hp.trans hqb.symm) hlevels
  have hplen : H.level b = p.length := by
    have hh : H.level p.last = p.length := hlevels ⟨p.length, by omega⟩
    simpa only [hp] using hh
  have hsavoid : ∀ (i : Fin (s.length + 1)) (j : Fin (a.length + 1)),
      s.vertex i ≠ a.vertex j := by
    intro i j he
    have hm := (hsmem (s.vertex i)).1 ⟨i, rfl⟩
    rcases hm with ⟨k, hk⟩ | hqmem
    · have hlow := hlevels k
      have hhigh := a.last_level_le (show a.Contains (a.vertex j) from ⟨j, rfl⟩)
      rw [haw] at hhigh
      rw [hk, he] at hlow
      omega
    · exact hdisj (a.vertex j) ⟨j, rfl⟩ (he ▸ hqmem)
  have hsr : ∀ i, s.vertex i ≠ r := by
    intro i
    simpa only [← ha, Path.first] using hsavoid i ⟨0, by omega⟩
  have hsg : s.last = g := hslast.trans hq
  have hsα : s.length = α := hslen.trans (by rw [hq, hg])
  have hedge : G.Adj s.last r := hsg ▸ hbridge
  have hpar : (M.mate s.last = some r) ↔ s.length % 2 = 1 := by
    simpa only [hsg, hsα] using hbridge_match
  let t := s.append r hsr hedge hpar
  have htlast : t.last = a.first := (s.append_last r hsr hedge hpar).trans ha.symm
  have htshift : t.length % 2 = (H.level a.first + 1) % 2 := by
    change (s.length + 1) % 2 = _
    rw [hsα, ha, hr]
  have htavoid : ∀ (i : Fin (t.length + 1)) (j : Fin (a.length + 1)),
      0 < j.val → t.vertex i ≠ a.vertex j := by
    intro i j hj he
    change (if hi : i.val ≤ s.length then s.vertex ⟨i.val, by omega⟩ else r) = a.vertex j at he
    split at he
    · exact hsavoid _ j he
    · have ha0 : a.vertex ⟨0, by omega⟩ = r := ha
      have hh := a.injective _ j (ha0.trans he)
      have hv : 0 = j.val := congrArg (fun x : Fin (a.length + 1) => x.val) hh
      omega
  let z := appendDown a t compat.adjacent compat.consecutive compat.alternating
    htlast htshift htavoid
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [appendDown_first]
    change (if h : 0 ≤ s.length then s.vertex ⟨0, by omega⟩ else r) = p.first
    simpa only [AltPath.first, Nat.zero_le, dite_true] using hsfirst
  · exact (appendDown_last a t compat.adjacent compat.consecutive compat.alternating
      htlast htshift htavoid).trans haw
  · have hal := a.level_add_index compat.consecutive ⟨a.length, by omega⟩
    change H.level a.last + a.length = H.level a.first at hal
    rw [haw, ha, hr] at hal
    change s.length + 1 + a.length = _
    omega

end DDFS
end MaximumMatching
