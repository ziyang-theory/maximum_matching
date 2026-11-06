import MaximumMatching.DDFSColoredLinkage

/-! Executable recovery from recorded DDFS parent maps. The recursion follows
exactly those parents; proofs of spanning and strict layer descent certify
termination but do not choose paths at runtime. -/
namespace MaximumMatching.DDFS
variable {V : Type} {H : LayeredGraph V}

namespace RootedTree
variable {r : V} {S : V → Prop}

theorem level_le_root (T : RootedTree H r S) (v : V) (hv : S v) :
    H.level v ≤ H.level r := by
  have hr := T.spanning v hv
  induction hr with
  | root => exact Nat.le_refl _
  | @step u v _ hp ih =>
    exact Nat.le_trans (Nat.le_of_lt (H.decreases (T.edge u v hp).2.2))
      (ih (T.edge u v hp).1)

theorem parent_none_eq_root (T : RootedTree H r S) (v : V) (hv : S v)
    (hp : T.parent v = none) : v = r := by
  cases T.spanning v hv with
  | root => rfl
  | step _ he => rw [hp] at he; contradiction

variable [DecidableEq V]

/-- Recover the unique stored-parent path to a tree vertex. This executable
function neither searches the original graph nor extracts a witness by choice. -/
def recover (T : RootedTree H r S) (v : V) (hv : S v) :
    { p : Path H // p.first = r ∧ p.last = v ∧
      (∀ w, p.Contains w → S w) ∧
      ∀ j : Fin p.length, T.parent (p.vertex ⟨j.val + 1, by omega⟩) =
        some (p.vertex ⟨j.val, by omega⟩) } :=
  if hroot : v = r then
    ⟨Path.trivial H r, rfl, hroot.symm,
      (by rintro w ⟨j, hj⟩; change r = w at hj; rw [← hj, ← hroot]; exact hv),
      (fun j => Fin.elim0 j)⟩
  else
    match hp : T.parent v with
    | none => False.elim (hroot (T.parent_none_eq_root v hv hp))
    | some u =>
      let q := T.recover u (T.edge u v hp).1
      have he : H.Edge q.val.last v := q.property.2.1.symm ▸ (T.edge u v hp).2.2
      ⟨q.val.snoc v he, (q.val.snoc_first v he).trans q.property.1,
        q.val.snoc_last v he, (by
          intro w hw
          rcases (q.val.snoc_contains_iff v he w).1 hw with hw | hw
          · exact q.property.2.2.1 w hw
          · exact hw.symm ▸ hv), (by
          intro j
          by_cases hj : j.val < q.val.length
          · simpa only [Path.snoc, dite_eq_left (show j.val ≤ q.val.length by omega),
              dite_eq_left (show j.val + 1 ≤ q.val.length by omega)] using q.property.2.2.2 ⟨j.val, hj⟩
          · have hje : j.val = q.val.length := by
              have hjbound := j.isLt
              change j.val < q.val.length + 1 at hjbound
              omega
            simp only [Path.snoc, hje, Nat.le_refl, dite_true,
              show ¬q.val.length + 1 ≤ q.val.length by omega, dite_false]
            change T.parent v = some q.val.last
            rw [q.property.2.1]
            exact hp)⟩
termination_by H.level r - H.level v
decreasing_by
  have hparent := (T.edge u v hp).1
  have hle := T.level_le_root u hparent
  have hlt := H.decreases (T.edge u v hp).2.2
  omega


/-- Compute disjoint paths in two stored trees whose domains meet only at the
bottleneck. The returned paths are the actual parent-map recoveries. -/
def recoverLinkage {g b v : V} {T : V → Prop}
    (A : RootedTree H r S) (B : RootedTree H g T)
    (hv : S v) (hb : T b) (hoverlap : ∀ w, S w → T w → w = b)
    (hlevel : H.level b < H.level v) :
    { pq : Path H × Path H // pq.1.first = r ∧ pq.1.last = v ∧
      pq.2.first = g ∧ pq.2.last = b ∧ pq.1.Disjoint pq.2 } :=
  let p := A.recover v hv
  let q := B.recover b hb
  ⟨(p.val, q.val), p.property.1, p.property.2.1, q.property.1, q.property.2.1, by
    intro w hp hq
    have hw := hoverlap w (p.property.2.2.1 w hp) (q.property.2.2.1 w hq)
    have hl := p.val.last_level_le hp
    rw [p.property.2.1, hw] at hl
    omega⟩

end RootedTree

namespace ColoredTrees
variable {n : Nat} {H : LayeredGraph (Fin n)} {S : Fin n → Prop} {r g b : Fin n}

/-- The stored color determines which two stored parent maps recover the
linkage for a newly selected vertex. No existential path is executed. -/
def recoverLinkage (T : ColoredTrees H S r g b) (v : Fin n)
    (hv : S v) (hlevel : H.level b < H.level v) :
    { pq : Path H × Path H // pq.1.last = v ∧ pq.2.last = b ∧ pq.1.Disjoint pq.2 ∧
      ((pq.1.first = r ∧ pq.2.first = g ∧ T.color v = some false) ∨
        (pq.1.first = g ∧ pq.2.first = r ∧ T.color v = some true)) } :=
  match hc : T.color v with
  | none => False.elim (by
      have hne : v ≠ b := by intro he; rw [he] at hlevel; omega
      obtain ⟨c, hcolor⟩ := (T.domain v).2 ⟨hv, hne⟩
      rw [hc] at hcolor
      contradiction)
  | some false =>
    let pq := T.red.recoverLinkage T.green (Or.inr hc) (Or.inl rfl)
      (fun w hw hw' => (T.overlap w).1 ⟨hw, hw'⟩) hlevel
    ⟨pq.val, pq.property.2.1, pq.property.2.2.2.1, pq.property.2.2.2.2,
      Or.inl ⟨pq.property.1, pq.property.2.2.1, rfl⟩⟩
  | some true =>
    let pq := T.green.recoverLinkage T.red (Or.inr hc) (Or.inl rfl)
      (fun w hw hw' => (T.overlap w).1 ⟨hw', hw⟩) hlevel
    ⟨pq.val, pq.property.2.1, pq.property.2.2.2.1, pq.property.2.2.2.2,
      Or.inr ⟨pq.property.1, pq.property.2.2.1, rfl⟩⟩

end ColoredTrees
end MaximumMatching.DDFS
