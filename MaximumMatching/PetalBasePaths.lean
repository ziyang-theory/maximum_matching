import MaximumMatching.CurrentBridgeSupport
import MaximumMatching.GeneralBasePathTransfer

/-! Actual shortest paths through a surviving petal boundary. The weighted
predecessor representation supplies the path and its exact boundary position;
semantic base transfer then uses only the tenacities of its suffix. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

omit [DecidableEq V] in
private theorem shortest_of_minlevel (p : AltPath M)
    (hm : minlevel M p.last = some p.length) : p.Shortest := by
  refine ⟨⟨p, rfl, rfl, rfl⟩, ?_⟩
  intro k hk
  obtain ⟨q, hq, hlen, _⟩ := hk
  have hl := minlevel_le_path M p.last p.length hm q hq
  omega

namespace CurrentBridgeRepresentation
variable {cap cut : Nat} {s : State V} {F : BudForest V}
    {h : BudGraphInvariant M cap s F}

/-- Expand a descending root path followed by a bottom path. The common
boundary occurs at its semantic minimum level on the resulting shortest
matching path. Every later vertex comes from the first root path's fibers. -/
theorem realize_bottom_suffix (P : CurrentBridgeRepresentation M cut h)
    (p q : DDFS.Path (predecessorGraph s F h))
    (hpfix : ∀ v, p.Contains v → F.root v = v)
    (hqfix : ∀ v, q.Contains v → F.root v = v)
    (hjoin : p.last = q.first)
    (hpa : ∃ k, s.minLabel p.first = some k)
    (hqa : ∃ k, s.minLabel q.first = some k)
    (hbottom : (predecessorGraph s F h).level q.last = 0) :
    ∃ z : AltPath M, z.last = p.first ∧ z.Shortest ∧
      ∃ i : Fin (z.length + 1), z.vertex i = p.last ∧
        minlevel M p.last = some i.val ∧ (z.take i.val (by omega)).Shortest ∧
        ∀ j : Fin (z.length + 1), i.val < j.val → p.Contains (F.root (z.vertex j)) := by
  let pr := p.restrictRoots F hpfix
  let qr := q.restrictRoots F hqfix
  obtain ⟨a, haf, hal, han, hap, hae, hah, _⟩ := P.weighted.realize pr hpfix
  obtain ⟨b, hbf, hbl, hbn, hbp, hbe, hbh, hbavoid⟩ := P.weighted.realize qr hqfix
  have hj : a.last = b.first := hal.trans (hjoin.trans hbf.symm)
  have hp : (a.phase + a.length) % 2 = b.phase % 2 := by
    exact hae.trans ((congrArg (fun v => P.weighted.phase v % 2) hjoin).trans hbp.symm)
  have hd : ∀ (i : Fin (a.length + 1)) (j : Fin (b.length + 1)),
      0 < j.val → a.vertex i ≠ b.vertex j := by
    intro i j hjp hij
    have hai : p.Contains (F.root (b.vertex j)) := by rw [← hij]; exact hah _ ⟨i, rfl⟩
    have hbj : q.Contains (F.root (b.vertex j)) := hbh _ ⟨j, rfl⟩
    have he : F.root (b.vertex j) = q.first :=
      q.contains_eq_first_of_level_ge hbj (by rw [← hjoin]; exact p.last_level_le hai)
    have hbfirst := (hbavoid _ ⟨j, rfl⟩ he).trans hbf.symm
    have hidx := congrArg Fin.val (b.injective j ⟨0, by omega⟩ hbfirst)
    dsimp only at hidx
    omega
  let a' := a.append b hp hj hd
  have hphase : a'.reverse.phase % 2 = 0 := by
    have hlast := hbe.trans (P.phase q.last)
    change (s.minLabel q.last).getD 0 = 0 at hbottom
    change (a.phase + (a.length + b.length) + 1) % 2 = 0
    rw [hbottom] at hlast
    omega
  have hfree : M.Free a'.reverse.first := by
    rw [ParitySegment.reverse_first, ParitySegment.append_last, hbl]
    exact h.path_bottom_free q hqa hbottom
  let z := (a'.reverse.toAltSegment hphase).fromFree hfree
  have hzf : z.last = p.first := by
    exact a'.reverse_last.trans ((a.append_first b hp hj hd).trans haf)
  have hwa := P.weighted.weight_add_potential (fun v => (s.minLabel v).getD 0) P.drop pr
  have hwb := P.weighted.weight_add_potential (fun v => (s.minLabel v).getD 0) P.drop qr
  rw [← han] at hwa
  rw [← hbn] at hwb
  change a.length + (s.minLabel p.last).getD 0 = (s.minLabel p.first).getD 0 at hwa
  change b.length + (s.minLabel q.last).getD 0 = (s.minLabel q.first).getD 0 at hwb
  change (s.minLabel q.last).getD 0 = 0 at hbottom
  have hbn' : b.length = (s.minLabel p.last).getD 0 := by rw [hbottom, ← hjoin] at hwb; omega
  have hzn : z.length = (s.minLabel p.first).getD 0 := by
    change a.length + b.length = _
    omega
  have hzm : minlevel M z.last = some z.length := by
    obtain ⟨k, hk⟩ := hpa
    rw [hzf, hzn, hk]
    exact h.minInvariant.1.1 p.first k hk
  let i : Fin (z.length + 1) := ⟨b.length, by change b.length < a.length + b.length + 1; omega⟩
  have hi : z.vertex i = p.last := by
    change (if h : a.length + b.length - b.length ≤ a.length then
      a.vertex ⟨a.length + b.length - b.length, _⟩ else b.vertex ⟨_, _⟩) = _
    simp only [Nat.add_sub_cancel, Nat.le_refl, dite_true]
    exact hal
  have hminb : minlevel M p.last = some i.val := by
    obtain ⟨k, hk⟩ := hqa
    have hk' : s.minLabel p.last = some k := by rwa [hjoin]
    have := h.minInvariant.1.1 p.last k hk'
    simpa only [i, hbn', hk', Option.getD_some] using this
  refine ⟨z, hzf, shortest_of_minlevel z hzm, i, hi, hminb, ?_, ?_⟩
  · apply shortest_of_minlevel
    simpa only [AltPath.take_last, AltPath.take_length, hi] using hminb
  · intro j hij
    have hjbound := j.isLt
    change j.val < a.length + b.length + 1 at hjbound
    change b.length < j.val at hij
    have hidx : a.length + b.length - j.val ≤ a.length := by omega
    change p.Contains (F.root ((if h : a.length + b.length - j.val ≤ a.length then
      a.vertex ⟨a.length + b.length - j.val, _⟩ else b.vertex ⟨_, _⟩)))
    rw [dite_eq_left hidx]
    exact hah _ ⟨_, rfl⟩

end CurrentBridgeRepresentation
end MaximumMatching.Search
