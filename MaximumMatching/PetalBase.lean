import MaximumMatching.BasePathTransfer
import MaximumMatching.CurrentBridgeRepresentation

section PetalBasePaths

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

end PetalBasePaths

section PetalBase

/-! Same-level petal contractions preserve semantic base classes. A temporary
bud may have the current tenacity, so the class relation permits either a
higher base or another current-tenacity vertex with the same canonical base. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

/-- Every vertex already absorbed into a different bud has bounded tenacity. -/
def NonrootLow (M : Matching G) (t : Nat) (F : BudForest V) : Prop :=
  ∀ v, F.root v ≠ v → levelLE (MaximumMatching.tenacity M v) (some t)

theorem nonrootLow_of_lower (h : BudGraphInvariant M cap s F)
    (hrep : LowerBlossomRepresentation M cut s F) : NonrootLow M (cut + 2) F := by
  intro v hne
  cases hv : s.minLabel v with
  | none => exact False.elim (hne (F.root_of_fixed v (h.unknown_fixed v hv)))
  | some k =>
    rcases (hrep v k hv).2 with he | hb
    · exact False.elim (hne he.symm)
    · obtain ⟨a, ha, hat⟩ := blossom_tenacity_bound cut (F.root v) v hb
      rw [ha]
      change a ≤ cut + 2
      omega

namespace PetalRecord
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G} {cut : Nat}

theorem after_nonrootLow (R : PetalRecord M)
    (P : CurrentBridgeRepresentation M cut R.invariant)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hten : R.tenacity = cut + 2) (hlow : NonrootLow M (cut + 2) R.forest) :
    NonrootLow M (cut + 2) R.after := by
  intro v hne
  by_cases hv : R.forest.root v = v
  · have hs : R.selected v := by
      apply Classical.byContradiction
      intro hs
      have he := R.after_outside v (by change ¬ R.selected (R.forest.root v); rwa [hv])
      exact hne (he.trans hv)
    have hvb : v ≠ R.bottleneck := by
      intro he
      have ha := R.after_selected v (by change R.selected (R.forest.root v); rwa [hv])
      exact hne (ha.trans he.symm)
    have ht := (R.newRoots_support_of_current P hc htop hten v ((R.mem_newRoots v).2 ⟨hs, hvb⟩)).1
    rw [ht, hten]
    exact Nat.le_refl _
  · exact hlow v hv

/-- Selected roots share the bottleneck's eventual canonical base. If the
bottleneck already has higher tenacity, it is itself that base. The proof uses
an actual shortest expanded path and its honest boundary prefix. -/
theorem selected_base_relation (R : PetalRecord M)
    (P : CurrentBridgeRepresentation M cut R.invariant)
    (hc : cut % 2 = 1) (hnoaug : ∀ p : AltPath M, p.Augmenting → cut + 2 < p.length)
    (hten : R.tenacity = cut + 2) (hlow : NonrootLow M (cut + 2) R.forest)
    (w : Fin n) (hw : R.selected w) (hne : w ≠ R.bottleneck) :
    IsBase M w R.bottleneck ∨
      (MaximumMatching.tenacity M R.bottleneck = some (cut + 2) ∧
        ∃ b, IsBase M w b ∧ IsBase M R.bottleneck b) := by
  have htop : AtMostShortestAugmenting M (cut + 2) := fun p hp => Nat.le_of_lt (hnoaug p hp)
  have hwt := (R.newRoots_support_of_current P hc htop hten w ((R.mem_newRoots w).2 ⟨hw, hne⟩)).1
  rw [hten] at hwt
  have ht : EligibleTenacity M (cut + 2) :=
    ⟨by omega, ⟨w, by rw [hwt]; exact Nat.le_refl _⟩, hnoaug⟩
  obtain ⟨p, hpf, hpl, hps⟩ := R.selected_tail w hw
  obtain ⟨q, hqf, hqb⟩ := R.invariant.reachBottom R.bottleneck
  have hpfix : ∀ v, p.Contains v → R.forest.root v = v := by
    intro v hv
    exact R.forest.root_of_fixed v (R.selected_fixed v (hps v hv))
  have hqfix : ∀ v, q.Contains v → R.forest.root v = v := by
    rintro v ⟨i, rfl⟩
    exact R.forest.root_of_fixed _ (R.invariant.path_fixed q
      (by rw [hqf]; exact R.selected_fixed _ R.trees.bottleneck_mem) i)
  have hpa : ∃ k, R.prior.minLabel p.first = some k := by
    rw [hpf]
    exact R.selected_assigned.2 w hw
  have hqa : ∃ k, R.prior.minLabel q.first = some k := by
    rw [hqf]
    exact R.selected_assigned.1
  obtain ⟨z, hzw, hz, i, hib, hminb, hprefix, htail⟩ :=
    P.realize_bottom_suffix p q hpfix hqfix (hpl.trans hqf.symm) hpa hqa hqb
  have hzw' : z.last = w := hzw.trans hpf
  have hib' : z.vertex i = R.bottleneck := hib.trans hpl
  have hzt : MaximumMatching.tenacity M z.last = some (cut + 2) := by rw [hzw']; exact hwt
  have hlowtail : ∀ j : Fin (z.length + 1), i.val < j.val →
      levelLE (MaximumMatching.tenacity M (z.vertex j)) (some (cut + 2)) := by
    intro j hij
    by_cases hfix : R.forest.root (z.vertex j) = z.vertex j
    · have hs := hps _ (htail j hij)
      rw [hfix] at hs
      have hjb : z.vertex j ≠ R.bottleneck := by
        intro he
        have heq := congrArg Fin.val (z.injective j i (he.trans hib'.symm))
        omega
      have htenj := (R.newRoots_support_of_current P hc htop hten _ ((R.mem_newRoots _).2 ⟨hs, hjb⟩)).1
      rw [htenj, hten]
      exact Nat.le_refl _
    · exact hlow _ hfix
  by_cases hbhigh : levelLT (some (cut + 2)) (MaximumMatching.tenacity M R.bottleneck)
  · left
    have hb := z.isBase_of_high_suffix_boundary hz (cut + 2) ht hzt i
      (by rw [hib']; exact hbhigh) hlowtail
    rwa [hzw', hib'] at hb
  · have hbt : MaximumMatching.tenacity M R.bottleneck = some (cut + 2) := by
      obtain ⟨k, hk⟩ := R.selected_assigned.1
      have hhigh := P.high R.bottleneck k hk
      rw [R.forest.root_of_fixed _ (R.selected_fixed _ R.trees.bottleneck_mem)] at hhigh
      cases hb : MaximumMatching.tenacity M R.bottleneck with
      | none => exact False.elim (hbhigh (by simp only [hb, levelLT]))
      | some a =>
        have haodd := tenacity_odd M R.bottleneck a hb
        rw [hb] at hhigh hbhigh
        change cut < a at hhigh
        change ¬cut + 2 < a at hbhigh
        have he : a = cut + 2 := by omega
        rw [he]
    right
    obtain ⟨b, hzb, hibase⟩ := z.common_base_of_shortest_prefix hz (cut + 2) ht hzt i
      (by rw [hib']; exact hbt) hprefix hlowtail
    exact ⟨hbt, b, hzw' ▸ hzb, hib' ▸ hibase⟩

end PetalRecord
end MaximumMatching.Search

end PetalBase

section PetalBaseClasses

/-! Preservation of canonical blossom classes while temporary buds still have
current tenacity. Once all surviving roots are above the current threshold,
this invariant yields the next level's lower-blossom representation. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

/-- Two vertices have the same membership in every valid blossom together
with its high-tenacity boundary. No temporary bud is required to be high. -/
def SameBlossomClass (M : Matching G) (t : Nat) (u v : V) : Prop :=
  ∀ b, levelLT (some t) (tenacity M b) →
    ((u = b ∨ Blossom M t b u) ↔ (v = b ∨ Blossom M t b v))

namespace SameBlossomClass

omit [DecidableEq V] in
theorem refl (u : V) : SameBlossomClass M t u u := fun _ _ => Iff.rfl

omit [DecidableEq V] in
theorem symm (h : SameBlossomClass M t u v) : SameBlossomClass M t v u :=
  fun b hb => (h b hb).symm

omit [DecidableEq V] in
theorem trans (h : SameBlossomClass M t u v) (h' : SameBlossomClass M t v w) :
    SameBlossomClass M t u w := fun b hb => (h b hb).trans (h' b hb)

omit [DecidableEq V] in
/-- Following the actual base chain below a threshold preserves the class. -/
theorem of_blossom (ht : t % 2 = 1) (h : Blossom M t v u) : SameBlossomClass M t u v := by
  intro b hb
  have hu := blossom_to_cut t v u h
  have hfun : BaseTree.Functional (IsBase M) := fun _ _ _ h₁ h₂ => h₁.unique h₂
  constructor
  · rintro (he | hu')
    · obtain ⟨a, ha, hat⟩ := blossom_tenacity_bound t v u h
      rw [← he, ha] at hb
      change t < a at hb
      omega
    · rcases BaseTree.Below.boundary_comparison hfun (fun _ h => h) (by
        intro hlow
        cases ht' : tenacity M b with
        | none => simp only [ht', levelLE] at hlow
        | some a =>
          rw [ht'] at hb hlow
          change t < a at hb
          change a ≤ t at hlow
          omega) hu (blossom_to_cut t b u hu') with hvb | hvb
      · exact Or.inl hvb
      · exact Or.inr (blossom_of_base_cut t ht b v hvb)
  · rintro (rfl | hv)
    · exact Or.inr h
    · exact Or.inr (blossom_of_base_cut t ht b u (hu.trans (blossom_to_cut t b v hv)))

end SameBlossomClass

/-- Bud lookup preserves each vertex's canonical class at the stated cutoff. -/
def BudBlossomClasses (M : Matching G) (t : Nat) (F : BudForest V) : Prop :=
  ∀ v, SameBlossomClass M t v (F.root v)

theorem budBlossomClasses_of_lower (h : BudGraphInvariant M cap s F)
    (hc : cut % 2 = 1) (hrep : LowerBlossomRepresentation M cut s F) :
    BudBlossomClasses M (cut + 2) F := by
  intro v
  by_cases he : F.root v = v
  · rw [he]
    exact SameBlossomClass.refl v
  · cases hv : s.minLabel v with
    | none => exact False.elim (he (F.root_of_fixed v (h.unknown_fixed v hv)))
    | some k =>
      rcases (hrep v k hv).2 with hv' | hbl
      · exact False.elim (he hv'.symm)
      · exact SameBlossomClass.of_blossom (by omega)
          (blossom_mono cut (cut + 2) (by omega) (by omega) (F.root v) v hbl)

/-- High surviving roots turn class preservation into the exact
lower-blossom invariant needed by the next MIN stage. -/
theorem BudBlossomClasses.lower_representation (h : BudBlossomClasses M t F)
    (hhigh : ∀ v k, s.minLabel v = some k → levelLT (some t) (tenacity M (F.root v))) :
    LowerBlossomRepresentation M t s F := by
  intro v k hv
  have hh := hhigh v k hv
  exact ⟨hh, (h v (F.root v) hh).2 (Or.inl rfl)⟩

namespace PetalRecord
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G} {cut : Nat}

theorem selected_sameBlossomClass (R : PetalRecord M)
    (P : CurrentBridgeRepresentation M cut R.invariant)
    (hc : cut % 2 = 1) (hnoaug : ∀ p : AltPath M, p.Augmenting → cut + 2 < p.length)
    (hten : R.tenacity = cut + 2) (hlow : NonrootLow M (cut + 2) R.forest)
    (w : Fin n) (hw : R.selected w) :
    SameBlossomClass M (cut + 2) w R.bottleneck := by
  by_cases he : w = R.bottleneck
  · rw [he]
    exact SameBlossomClass.refl _
  · have hwt := (R.newRoots_support_of_current P hc (fun p hp => Nat.le_of_lt (hnoaug p hp))
      hten w ((R.mem_newRoots w).2 ⟨hw, he⟩)).1
    rw [hten] at hwt
    rcases R.selected_base_relation P hc hnoaug hten hlow w hw he with hb | ⟨hbt, b, hwb, hbb⟩
    · exact SameBlossomClass.of_blossom (by omega) (Or.inl ⟨hwt, hb⟩)
    · exact (SameBlossomClass.of_blossom (by omega) (show Blossom M (cut + 2) b w from
        Or.inl ⟨hwt, hwb⟩)).trans
        (SameBlossomClass.of_blossom (by omega) (show Blossom M (cut + 2) b R.bottleneck from
          Or.inl ⟨hbt, hbb⟩)).symm

/-- Actual recorded contraction preserves canonical classes, including
contractions whose temporary bottleneck has current tenacity. -/
theorem after_blossomClasses (R : PetalRecord M)
    (P : CurrentBridgeRepresentation M cut R.invariant)
    (hc : cut % 2 = 1) (hnoaug : ∀ p : AltPath M, p.Augmenting → cut + 2 < p.length)
    (hten : R.tenacity = cut + 2) (hlow : NonrootLow M (cut + 2) R.forest)
    (hclasses : BudBlossomClasses M (cut + 2) R.forest) :
    BudBlossomClasses M (cut + 2) R.after := by
  intro v
  by_cases hs : R.selectedFiber v
  · rw [R.after_selected v hs]
    exact (hclasses v).trans (R.selected_sameBlossomClass P hc hnoaug hten hlow (R.forest.root v) hs)
  · rw [R.after_outside v hs]
    exact hclasses v

end PetalRecord
end MaximumMatching.Search

end PetalBaseClasses
