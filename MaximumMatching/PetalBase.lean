import MaximumMatching.PetalBasePaths
import MaximumMatching.PetalCurrentMax

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
