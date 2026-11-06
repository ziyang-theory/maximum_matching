import MaximumMatching.ActivePetalRecord

/-! Sound current-level assignments from trees computed on the live graph.
The colored trees lift to original predecessor edges; no assertion that the
live region equals the region of the undeleted graph is required. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}
namespace CurrentBridgeRepresentation
variable {cap cut : Nat} {s : State (Fin n)} {F : BudForest (Fin n)}
    {h : BudGraphInvariant M cap s F}

theorem colored_linkage_support (P : CurrentBridgeRepresentation M cut h)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (u v : Fin n) (hbridge : Bridge M u v)
    (ht : MaximumMatching.edgeTenacity M u v = some (cut + 2))
    (hu : ∃ k, s.minLabel u = some k) (hv : ∃ k, s.minLabel v = some k)
    (b : Fin n) (S : Fin n → Prop)
    (T : DDFS.ColoredTrees (predecessorGraph s F h) S (F.root u) (F.root v) b)
    (w : Fin n) (hw : S w)
    (hlevel : (predecessorGraph s F h).level b < (predecessorGraph s F h).level w) :
    tenacity M w = some (cut + 2) ∧ InSupport M u v w := by
  obtain ⟨p, q, hpw, hqb, hdis, hstart⟩ := T.bottom_linkage h.reachBottom w hw hlevel
  have hrootu : ∃ k, s.minLabel (F.root u) = some k := by
    obtain ⟨k, hk⟩ := hu
    exact h.rootAssigned u k hk
  have hrootv : ∃ k, s.minLabel (F.root v) = some k := by
    obtain ⟨k, hk⟩ := hv
    exact h.rootAssigned v k hk
  have hpa : ∃ k, s.minLabel p.first = some k := by
    rcases hstart with ⟨hpu, _, _⟩ | ⟨hpv, _, _⟩
    · rw [hpu]; exact hrootu
    · rw [hpv]; exact hrootv
  have hpf : F.parent p.first = p.first := by
    rcases hstart with ⟨hpu, _, _⟩ | ⟨hpv, _, _⟩
    · rw [hpu]; exact F.root_fixed u
    · rw [hpv]; exact F.root_fixed v
  have hwfixed : F.parent w = w := by
    have hh := h.path_fixed p hpf ⟨p.length, by omega⟩
    simpa only [show p.vertex ⟨p.length, by omega⟩ = w from hpw] using hh
  have hwassigned : ∃ k, s.minLabel w = some k := by
    have hh := h.path_assigned p hpa ⟨p.length, by omega⟩
    simpa only [show p.vertex ⟨p.length, by omega⟩ = w from hpw] using hh
  obtain ⟨k, hk⟩ := hwassigned
  have hwhigh : levelLT (some cut) (tenacity M w) := by
    have hh := P.high w k hk
    rwa [F.root_of_fixed w hwfixed] at hh
  have hex : ∃ z : AltPath M, z.last = w ∧ z.length + k = cut + 2 ∧ z.ContainsEdge u v := by
    rcases hstart with ⟨hpu, hqv, _⟩ | ⟨hpv, hqu, _⟩
    · obtain ⟨z, _, hzw, hlen, he⟩ := P.bridge_linkage_path u v
        hbridge ht hu hv p q hpu hqv hqb hdis
      rw [hpw, hk] at hlen
      exact ⟨z, hzw.trans hpw, hlen, he⟩
    · obtain ⟨z, _, hzw, hlen, he⟩ := P.bridge_linkage_path v u
        (bridge_symm hbridge) ((edgeTenacity_symmetric v u).trans ht) hv hu p q hpv hqu hqb hdis
      rw [hpw, hk] at hlen
      exact ⟨z, hzw.trans hpw, hlen, (z.containsEdge_symm v u).1 he⟩
  obtain ⟨z, hzw, hlen, he⟩ := hex
  have hmin : minlevel M z.last = some k := by rw [hzw]; exact h.minInvariant.1.1 w k hk
  obtain ⟨hzt, hmax⟩ := z.maxlevel_of_complementary_length cut k hc hmin
    (by rw [hzw]; exact hwhigh) hlen
  have hwt : tenacity M w = some (cut + 2) := by rwa [hzw] at hzt
  exact ⟨hwt, hbridge, cut + 2, htop, ht, hwt, z, hzw,
    by rwa [hzw] at hmax, he⟩

end CurrentBridgeRepresentation

namespace ActivePetalRecord
variable {i cut : Nat}

/-- Retain the stored parent maps while viewing each live edge as an original
predecessor edge. This does not lift the all-path bottleneck assertion. -/
def ambientTrees (R : ActivePetalRecord M i cut) :
    DDFS.ColoredTrees (predecessorGraph R.prior R.forest R.invariant)
      R.selected (R.forest.root R.left) (R.forest.root R.right) R.bottleneck where
  color := R.trees.color
  bottleneck_mem := R.trees.bottleneck_mem
  domain := R.trees.domain
  red := {
    parent := R.trees.red.parent
    root_none := R.trees.red.root_none
    edge := fun u v he => ⟨(R.trees.red.edge u v he).1,
      (R.trees.red.edge u v he).2.1, (R.trees.red.edge u v he).2.2.2.2⟩
    spanning := R.trees.red.spanning }
  green := {
    parent := R.trees.green.parent
    root_none := R.trees.green.root_none
    edge := fun u v he => ⟨(R.trees.green.edge u v he).1,
      (R.trees.green.edge u v he).2.1, (R.trees.green.edge u v he).2.2.2.2⟩
    spanning := R.trees.green.spanning }

/-- Every newly merged live root has exactly the current tenacity and belongs
to the triggering bridge's semantic support in the original matching. -/
theorem newRoots_support_of_current (R : ActivePetalRecord M i cut)
    (P : CurrentBridgeRepresentation M cut R.invariant)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) (v : Fin n) (hv : v ∈ R.newRoots) :
    MaximumMatching.tenacity M v = some (2 * i + 1) ∧ InSupport M R.left R.right v := by
  obtain ⟨hs, hn⟩ := (R.mem_newRoots v).1 hv
  have hl := DDFS.onRootTo_level_gt ((R.region v).1 hs) hn
  have hlevel : (predecessorGraph R.prior R.forest R.invariant).level R.bottleneck <
      (predecessorGraph R.prior R.forest R.invariant).level v := by
    change (R.prior.minLabel R.bottleneck).getD 0 < (R.prior.minLabel v).getD 0
    simpa only [R.input.level_live v (R.selected_live v hs),
      R.input.level_live R.bottleneck (R.selected_live _ R.trees.bottleneck_mem)] using hl
  have hh := P.colored_linkage_support hc htop R.left R.right R.trigger.1
    (by rw [hstageTen]; exact R.trigger.2) R.starts_assigned.1 R.starts_assigned.2
    R.bottleneck R.selected R.ambientTrees v hs hlevel
  exact ⟨by simpa only [hstageTen] using hh.1, hh.2⟩

section
variable [DecidableRel G.Adj]

def maxEvent (R : ActivePetalRecord M i cut) : State (Fin n) × BudForest (Fin n) :=
  (maxProcessVertices M i R.newRoots R.prior, R.after)

theorem maxEvent_minLabel (R : ActivePetalRecord M i cut) (v : Fin n) :
    R.maxEvent.1.minLabel v = R.prior.minLabel v :=
  maxProcessVertices_minLabel M i R.newRoots R.prior v

theorem maxEvent_outside (R : ActivePetalRecord M i cut) (v : Fin n) (hv : v ∉ R.newRoots) :
    R.maxEvent.1.maxLabel v = R.prior.maxLabel v :=
  maxProcessVertices_outside_maxLabel M i R.newRoots R.prior v hv

theorem maxEvent_bucket_mono (R : ActivePetalRecord M i cut)
    (u v : Fin n) (t : Nat) (h : (u, v) ∈ R.prior.bucket t) :
    (u, v) ∈ R.maxEvent.1.bucket t :=
  maxProcessVertices_bucket_mono M i R.prior R.newRoots u v t h

/-- The lower-cutoff root bound survives because every new root was already
an assigned old root; it is independent of deletion completeness. -/
theorem maxEvent_high (R : ActivePetalRecord M i cut)
    (P : CurrentBridgeRepresentation M cut R.invariant) :
    ∀ v k, R.maxEvent.1.minLabel v = some k →
      levelLT (some cut) (tenacity M (R.after.root v)) := by
  intro v k hv
  have hold : R.prior.minLabel v = some k := (R.maxEvent_minLabel v).symm.trans hv
  rw [R.after_root]
  split
  · obtain ⟨j, hj⟩ := R.selected_assigned R.bottleneck R.trees.bottleneck_mem
    have hh := P.high R.bottleneck j hj
    rwa [R.selected_root R.bottleneck R.trees.bottleneck_mem] at hh
  · exact P.high v k hold

/-- MAX keeps the full semantic stage state and bud invariant after an active
petal contraction, despite computing its region in the restricted graph. -/
theorem maxEvent_correct_of_current (R : ActivePetalRecord M i cut)
    (P : CurrentBridgeRepresentation M cut R.invariant)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) :
    StageState M (i + 1) (2 * i + 1) R.maxEvent.1 ∧
      BudGraphInvariant M (i + 1) R.maxEvent.1 R.maxEvent.2 ∧
      (∀ v, v ∈ R.newRoots → R.maxEvent.1.maxLabel v = maxlevel M v) ∧
      (∀ v k, R.prior.maxLabel v = some k → R.maxEvent.1.maxLabel v = some k) := by
  have hroots : ∀ v, v ∈ R.newRoots → MaximumMatching.tenacity M v = some (2 * i + 1) :=
    fun v hv => (R.newRoots_support_of_current P hc htop hstageTen v hv).1
  have hs := maxProcessVertices_stageState M i (2 * i + 1) R.newRoots R.prior R.input.B.stage hroots
  refine ⟨hs, ?_, ?_, ?_⟩
  · refine ⟨hs.min, hs.minBound, ?_, ?_⟩
    · intro v k hv
      have hold : R.prior.minLabel v = some k := (R.maxEvent_minLabel v).symm.trans hv
      obtain ⟨j, hj⟩ := R.after_invariant.rootAssigned v k hold
      exact ⟨j, (R.maxEvent_minLabel (R.after.root v)).trans hj⟩
    · intro v
      exact (R.after_invariant.rankLabel v).trans (congrArg (fun x : Option Nat => x.getD 0)
        (R.maxEvent_minLabel v).symm)
  · intro v hv
    exact maxProcessVertices_member_correct M i (2 * i + 1) R.newRoots R.prior R.input.B.stage hroots v hv
  · intro v k hv
    exact maxProcessVertices_preserves_known_maxLabel M i (2 * i + 1) R.newRoots R.prior R.input.B.stage hroots v k hv

end
end ActivePetalRecord
end MaximumMatching.Search
