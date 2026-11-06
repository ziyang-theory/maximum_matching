import MaximumMatching.BudForest
import MaximumMatching.DDFSGeometry
import MaximumMatching.DDFSTrees
import MaximumMatching.WeightedRecovery

section DDFSBud

/-! Execute DDFS and contract exactly its bottleneck region in a bud forest.
The checked representation premises align current roots and ranks with the
layered search graph. Matching-specific support correspondence is separate. -/
namespace MaximumMatching.DDFS
variable {n : Nat} {H : LayeredGraph (Fin n)}

namespace ColoredTrees
variable {S : Fin n → Prop} {r g b : Fin n}

/-- Enumerate the actual reconstructed region using its computed colors. -/
def vertices (T : ColoredTrees H S r g b) : List (Fin n) :=
  (List.finRange n).filter fun v => decide (v = b) || (T.color v).isSome

theorem mem_vertices (T : ColoredTrees H S r g b) (v : Fin n) : v ∈ T.vertices ↔ S v := by
  simp only [vertices, List.mem_filter, List.mem_finRange, true_and, Bool.or_eq_true,
    decide_eq_true_eq, Option.isSome_iff_exists]
  constructor
  · rintro (he | hc)
    · exact he ▸ T.bottleneck_mem
    · exact ((T.domain v).1 hc).1
  · intro hv
    by_cases he : v = b
    · exact Or.inl he
    · exact Or.inr ((T.domain v).2 ⟨hv, he⟩)

end ColoredTrees

/-- Every nonterminal vertex of an actual root-to-bottleneck path has larger
layer than the bottleneck. -/
theorem onRootTo_level_gt {r g b v : Fin n} (hv : OnRootTo (H := H) r g b v) (hne : v ≠ b) :
    H.level b < H.level v := by
  obtain ⟨p, _, hpb, i, hiv⟩ := hv
  have hil : i.val < p.length := by
    by_cases he : i.val = p.length
    · have hi : i = ⟨p.length, by omega⟩ := Fin.ext he
      exact False.elim (hne (hiv.symm.trans ((congrArg p.vertex hi).trans hpb)))
    · have := i.isLt
      omega
  have hh := p.level_strict i ⟨p.length, by omega⟩ hil
  simpa only [hiv, show p.vertex ⟨p.length, by omega⟩ = b from hpb] using hh

namespace Machine.FullOutput
variable {r g : Fin n}

/-- Merge the actual finite bottleneck region into its reported boundary.
The disjoint-path outcome does not request a contraction. -/
def contract (out : FullOutput H r g) (F : BudForest (Fin n)) : BudForest (Fin n) :=
  match out with
  | .disjoint _ _ _ _ _ => F
  | .bottleneck b _ trees _ _ => F.mergeManyInto trees.vertices b

theorem contract_rank (out : FullOutput H r g) (F : BudForest (Fin n)) (v : Fin n) :
    (out.contract F).rank v = F.rank v := by
  cases out with
  | disjoint => rfl
  | bottleneck b S trees highest region => exact F.mergeManyInto_rank trees.vertices b v

theorem contract_root_congr (out : FullOutput H r g) (F : BudForest (Fin n)) (u v : Fin n)
    (h : F.root u = F.root v) : (out.contract F).root u = (out.contract F).root v := by
  cases out with
  | disjoint => exact h
  | bottleneck b S trees highest region => exact F.mergeManyInto_root_congr trees.vertices b u v h

/-- The actual search region supplies every rank guard; no closure of a
caller-supplied support set is assumed. -/
theorem contract_bottleneck_source (F : BudForest (Fin n)) (b : Fin n) (S : Fin n → Prop)
    (trees : ColoredTrees H S r g b) (highest : HighestBottleneck H r g b)
    (region : ∀ v, S v ↔ OnRootTo (H := H) r g b v)
    (hrank : ∀ v, F.rank v = H.level v) (hfixed : ∀ v, S v → F.parent v = v)
    (v : Fin n) (hv : S v) :
    ((FullOutput.bottleneck b S trees highest region).contract F).root v = b := by
  have hb : F.root b = b := F.root_of_fixed b (hfixed b trees.bottleneck_mem)
  have hvr : F.root v = v := F.root_of_fixed v (hfixed v hv)
  change (F.mergeManyInto trees.vertices b).root v = b
  apply Eq.trans ?_ hb
  apply F.mergeManyInto_source trees.vertices v b ((trees.mem_vertices v).2 hv)
  rw [hb, hvr]
  by_cases he : v = b
  · exact Or.inr he
  · apply Or.inl
    rw [hrank b, hrank v]
    exact onRootTo_level_gt ((region v).1 hv) he

/-- Previously compressed descendants of any selected root are contracted
with that root, by preservation of existing root equivalence. -/
theorem contract_bottleneck_class (F : BudForest (Fin n)) (b : Fin n) (S : Fin n → Prop)
    (trees : ColoredTrees H S r g b) (highest : HighestBottleneck H r g b)
    (region : ∀ v, S v ↔ OnRootTo (H := H) r g b v)
    (hrank : ∀ v, F.rank v = H.level v) (hfixed : ∀ v, S v → F.parent v = v)
    (v : Fin n) (hv : S (F.root v)) :
    ((FullOutput.bottleneck b S trees highest region).contract F).root v = b := by
  let out := FullOutput.bottleneck b S trees highest region
  have he := out.contract_root_congr F v (F.root v) (F.root_idempotent v).symm
  exact he.trans (contract_bottleneck_source F b S trees highest region hrank hfixed (F.root v) hv)

end Machine.FullOutput

namespace Machine
variable {r g : Fin n}

/-- Run the actual executable DDFS once, retain its certified full outcome,
and perform the corresponding finite guarded bud contraction. -/
def executeAndContract [DecidableRel H.Edge] (hreach : ReachBottom H)
    (r g : Fin n) (F : BudForest (Fin n)) : FullOutput H r g × BudForest (Fin n) :=
  let out := executeFull hreach r g
  (out, out.contract F)

theorem executeAndContract_output [DecidableRel H.Edge] (hreach : ReachBottom H)
    (r g : Fin n) (F : BudForest (Fin n)) :
    (executeAndContract hreach r g F).1 = executeFull hreach r g := rfl

theorem executeAndContract_rank [DecidableRel H.Edge] (hreach : ReachBottom H)
    (r g : Fin n) (F : BudForest (Fin n)) (v : Fin n) :
    (executeAndContract hreach r g F).2.rank v = F.rank v :=
  (executeFull hreach r g).contract_rank F v

/-- Every selected root of an actual bottleneck run, including all its old
bud descendants, has the reported bottleneck as its resulting root. -/
theorem executeAndContract_bottleneck [DecidableRel H.Edge] (hreach : ReachBottom H)
    (r g : Fin n) (F : BudForest (Fin n)) (b : Fin n) (S : Fin n → Prop)
    (trees : ColoredTrees H S r g b) (highest : HighestBottleneck H r g b)
    (region : ∀ v, S v ↔ OnRootTo (H := H) r g b v)
    (hout : executeFull hreach r g = .bottleneck b S trees highest region)
    (hrank : ∀ v, F.rank v = H.level v) (hfixed : ∀ v, S v → F.parent v = v)
    (v : Fin n) (hv : S (F.root v)) :
    (executeAndContract hreach r g F).2.root v = b := by
  change ((executeFull hreach r g).contract F).root v = b
  rw [hout]
  exact FullOutput.contract_bottleneck_class F b S trees highest region hrank hfixed v hv

end Machine
end MaximumMatching.DDFS

end DDFSBud

section DDFSRootTargets

namespace MaximumMatching.DDFS
variable {n : Nat} {H : LayeredGraph (Fin n)}

/-- Root-valued search edges preserve the root representation along every
actual path whose initial vertex is a fixed forest root. -/
theorem Path.fixed_roots (p : Path H) (F : BudForest (Fin n))
    (hedge : ∀ u v, H.Edge u v → F.parent v = v)
    (hfirst : F.parent p.first = p.first) (j : Fin (p.length + 1)) :
    F.parent (p.vertex j) = p.vertex j := by
  by_cases hj : j.val = 0
  · have hj0 : j = ⟨0, by omega⟩ := Fin.ext hj
    rw [hj0]
    exact hfirst
  · have hh := hedge _ _ (p.adjacent ⟨j.val - 1, by omega⟩)
    have he : (⟨j.val - 1 + 1, by omega⟩ : Fin (p.length + 1)) = j := Fin.ext (by change j.val - 1 + 1 = j.val; omega)
    simpa only [he] using hh

/-- The actual reported region consists of fixed roots whenever its two
starts are fixed and every search edge targets a fixed root. -/
theorem onRootTo_fixed_root (F : BudForest (Fin n))
    (hedge : ∀ u v, H.Edge u v → F.parent v = v)
    (r g b v : Fin n) (hr : F.parent r = r) (hg : F.parent g = g)
    (hv : OnRootTo (H := H) r g b v) : F.parent v = v := by
  obtain ⟨p, hfirst, _, j, hj⟩ := hv
  have hf : F.parent p.first = p.first := by
    rcases hfirst with hpr | hpg
    · rw [hpr]; exact hr
    · rw [hpg]; exact hg
  simpa only [hj] using p.fixed_roots F hedge hf j

namespace Machine

/-- The root-valued graph representation discharges selected-root fixedness
for the actual executable search and contraction, rather than assuming it
separately for the returned support. -/
theorem executeAndContract_root_targets [DecidableRel H.Edge] (hreach : ReachBottom H)
    (r g : Fin n) (F : BudForest (Fin n)) (b : Fin n) (S : Fin n → Prop)
    (trees : ColoredTrees H S r g b) (highest : HighestBottleneck H r g b)
    (region : ∀ v, S v ↔ OnRootTo (H := H) r g b v)
    (hout : executeFull hreach r g = .bottleneck b S trees highest region)
    (hrank : ∀ v, F.rank v = H.level v)
    (hedge : ∀ u v, H.Edge u v → F.parent v = v)
    (hr : F.parent r = r) (hg : F.parent g = g)
    (v : Fin n) (hv : S (F.root v)) :
    (executeAndContract hreach r g F).2.root v = b := by
  exact executeAndContract_bottleneck hreach r g F b S trees highest region hout hrank
    (fun w hw => onRootTo_fixed_root F hedge r g b w hr hg ((region w).1 hw)) v hv

end Machine
end MaximumMatching.DDFS

end DDFSRootTargets

section DDFSColoredLinkage

/-! Per-vertex disjoint linkages in the actual reconstructed colored trees.
The paths follow the recorded parents; a continuation below the bottleneck
can be appended without meeting the opposite, strictly higher endpoint. -/
namespace MaximumMatching.DDFS
variable {V : Type} {H : LayeredGraph V}

namespace RootedTree

theorem path_within {r : V} {S : V → Prop} (T : RootedTree H r S)
    (v : V) (hv : S v) :
    ∃ p : Path H, p.first = r ∧ p.last = v ∧
      (∀ w, p.Contains w → S w) ∧
      ∀ i : Fin p.length, T.parent (p.vertex ⟨i.val + 1, by omega⟩) =
        some (p.vertex ⟨i.val, by omega⟩) := by
  obtain ⟨p, hpf, hpl, hparent⟩ := T.path v hv
  refine ⟨p, hpf, hpl, ?_, hparent⟩
  rintro w ⟨j, rfl⟩
  by_cases hj : j.val < p.length
  · exact (T.edge _ _ (hparent ⟨j.val, hj⟩)).1
  · have hjl : j = ⟨p.length, by omega⟩ := Fin.ext (by change j.val = p.length; have := j.isLt; omega)
    simpa only [hjl, show p.vertex ⟨p.length, by omega⟩ = v from hpl] using hv

/-- Two tree domains that meet only at `b` give disjoint paths to a vertex
above `b` and to `b`, respectively. -/
theorem linkage_above {r g b v : V} {S T : V → Prop}
    (A : RootedTree H r S) (B : RootedTree H g T)
    (hv : S v) (hb : T b) (hoverlap : ∀ w, S w → T w → w = b)
    (hlevel : H.level b < H.level v) : Linkage H r g v b := by
  obtain ⟨p, hpr, hpv, hps, _⟩ := A.path_within v hv
  obtain ⟨q, hqg, hqb, hqt, _⟩ := B.path_within b hb
  refine ⟨p, q, hpr, hpv, hqg, hqb, ?_⟩
  intro w hpw hqw
  have hwb := hoverlap w (hps w hpw) (hqt w hqw)
  have hl := p.last_level_le hpw
  rw [hpv, hwb] at hl
  omega

end RootedTree

namespace ColoredTrees
variable {n : Nat} {H : LayeredGraph (Fin n)} {S : Fin n → Prop} {r g b : Fin n}

/-- The actual color selects which root can be joined to the chosen vertex
while the other is joined disjointly to the reported bottleneck. -/
theorem linkage (T : ColoredTrees H S r g b) (v : Fin n)
    (hv : S v) (hlevel : H.level b < H.level v) :
    (T.color v = some false ∧ Linkage H r g v b) ∨
      (T.color v = some true ∧ Linkage H g r v b) := by
  have hne : v ≠ b := by intro he; rw [he] at hlevel; omega
  obtain ⟨c, hc⟩ := (T.domain v).2 ⟨hv, hne⟩
  cases c
  · exact Or.inl ⟨hc, T.red.linkage_above T.green (Or.inr hc) (Or.inl rfl)
      (fun w hw hw' => (T.overlap w).1 ⟨hw, hw'⟩) hlevel⟩
  · exact Or.inr ⟨hc, T.green.linkage_above T.red (Or.inr hc) (Or.inl rfl)
      (fun w hw hw' => (T.overlap w).1 ⟨hw', hw⟩) hlevel⟩

/-- Continue the opposite tree to a genuine layer-zero vertex. The selected
vertex remains strictly above the continuation, so disjointness is retained. -/
theorem bottom_linkage (T : ColoredTrees H S r g b) (hreach : ReachBottom H)
    (v : Fin n) (hv : S v) (hlevel : H.level b < H.level v) :
    ∃ p q : Path H, p.last = v ∧ H.level q.last = 0 ∧ p.Disjoint q ∧
      ((p.first = r ∧ q.first = g ∧ T.color v = some false) ∨
        (p.first = g ∧ q.first = r ∧ T.color v = some true)) := by
  obtain ⟨d, hdf, hdb⟩ := hreach b
  have extend (a c : Fin n) (hc : Linkage H a c v b) :
      ∃ p q : Path H, p.last = v ∧ H.level q.last = 0 ∧ p.Disjoint q ∧
        p.first = a ∧ q.first = c := by
    obtain ⟨p, q, hpa, hpv, hqc, hqb, hd⟩ := hc
    have hj : q.last = d.first := hqb.trans hdf.symm
    exact ⟨p, q.append d hj, hpv, by simpa only [Path.append_last] using hdb,
      p.disjoint_append_below q d hj hd (by rw [hqb, hpv]; exact hlevel),
      hpa, by simpa only [Path.append_first] using hqc⟩
  rcases T.linkage v hv hlevel with ⟨hc, hl⟩ | ⟨hc, hl⟩
  · obtain ⟨p, q, hpv, hqb, hd, hpr, hqg⟩ := extend r g hl
    exact ⟨p, q, hpv, hqb, hd, Or.inl ⟨hpr, hqg, hc⟩⟩
  · obtain ⟨p, q, hpv, hqb, hd, hpg, hqr⟩ := extend g r hl
    exact ⟨p, q, hpv, hqb, hd, Or.inr ⟨hpg, hqr, hc⟩⟩

end ColoredTrees
end MaximumMatching.DDFS

end DDFSColoredLinkage
