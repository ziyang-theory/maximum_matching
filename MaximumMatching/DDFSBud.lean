import MaximumMatching.DDFSTrees
import MaximumMatching.BudLink

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
