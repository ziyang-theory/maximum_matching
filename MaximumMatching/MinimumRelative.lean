import MaximumMatching.RelativeJoin
import MaximumMatching.MinimumBlossomPaths

/-! Arbitrary shortest relative paths inside a minimum-tenacity blossom. Such
paths are joined to an actual shortest even prefix using proved disjointness;
the global shortest-path confinement and edge-tenacity theorems then apply. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

namespace AltPath

/-- The relative segment occurs literally as the suffix of concatenation. -/
theorem appendSegment_vertex_suffix (p : AltPath M) (q : AltSegment M)
    (hpe : p.length % 2 = 0) (hjoin : p.last = q.first) (hdis)
    (j : Fin (q.length + 1)) :
    (p.appendSegment q hpe hjoin hdis).vertex
      ⟨p.length + j.val, by change p.length + j.val < p.length + q.length + 1; omega⟩ =
      q.vertex j := by
  by_cases hj : j.val = 0
  · have hj0 : j = ⟨0, by omega⟩ := Fin.ext hj
    rw [hj0]
    simpa only [appendSegment, Nat.add_zero, Nat.le_refl, dite_true,
      AltSegment.first, last] using hjoin
  · simp only [appendSegment, dite_eq_right (show ¬p.length + j.val ≤ p.length by omega),
      Nat.add_sub_cancel_left]

end AltPath

/-- At minimum eligible tenacity, every shortest relative path from an actual
base to its child stays inside the source blossom (apart from the base), and
every edge of that path has exactly the minimum tenacity. The path is arbitrary;
it need not have been extracted from an existing global path. -/
theorem IsBase.minimum_relative_properties {v b : V} (hb : IsBase M v b)
    (t : Nat) (ht : EligibleTenacity M t) (hvt : tenacity M v = some t)
    (hmin : ∀ w : V, levelLE (some t) (tenacity M w))
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v) :
    (∀ j : Fin (q.length + 1), 0 < j.val → Blossom M t b (q.vertex j)) ∧
      (∀ k : Fin q.length, edgeTenacity M (q.vertex ⟨k.val, by omega⟩)
        (q.vertex ⟨k.val + 1, by omega⟩) = some t) := by
  obtain ⟨s, r, _, hrv, hr, _⟩ := hb.path
  obtain ⟨i, hib, hie, _, _, hip⟩ := hb.on_shortest r hrv hr
  let p := r.take i.val (by omega)
  have hp : p.Shortest := hip
  have hpe : p.length % 2 = 0 := hie
  have hpb : p.last = b := hib
  let hdis := hb.relative_avoids_prefix p hp hpe hpb q hq hqb hqv
  let joined := p.appendSegment q hpe (hpb.trans hqb.symm) hdis
  have hjshort : joined.Shortest := hb.append_relative_shortest p hp hpe hpb q hq hqb hqv
  have hjend : joined.last = v := (p.appendSegment_last q hpe (hpb.trans hqb.symm) hdis).trans hqv
  have hjten : tenacity M joined.last = some t := hjend ▸ hvt
  have hjbase : joined.BaseOnPath t b := (isBase_iff_common t hvt).1 hb joined hjend hjshort
  let baseIndex : Fin (joined.length + 1) := ⟨p.length, by change p.length < p.length + q.length + 1; omega⟩
  have hbase : joined.vertex baseIndex = b := by
    change (if h : p.length ≤ p.length then p.vertex ⟨p.length, _⟩ else _) = b
    simpa only [Nat.le_refl, dite_true, AltPath.last] using hpb
  have hvertex (j : Fin (q.length + 1)) :
      joined.vertex ⟨p.length + j.val, by change p.length + j.val < p.length + q.length + 1; omega⟩ =
        q.vertex j := p.appendSegment_vertex_suffix q hpe (hpb.trans hqb.symm) hdis j
  constructor
  · intro j hj
    have hc := joined.minimum_suffix_in_blossom hjshort t ht hjten hmin b hjbase baseIndex
      ⟨p.length + j.val, by change p.length + j.val < p.length + q.length + 1; omega⟩ hbase
      (by change p.length < p.length + j.val; omega)
    rwa [hvertex] at hc
  · intro k
    have hc := joined.minimum_suffix_edge_tenacity hjshort t hjten hmin b hjbase baseIndex
      hbase ⟨p.length + k.val, by change p.length + k.val < p.length + q.length; omega⟩
      (by change p.length ≤ p.length + k.val; omega)
    have hv0 := hvertex ⟨k.val, by omega⟩
    have hv1 := hvertex ⟨k.val + 1, by omega⟩
    simpa only [Nat.add_assoc, hv0, hv1] using hc

/-- The set-theoretic confinement statement for an arbitrary shortest relative
path in a minimum-tenacity blossom. -/
theorem IsBase.minimum_relative_confined {v b : V} (hb : IsBase M v b)
    (t : Nat) (ht : EligibleTenacity M t) (hvt : tenacity M v = some t)
    (hmin : ∀ w : V, levelLE (some t) (tenacity M w))
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v) :
    ∀ w, q.Contains w → w = b ∨ Blossom M t b w := by
  intro w hw
  obtain ⟨j, rfl⟩ := hw
  by_cases hj : j.val = 0
  · have hj0 : j = ⟨0, by omega⟩ := Fin.ext hj
    exact Or.inl (by rw [hj0]; exact hqb)
  · exact Or.inr ((hb.minimum_relative_properties t ht hvt hmin q hq hqb hqv).1 j (by omega))

/-- Theorem 6.19(4), confinement and edge-tenacity parts of the minimum-tenacity
basis, stated for any member of a source blossom and any shortest relative path. -/
theorem minimum_blossom_relative_paths (t : Nat) (ht : EligibleTenacity M t)
    (hmin : ∀ w : V, levelLE (some t) (tenacity M w)) (b v : V)
    (hv : Blossom M t b v) (q : AltSegment M) (hq : q.Shortest)
    (hqb : q.first = b) (hqv : q.last = v) :
    (∀ w, q.Contains w → w = b ∨ Blossom M t b w) ∧
      (∀ k : Fin q.length, edgeTenacity M (q.vertex ⟨k.val, by omega⟩)
        (q.vertex ⟨k.val + 1, by omega⟩) = some t) := by
  have htwo : 2 ≤ t := by
    cases t with
    | zero => exact False.elim hv
    | succ t =>
      cases t with
      | zero => exact False.elim hv
      | succ t => omega
  have hs := (minimum_blossom_iff t htwo hmin b v).1 hv
  exact ⟨hs.2.minimum_relative_confined t ht hs.1 hmin q hq hqb hqv,
    (hs.2.minimum_relative_properties t ht hs.1 hmin q hq hqb hqv).2⟩

end MaximumMatching
