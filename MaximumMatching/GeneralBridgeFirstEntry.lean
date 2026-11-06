import MaximumMatching.GeneralBridgeSplit
import MaximumMatching.GeneralEdgeHelpers
import MaximumMatching.GeneralBlossomProps

/-! The bridge recurrence at a first lower-blossom entry. The crossing has
current tenacity, while the actual reversed tail has only lower-tenacity edges. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Original tail edges inherit the lower bound from the actual shortest
reversed relative path; symmetry handles their orientation. -/
theorem first_entry_tail_edge_ne (p : AltPath M) (hpo : p.length % 2 = 1)
    (t : Nat) (hpt : tenacity M p.last = some t)
    (hedge : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ i : Fin q.length, levelLE (edgeTenacity M (q.vertex ⟨i.val, by omega⟩)
          (q.vertex ⟨i.val + 1, by omega⟩)) (some (t - 2)))
    (D : Fin (p.length + 1)) (hDmem : Blossom M (t - 2) p.last (p.vertex D))
    (htail : (p.reverseOddTail hpo D).Shortest) (i : Fin p.length) (hDi : D.val ≤ i.val) :
    edgeTenacity M (p.vertex ⟨i.val, by omega⟩) (p.vertex ⟨i.val + 1, by omega⟩) ≠ some t := by
  have htodd := tenacity_odd M p.last t hpt
  have hc : levelLT (some (t - 2)) (tenacity M p.last) := by rw [hpt]; change t - 2 < t; omega
  let q := p.reverseOddTail hpo D
  let K : Fin q.length := ⟨p.length - (i.val + 1), by change p.length - (i.val + 1) < p.length - D.val; omega⟩
  have hbound := hedge p.last (p.vertex D) hDmem hc q htail
    (p.reverseOddTail_first hpo D) (p.reverseOddTail_last hpo D) K
  have hleft : q.vertex ⟨K.val, by omega⟩ = p.vertex ⟨i.val + 1, by omega⟩ := by
    change p.vertex ⟨p.length - (p.length - (i.val + 1)), _⟩ = _
    congr 1
    apply Fin.ext
    change p.length - (p.length - (i.val + 1)) = i.val + 1
    omega
  have hright : q.vertex ⟨K.val + 1, by omega⟩ = p.vertex ⟨i.val, by omega⟩ := by
    change p.vertex ⟨p.length - (p.length - (i.val + 1) + 1), _⟩ = _
    congr 1
    apply Fin.ext
    change p.length - (p.length - (i.val + 1) + 1) = i.val
    omega
  rw [hleft, hright, edgeTenacity_symmetric] at hbound
  intro he
  rw [he] at hbound
  change t ≤ t - 2 at hbound
  omega

/-- A prop crossing into the endpoint's lower blossom must be traversed
backwards, so the honest outside prefix is a current-tenacity maxlevel path. -/
theorem first_entry_prop_prefix_maxlevel (p : AltPath M) (hp : p.Shortest)
    (hpo : p.length % 2 = 1) (t : Nat) (hpt : tenacity M p.last = some t)
    (hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w)
    (D : Fin (p.length + 1)) (hDo : D.val % 2 = 1)
    (hDmem : Blossom M (t - 2) p.last (p.vertex D))
    (hfirst : ∀ a : Fin (p.length + 1), a.val < D.val → ¬Blossom M (t - 2) p.last (p.vertex a))
    (htail : (p.reverseOddTail hpo D).Shortest)
    (hprefix : p.BFSHonest ⟨D.val - 1, by omega⟩)
    (hprop : PropEdge M (p.vertex ⟨D.val - 1, by omega⟩) (p.vertex D)) :
    tenacity M (p.vertex ⟨D.val - 1, by omega⟩) = some t ∧
      maxlevel M (p.vertex ⟨D.val - 1, by omega⟩) = some (D.val - 1) := by
  have htodd := tenacity_odd M p.last t hpt
  have hc : levelLT (some (t - 2)) (tenacity M p.last) := by rw [hpt]; change t - 2 < t; omega
  have hreverse : Predecessor M (p.vertex D) (p.vertex ⟨D.val - 1, by omega⟩) := by
    rcases hprop with hforward | hreverse
    · rcases blossom_predecessor_mem (t - 2) p.last (p.vertex ⟨D.val - 1, by omega⟩)
        (p.vertex D) hDmem hc hconf hforward with he | hm
      · have hi := congrArg Fin.val (p.injective ⟨D.val - 1, by omega⟩ ⟨p.length, by omega⟩ he)
        change D.val - 1 = p.length at hi
        have := D.isLt
        omega
      · exact False.elim (hfirst ⟨D.val - 1, by omega⟩ (by change D.val - 1 < D.val; omega) hm)
    · exact hreverse
  let r := p.take (D.val - 1) (by omega)
  have hre : r.length % 2 = 0 := by change (D.val - 1) % 2 = 0; omega
  have hm : M.mate r.last ≠ some (p.vertex D) := by
    intro h
    change M.mate (p.vertex ⟨D.val - 1, by omega⟩) = some (p.vertex D) at h
    have hh := (p.alternating ⟨D.val - 1, by omega⟩).1
      (by simpa only [show D.val - 1 + 1 = D.val by omega] using h)
    change (D.val - 1) % 2 = 1 at hh
    omega
  exact r.even_prefix_maxlevel_of_reverse_prop hprefix hre (p.vertex D) hreverse hm t
    (p.first_entry_edge_tenacity hp hpo t hpt D hDo hDmem htail hprefix)

end MaximumMatching.AltPath
