import MaximumMatching.Augmentation

/-! Alternating components of the union of two matchings. -/
namespace MaximumMatching

/-- An M-alternating simple path whose even-indexed edges belong to N. -/
structure DifferencePath {V : Type} {G : Graph V} (M N : Matching G) where
  path : AltPath M
  other : ∀ i : Fin path.length, i.val % 2 = 0 →
    N.mate (path.vertex ⟨i.val, by omega⟩) =
      some (path.vertex ⟨i.val + 1, by omega⟩)

namespace DifferencePath
variable {V : Type} {G : Graph V} {M N : Matching G}

def trivial (M N : Matching G) (v : V) (hv : M.Free v) : DifferencePath M N where
  path := AltPath.trivial M v hv
  other := by intro i; exact Fin.elim0 i

/-- The N-neighbor of an even terminal vertex cannot have appeared already. -/
theorem other_last_fresh (p : DifferencePath M N) (heven : p.path.length % 2 = 0)
    {v : V} (hv : N.mate p.path.last = some v) : ∀ i, p.path.vertex i ≠ v := by
  intro i hi
  have hback : N.mate (p.path.vertex i) = some p.path.last := by
    simpa only [hi] using N.symm hv
  by_cases hlast : i.val = p.path.length
  · have he : p.path.vertex i = p.path.last := congrArg p.path.vertex (Fin.ext hlast)
    have hlv : p.path.last = v := he.symm.trans hi
    exact N.mate_ne_self (hlv ▸ hv)
  by_cases heven_i : i.val % 2 = 0
  · have hm := p.other ⟨i.val, by omega⟩ heven_i
    have hh := p.path.injective _ _ (N.mate_unique hm hback)
    have hval : i.val + 1 = p.path.length := congrArg Fin.val hh
    omega
  · have hpos : 0 < i.val := by omega
    have hpar : (i.val - 1) % 2 = 0 := by omega
    have hm := N.symm (p.other ⟨i.val - 1, by omega⟩ hpar)
    have he : i.val - 1 + 1 = i.val := by omega
    simp only [he] at hm
    have hh := p.path.injective _ _ (N.mate_unique hm hback)
    have hval : i.val - 1 = p.path.length := congrArg Fin.val hh
    omega

theorem other_last_unmatched (p : DifferencePath M N) (heven : p.path.length % 2 = 0)
    {v : V} (hv : N.mate p.path.last = some v) : M.mate p.path.last ≠ some v := by
  intro hM
  by_cases hz : p.path.length = 0
  · have he : p.path.last = p.path.first :=
      congrArg p.path.vertex (Fin.ext (by simpa using hz))
    have hf : M.mate p.path.first = none := p.path.start_free
    rw [he, hf] at hM
    contradiction
  · have hm := p.path.mate_previous p.path.length (by omega) (by omega) heven
    have hv' : p.path.vertex ⟨p.path.length - 1, by omega⟩ = v := M.mate_unique hm hM
    exact p.other_last_fresh heven hv _ hv'

/-- Extend by the uniquely determined N edge. -/
def appendOther (p : DifferencePath M N) (heven : p.path.length % 2 = 0)
    {v : V} (hv : N.mate p.path.last = some v) : DifferencePath M N where
  path := p.path.append v (p.other_last_fresh heven hv) (N.edge hv)
    (by constructor
        · intro h; exact False.elim (p.other_last_unmatched heven hv h)
        · intro h; omega)
  other := by
    intro i hi
    by_cases hlt : i.val < p.path.length
    · simpa only [AltPath.append, dite_eq_left (show i.val ≤ p.path.length by omega),
        dite_eq_left (show i.val + 1 ≤ p.path.length by omega)] using p.other ⟨i.val, hlt⟩ hi
    · have he : i.val = p.path.length := by
        have hib : i.val < p.path.length + 1 := i.isLt
        omega
      simp only [AltPath.append, he, Nat.le_refl, dite_true,
        show ¬p.path.length + 1 ≤ p.path.length by omega, dite_false]
      exact hv

/-- Extend by the uniquely determined M edge. -/
def appendMatched (p : DifferencePath M N) (hodd : p.path.length % 2 = 1)
    {v : V} (hv : M.mate p.path.last = some v) : DifferencePath M N where
  path := p.path.appendMatched hodd hv
  other := by
    intro i hi
    have hlt : i.val < p.path.length := by
      have hib : i.val < p.path.length + 1 := i.isLt
      omega
    simpa only [AltPath.appendMatched, AltPath.append,
      dite_eq_left (show i.val ≤ p.path.length by omega),
      dite_eq_left (show i.val + 1 ≤ p.path.length by omega)] using p.other ⟨i.val, hlt⟩ hi

@[simp] theorem appendOther_first (p : DifferencePath M N) (heven : p.path.length % 2 = 0)
    {v : V} (hv : N.mate p.path.last = some v) :
    (p.appendOther heven hv).path.first = p.path.first := by
  simp [appendOther, AltPath.first, AltPath.append]

@[simp] theorem appendOther_last (p : DifferencePath M N) (heven : p.path.length % 2 = 0)
    {v : V} (hv : N.mate p.path.last = some v) :
    (p.appendOther heven hv).path.last = v := by
  simp only [appendOther, AltPath.append_last]

@[simp] theorem appendMatched_first (p : DifferencePath M N) (hodd : p.path.length % 2 = 1)
    {v : V} (hv : M.mate p.path.last = some v) :
    (p.appendMatched hodd hv).path.first = p.path.first := by
  simp [appendMatched, AltPath.appendMatched, AltPath.first, AltPath.append]

@[simp] theorem appendMatched_last (p : DifferencePath M N) (hodd : p.path.length % 2 = 1)
    {v : V} (hv : M.mate p.path.last = some v) :
    (p.appendMatched hodd hv).path.last = v := by
  simp only [appendMatched, AltPath.appendMatched_last]

end DifferencePath

namespace AltPath
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

theorem length_lt_vertices (p : AltPath M) : p.length < n := by
  have hnodup : ((List.finRange (p.length + 1)).map p.vertex).Nodup :=
    (List.nodup_finRange _).map p.vertex (fun i j h hij => h (p.injective _ _ hij))
  have hlen := hnodup.length_le_of_subset
    (l₂ := List.finRange n) (fun v _ => List.mem_finRange v)
  simp only [List.length_map, List.length_finRange] at hlen
  omega
end AltPath
end MaximumMatching
