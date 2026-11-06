import MaximumMatching.SymmetricDifference

namespace MaximumMatching.DifferencePath
variable {V : Type} {G : Graph V} {M N : Matching G}

def take (p : DifferencePath M N) (k : Nat) (hk : k ≤ p.path.length) : DifferencePath M N where
  path := p.path.take k hk
  other := by
    intro i hi
    have hik : i.val < k := i.isLt
    exact p.other ⟨i.val, by omega⟩ hi

@[simp] theorem take_first (p : DifferencePath M N) (k : Nat) (hk : k ≤ p.path.length) :
    (p.take k hk).path.first = p.path.first := rfl

/-- At an even endpoint, reversing two edges is deterministic: first M, then N. -/
theorem two_back_eq (p q : DifferencePath M N)
    (hp : p.path.length % 2 = 0) (hq : q.path.length % 2 = 0)
    (hpp : 0 < p.path.length) (hqp : 0 < q.path.length)
    (he : p.path.last = q.path.last) :
    p.path.vertex ⟨p.path.length - 2, by omega⟩ =
      q.path.vertex ⟨q.path.length - 2, by omega⟩ := by
  have pm := p.path.mate_previous p.path.length (by omega) hpp hp
  have qm := q.path.mate_previous q.path.length (by omega) hqp hq
  change M.mate p.path.last = _ at pm
  change M.mate q.path.last = _ at qm
  rw [he] at pm
  have he1 := M.mate_unique pm qm
  have pn := N.symm (p.other ⟨p.path.length - 2, by omega⟩ (by change (p.path.length - 2) % 2 = 0; omega))
  have qn := N.symm (q.other ⟨q.path.length - 2, by omega⟩ (by change (q.path.length - 2) % 2 = 0; omega))
  have hpidx : p.path.length - 2 + 1 = p.path.length - 1 := by omega
  have hqidx : q.path.length - 2 + 1 = q.path.length - 1 := by omega
  simp only [hpidx] at pn
  simp only [hqidx] at qn
  rw [he1] at pn
  exact N.mate_unique pn qn

/-- Two even-length difference paths with the same last vertex start at the same
M-free vertex. This is the injectivity fact needed by the Berge counting proof. -/
theorem same_last_same_first (p q : DifferencePath M N)
    (hp : p.path.length % 2 = 0) (hq : q.path.length % 2 = 0)
    (he : p.path.last = q.path.last) : p.path.first = q.path.first := by
  by_cases hp0 : p.path.length = 0
  · have hpf : p.path.first = p.path.last :=
      congrArg p.path.vertex (Fin.ext (by omega))
    by_cases hq0 : q.path.length = 0
    · have hqf : q.path.first = q.path.last :=
        congrArg q.path.vertex (Fin.ext (by omega))
      exact hpf.trans (he.trans hqf.symm)
    · have hm := q.path.mate_previous q.path.length (by omega) (by omega) hq
      change M.mate q.path.last = some _ at hm
      have hf : M.mate q.path.last = none := by
        rw [← he, ← hpf]
        exact p.path.start_free
      rw [hf] at hm
      contradiction
  · by_cases hq0 : q.path.length = 0
    · have hqf : q.path.first = q.path.last :=
        congrArg q.path.vertex (Fin.ext (by omega))
      have hm := p.path.mate_previous p.path.length (by omega) (by omega) hp
      change M.mate p.path.last = some _ at hm
      have hf : M.mate p.path.last = none := by
        rw [he, ← hqf]
        exact q.path.start_free
      rw [hf] at hm
      contradiction
    · have heb := two_back_eq p q hp hq (by omega) (by omega) he
      exact same_last_same_first (p.take (p.path.length - 2) (by omega))
        (q.take (q.path.length - 2) (by omega)) (by dsimp [take]; omega)
        (by dsimp [take]; omega) heb
termination_by p.path.length
decreasing_by
  dsimp [take, AltPath.take]
  omega

end MaximumMatching.DifferencePath
