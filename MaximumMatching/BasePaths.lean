import MaximumMatching.BlossomLaminar

/-! Every iterated common base occurs on every shortest path to its descendant.
Each occurrence is an even, honest minimum-level prefix. These facts follow from
the actual common-base relation and finite parent chains, without general base
existence or blossom-confinement assumptions. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A direct common base is an internal even vertex of every shortest path,
and the prefix to it attains its minimum level. -/
theorem IsBase.on_shortest {v b : V} (h : IsBase M v b)
    (p : AltPath M) (hpv : p.last = v) (hp : p.Shortest) :
    ∃ i : Fin (p.length + 1), p.vertex i = b ∧ i.val % 2 = 0 ∧ i.val < p.length ∧
      minlevel M b = some i.val ∧ (p.take i.val (by omega)).Shortest := by
  obtain ⟨t, ht, hcommon⟩ := (show IsBase M v b from h)
  have hpb := hcommon p hpv hp
  have hpt : tenacity M p.last = some t := hpv ▸ ht
  obtain ⟨i, hi, hie⟩ := p.baseOnPath_even t hpt hpb
  have hhigh : levelLT (tenacity M p.last) (tenacity M (p.vertex i)) := by
    rw [hpt, hi]
    exact hpb.choose_spec.2.1
  obtain ⟨hhon, hmin⟩ := p.limited_bfs_honesty hp i (levelLT_le hhigh)
  have hlt : i.val < p.length := by
    by_cases hlt : i.val < p.length
    · exact hlt
    · have he : i = ⟨p.length, by omega⟩ := Fin.ext (by change i.val = p.length; omega)
      have hbv : b = v := by rw [← hi, he]; exact hpv
      exact False.elim (h.ne hbv.symm)
  refine ⟨i, hi, hie, hlt, ?_, ?_⟩
  · simpa only [hi] using hmin hhigh
  · exact hhon

/-- A finite chain of actual bases propagates through the shortest prefixes.
The allowed-region predicate only specifies the chain; no property of it is
assumed in this theorem. -/
theorem base_chain_on_shortest {A : V → Prop} {b v : V}
    (h : BaseTree.Below (IsBase M) A b v)
    (p : AltPath M) (hpv : p.last = v) (hp : p.Shortest) :
    ∃ i : Fin (p.length + 1), p.vertex i = b ∧ i.val % 2 = 0 ∧ i.val < p.length ∧
      minlevel M b = some i.val ∧ (p.take i.val (by omega)).Shortest := by
  induction h generalizing p with
  | edge hbase _ => exact hbase.on_shortest p hpv hp
  | @step v w b hbase _ _ ih =>
    obtain ⟨j, hj, hje, hjlt, hjmin, hjshort⟩ := hbase.on_shortest p hpv hp
    obtain ⟨i, hi, hie, hilt, himin, hishort⟩ := ih (p.take j.val (by omega)) hj hjshort
    have hib : i.val < p.length + 1 := by
      change i.val < j.val at hilt
      omega
    refine ⟨⟨i.val, hib⟩, ?_, hie, ?_, himin, ?_⟩
    · exact hi
    · change i.val < j.val at hilt
      change i.val < p.length
      omega
    · exact hishort

/-- In particular, every threshold-cut root is an even minimum-level prefix
of every shortest path to any vertex in that cut. -/
theorem base_cut_on_shortest (t : Nat) (b v : V)
    (h : BaseTree.Cut (IsBase M) (tenacity M) t b v)
    (p : AltPath M) (hpv : p.last = v) (hp : p.Shortest) :
    ∃ i : Fin (p.length + 1), p.vertex i = b ∧ i.val % 2 = 0 ∧ i.val < p.length ∧
      minlevel M b = some i.val ∧ (p.take i.val (by omega)).Shortest :=
  base_chain_on_shortest h p hpv hp

/-- Every member of a source-recursive blossom has its base on every shortest
path, with an even minimum-level prefix. This establishes the prefix-location
part of Theorem 6.19(4), independently of the relative suffix minimality proof. -/
theorem blossom_on_shortest (t : Nat) (b v : V) (h : Blossom M t b v)
    (p : AltPath M) (hpv : p.last = v) (hp : p.Shortest) :
    ∃ i : Fin (p.length + 1), p.vertex i = b ∧ i.val % 2 = 0 ∧ i.val < p.length ∧
      minlevel M b = some i.val ∧ (p.take i.val (by omega)).Shortest :=
  base_cut_on_shortest t b v (blossom_to_cut t b v h) p hpv hp

end MaximumMatching
