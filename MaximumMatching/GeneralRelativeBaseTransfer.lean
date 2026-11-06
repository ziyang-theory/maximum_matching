import MaximumMatching.GeneralBlossomJoin
import MaximumMatching.MinimumRelative

/-! Transfer actual base occurrences from global shortest paths to arbitrary
shortest relative segments by the proved shortest, simple joining operation. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A global base-occurrence property after an iterated boundary transfers to
any shortest relative path from that boundary. The located base belongs to the
relative segment itself, including its initial boundary. -/
theorem blossom_relative_base_occurs_of_global (t : Nat) (c v : V)
    (hv : Blossom M t c v) (hc : levelLT (some t) (tenacity M c))
    (hglobal : ∀ p : AltPath M, p.Shortest → p.last = v →
      ∀ (i j : Fin (p.length + 1)), p.vertex i = c → i.val < j.val →
        ∃ b, IsBase M (p.vertex j) b ∧ ∃ k : Fin (p.length + 1), i.val ≤ k.val ∧ p.vertex k = b)
    (q : AltSegment M) (hq : q.Shortest) (hqc : q.first = c) (hqv : q.last = v)
    (j : Fin (q.length + 1)) (hj : 0 < j.val) :
    ∃ b, IsBase M (q.vertex j) b ∧ q.Contains b := by
  obtain ⟨s, hs, _⟩ := blossom_tenacity_bound t c v hv
  obtain ⟨r, hrv, hr, _⟩ := finite_tenacity_shortest_parity v s 0 hs
  obtain ⟨i, hic, hie, _, _, hip⟩ := blossom_on_shortest t c v hv r hrv hr
  let p := r.take i.val (by omega)
  have hp : p.Shortest := hip
  have hpe : p.length % 2 = 0 := hie
  have hpc : p.last = c := hic
  let hdis := blossom_relative_avoids_prefix t c v hv hc p hp hpe hpc q hq hqc hqv
  let a := p.appendSegment q hpe (hpc.trans hqc.symm) hdis
  have ha : a.Shortest := blossom_append_relative_shortest t c v hv hc p hp hpe hpc q hq hqc hqv
  have hav : a.last = v := (p.appendSegment_last q hpe (hpc.trans hqc.symm) hdis).trans hqv
  let I : Fin (a.length + 1) := ⟨p.length, by change p.length < p.length + q.length + 1; omega⟩
  have hIc : a.vertex I = c := by
    change (if h : p.length ≤ p.length then p.vertex ⟨p.length, _⟩ else _) = c
    simpa only [Nat.le_refl, dite_true, AltPath.last] using hpc
  let J : Fin (a.length + 1) := ⟨p.length + j.val, by change p.length + j.val < p.length + q.length + 1; omega⟩
  have hJq : a.vertex J = q.vertex j := p.appendSegment_vertex_suffix q hpe (hpc.trans hqc.symm) hdis j
  obtain ⟨b, hb, k, hIk, hkb⟩ := hglobal a ha hav I J hIc
    (by change p.length < p.length + j.val; omega)
  refine ⟨b, by simpa only [hJq] using hb, ?_⟩
  have hkbound := k.isLt
  change k.val < p.length + q.length + 1 at hkbound
  change p.length ≤ k.val at hIk
  let l : Fin (q.length + 1) := ⟨k.val - p.length, by omega⟩
  have hindex : (⟨p.length + l.val, by change p.length + l.val < p.length + q.length + 1; omega⟩ :
      Fin (a.length + 1)) = k := by
    apply Fin.ext
    change p.length + (k.val - p.length) = k.val
    omega
  have hkl : a.vertex k = q.vertex l := by
    rw [← hindex]
    exact p.appendSegment_vertex_suffix q hpe (hpc.trans hqc.symm) hdis l
  exact ⟨l, hkl.symm.trans hkb⟩

end MaximumMatching
