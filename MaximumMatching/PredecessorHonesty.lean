import MaximumMatching.MinimumBridgeAll

/-! Lemma 6.18: honesty at a predecessor immediately before a vertex of the
endpoint's tenacity on a minlevel path. The proof establishes a stronger local
statement: the successor may have any tenacity at least that of the endpoint;
no restriction on the predecessor's tenacity or the path-relative base is needed.
-/
namespace MaximumMatching

variable {V : Type} {G : Graph V} {M : Matching G}

/-- Every finite tenacity is at least twice the minimum of its parity levels. -/
theorem twice_minlevel_le_tenacity (v : V) (k t : Nat)
    (hk : minlevel M v = some k) (ht : tenacity M v = some t) : 2 * k ≤ t := by
  obtain ⟨e, o, he, ho, _, _, hsum⟩ := finite_levels_of_tenacity v t ht
  have hm : min e o = k := by
    simpa only [minlevel, he, ho, levelMin, Option.some.injEq] using hk
  have he' := Nat.min_le_left e o
  have ho' := Nat.min_le_right e o
  omega

namespace AltPath

/-- A predecessor on a minimum-level path is BFS-honest whenever its successor
has tenacity at least that of the endpoint. This implies the local conclusion
of Lemma 6.18, including both endpoint parities and infinite successor tenacity. -/
theorem minlevel_predecessor_honest (p : AltPath M) (hp : p.Shortest)
    (hminpath : minlevel M p.last = some p.length)
    (t : Nat) (hten : tenacity M p.last = some t) (i : Fin p.length)
    (hsucc : levelLE (some t) (tenacity M (p.vertex ⟨i.val + 1, by omega⟩))) :
    p.BFSHonest ⟨i.val, by omega⟩ := by
  have htwice := twice_minlevel_le_tenacity p.last p.length t hminpath hten
  by_cases hie : i.val % 2 = 0
  · let u := p.vertex ⟨i.val, by omega⟩
    let w := p.vertex ⟨i.val + 1, by omega⟩
    have hsuccw : levelLE (some t) (tenacity M w) := hsucc
    have hwhon := (p.limited_bfs_honesty hp ⟨i.val + 1, by omega⟩ (by
      rw [hten]; exact hsucc)).1
    have hwo : oddlevel M w = some (i.val + 1) := by
      have hh := (p.honest_iff_level ⟨i.val + 1, by omega⟩).1 hwhon
      simpa only [show (i.val + 1) % 2 = 1 by omega] using hh
    obtain ⟨a, ha, hak⟩ := p.prefix_level_bound ⟨i.val, by omega⟩
    change a ≤ i.val at hak
    have hue : evenlevel M u = some a := by simpa only [hie] using ha
    apply (p.honest_iff_level ⟨i.val, by omega⟩).2
    change level M (i.val % 2) u = some i.val
    rw [hie]
    change evenlevel M u = some i.val
    rw [hue]
    apply congrArg some
    apply Nat.le_antisymm hak
    apply Nat.le_of_not_lt
    intro halt
    obtain ⟨q, hqu, hqa, hqpar⟩ := ((level_eq_some_iff M 0 u a).1 hue).1
    have hfresh : ∀ j, q.vertex j ≠ w := by
      intro j hj
      by_cases hje : j.val % 2 = 0
      · obtain ⟨b, hb, hbj⟩ := q.prefix_level_bound j
        have hwe : evenlevel M w = some b := by
          simpa only [hje, hj] using hb
        have hbound : t ≤ b + (i.val + 1) := by
          simpa only [tenacity, hwe, hwo, levelAdd, levelLE] using hsuccw
        omega
      · have hjo : j.val % 2 = 1 := by omega
        have hwitness : HasPathLength M 1 w j.val := by
          simpa only [hjo, hj] using q.prefix_witness j
        have hbound := ((level_eq_some_iff M 1 w (i.val + 1)).1 hwo).2 j.val hwitness
        omega
    have hpar : (M.mate q.last = some w) ↔ q.length % 2 = 1 := by
      rw [hqu, hqa]
      have hstep : (M.mate u = some w) ↔ i.val % 2 = 1 := p.alternating i
      simp only [hstep, hie, hqpar]
    have hadj : G.Adj q.last w := by rw [hqu]; exact p.adjacent i
    let r := q.append w hfresh hadj hpar
    have hr : HasPathLength M 1 w (a + 1) :=
      ⟨r, append_last _ _ _ _ _, by change q.length + 1 = a + 1; omega, by omega⟩
    have hbad := ((level_eq_some_iff M 1 w (i.val + 1)).1 hwo).2 (a + 1) hr
    omega
  · have hio : i.val % 2 = 1 := by omega
    have hmate := (p.alternating i).2 hio
    have hteneq := (matched_tenacity M hmate).1
    exact (p.limited_bfs_honesty hp ⟨i.val, by omega⟩ (by rw [hten, hteneq]; exact hsucc)).1

end AltPath
end MaximumMatching
