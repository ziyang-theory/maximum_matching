import MaximumMatching.DDFSPaths
import MaximumMatching.PathLemmas

/-! Lifting downward paths of the layered graph to actual alternating paths.
The compatibility properties are input-graph properties; no path-existence or
disjointness conclusion is a field. Simplicity of the lifted path is derived.
-/
namespace MaximumMatching.DDFS
variable {V : Type} {G : Graph V} {M : Matching G} {H : LayeredGraph V}

structure LayeredMatching (M : Matching G) (H : LayeredGraph V) : Prop where
  adjacent : ∀ {u v}, H.Edge u v → G.Adj u v
  consecutive : ∀ {u v}, H.Edge u v → H.level u = H.level v + 1
  alternating : ∀ {u v}, H.Edge u v →
    ((M.mate v = some u) ↔ H.level v % 2 = 1)

/-- A minlevel prefix ending at the lower endpoint can be extended along the
reversal of any compatible layered path. The levels prove all freshness checks.
The final equivalence records exactly which original vertices occur. -/
theorem lift_path (compat : LayeredMatching M H) (q : Path H) (p : AltPath M)
    (hend : p.last = q.last) (hlevels : ∀ i, H.level (p.vertex i) = i.val) :
    ∃ r : AltPath M, r.first = p.first ∧ r.last = q.first ∧
      r.length = H.level q.first ∧ (∀ i, H.level (r.vertex i) = i.val) ∧
      (∀ v, (∃ i, r.vertex i = v) ↔ (∃ i, p.vertex i = v) ∨ q.Contains v) := by
  by_cases hz : q.length = 0
  · have hq : q.first = q.last := congrArg q.vertex (Fin.ext (by omega))
    refine ⟨p, rfl, hend.trans hq.symm, ?_, hlevels, ?_⟩
    · rw [hq, ← hend]
      exact (hlevels ⟨p.length, by omega⟩).symm
    · intro v
      constructor
      · exact Or.inl
      · rintro (hv | ⟨i, hi⟩)
        · exact hv
        · have he : i = ⟨q.length, by omega⟩ := Fin.ext (by omega)
          rw [he] at hi
          exact ⟨⟨p.length, by omega⟩, hend.trans hi⟩
  · let tail := q.drop 1 (by omega)
    have hedge : H.Edge q.first tail.first := q.adjacent ⟨0, by omega⟩
    have hl : H.level q.first = H.level tail.first + 1 := compat.consecutive hedge
    have htend : p.last = tail.last := by simpa [tail] using hend
    obtain ⟨s, hsf, hsl, hslen, hslevels, hsmem⟩ := lift_path compat tail p htend hlevels
    have hfresh : ∀ i, s.vertex i ≠ q.first := by
      intro i he
      have hi := hslevels i
      rw [he] at hi
      have hib := i.isLt
      omega
    have hadj : G.Adj s.last q.first := by
      rw [hsl]
      exact G.symm (compat.adjacent hedge)
    have hpar : (M.mate s.last = some q.first) ↔ s.length % 2 = 1 := by
      rw [hsl, hslen]
      exact compat.alternating hedge
    let r := s.append q.first hfresh hadj hpar
    have hrfirst : r.first = s.first := by simp [r, AltPath.append, AltPath.first]
    have hrmem (v : V) : (∃ i, r.vertex i = v) ↔ (∃ i, s.vertex i = v) ∨ v = q.first := by
      constructor
      · rintro ⟨i, hi⟩
        change (if h : i.val ≤ s.length then s.vertex ⟨i.val, _⟩ else q.first) = v at hi
        split at hi
        · exact Or.inl ⟨_, hi⟩
        · exact Or.inr hi.symm
      · rintro (⟨i, hi⟩ | hv)
        · refine ⟨⟨i.val, by change i.val < s.length + 1 + 1; omega⟩, ?_⟩
          simpa [r, AltPath.append, show i.val ≤ s.length by omega] using hi
        · exact ⟨⟨r.length, by omega⟩, (AltPath.append_last s q.first hfresh hadj hpar).trans hv.symm⟩
    have hqmem (v : V) : q.Contains v ↔ v = q.first ∨ tail.Contains v := by
      constructor
      · rintro ⟨i, hi⟩
        by_cases hi0 : i.val = 0
        · exact Or.inl (hi.symm.trans (congrArg q.vertex (Fin.ext hi0)))
        · refine Or.inr ⟨⟨i.val - 1, by change i.val - 1 < q.length - 1 + 1; omega⟩, ?_⟩
          change q.vertex ⟨1 + (i.val - 1), _⟩ = v
          simpa only [show 1 + (i.val - 1) = i.val by omega, Fin.eta] using hi
      · rintro (rfl | hv)
        · exact q.contains_first
        · exact q.contains_drop 1 (by omega) hv
    refine ⟨r, hrfirst.trans hsf, AltPath.append_last _ _ _ _ _, ?_, ?_, ?_⟩
    · change s.length + 1 = H.level q.first
      omega
    · intro i
      change H.level (if h : i.val ≤ s.length then s.vertex ⟨i.val, _⟩ else q.first) = i.val
      split
      · exact hslevels _
      · have hi := i.isLt
        change i.val < s.length + 1 + 1 at hi
        omega
    · intro v
      rw [hrmem, hsmem, hqmem]
      constructor
      · rintro ((hp | hq) | he)
        · exact Or.inl hp
        · exact Or.inr (Or.inr hq)
        · exact Or.inr (Or.inl he)
      · rintro (hp | he | hq)
        · exact Or.inl (Or.inl hp)
        · exact Or.inr he
        · exact Or.inl (Or.inr hq)
termination_by q.length
decreasing_by
  change q.length - 1 < q.length
  omega

end MaximumMatching.DDFS
