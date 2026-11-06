import MaximumMatching.DDFSPaths

/-! Map a directed path into another layered graph, omitting steps whose
endpoint images coincide. Every original image remains represented. -/
namespace MaximumMatching.DDFS.Path
variable {V W : Type} {H : LayeredGraph V} {K : LayeredGraph W}

private theorem contains_drop_one_iff (p : Path H) (hpos : 0 < p.length) (v : V) :
    p.Contains v ↔ v = p.first ∨ (p.drop 1 (by omega)).Contains v := by
  constructor
  · rintro ⟨i, hi⟩
    by_cases hiz : i.val = 0
    · left
      have he : i = ⟨0, by omega⟩ := Fin.ext hiz
      exact hi.symm.trans (congrArg p.vertex he)
    · right
      refine ⟨⟨i.val - 1, by have := i.isLt; change i.val - 1 < p.length - 1 + 1; omega⟩, ?_⟩
      change p.vertex ⟨1 + (i.val - 1), _⟩ = v
      simpa only [show 1 + (i.val - 1) = i.val by omega, Fin.eta] using hi
  · rintro (rfl | hv)
    · exact p.contains_first
    · exact p.contains_drop 1 (by omega) hv

/-- An edge-respecting map may identify adjacent vertices. Removing those
zero steps constructs an actual path with exactly the original image set. -/
theorem map_eq_or_edge (p : Path H) (f : V → W)
    (hedges : ∀ u v, H.Edge u v → p.Contains u → p.Contains v →
      f u = f v ∨ K.Edge (f u) (f v)) :
    ∃ q : Path K, q.first = f p.first ∧ q.last = f p.last ∧ q.length ≤ p.length ∧
      ∀ w, q.Contains w ↔ ∃ v, p.Contains v ∧ f v = w := by
  classical
  generalize hn : p.length = n
  induction n using Nat.strongRecOn generalizing p with
  | ind n ih =>
    by_cases hz : p.length = 0
    · refine ⟨Path.trivial K (f p.first), rfl, ?_, by change 0 ≤ n; omega, ?_⟩
      · have he : p.first = p.last := congrArg p.vertex (Fin.ext (by omega))
        exact congrArg f he
      · intro w
        constructor
        · rintro ⟨i, hi⟩
          exact ⟨p.first, p.contains_first, hi⟩
        · rintro ⟨v, ⟨i, hi⟩, hfv⟩
          have hie : i = ⟨0, by omega⟩ := Fin.ext (by have := i.isLt; omega)
          have hv : v = p.first := hi.symm.trans (congrArg p.vertex hie)
          exact ⟨⟨0, by simp [Path.trivial]⟩, by simpa only [hv, Path.trivial] using hfv⟩
    · have hpos : 0 < p.length := by omega
      let r := p.drop 1 (by omega)
      have hrlen : r.length = p.length - 1 := rfl
      obtain ⟨q, hqf, hql, hqlen, hqverts⟩ := ih r.length (by omega) r
        (fun u v he hu hv => hedges u v he (p.contains_drop _ _ hu) (p.contains_drop _ _ hv)) rfl
      have he : H.Edge p.first r.first := by
        simpa only [first, r, drop, Nat.add_zero] using p.adjacent ⟨0, hpos⟩
      have hrfirst : p.Contains r.first := p.contains_drop _ _ r.contains_first
      have hrends : r.last = p.last := p.drop_last _ _
      rcases hedges p.first r.first he p.contains_first hrfirst with hsame | hedge
      · refine ⟨q, hqf.trans hsame.symm, hql.trans (congrArg f hrends), by omega, ?_⟩
        intro w
        rw [hqverts]
        constructor
        · rintro ⟨v, hv, hfv⟩
          exact ⟨v, p.contains_drop _ _ hv, hfv⟩
        · rintro ⟨v, hv, hfv⟩
          rcases (p.contains_drop_one_iff hpos v).1 hv with rfl | hv
          · exact ⟨r.first, r.contains_first, hsame.symm.trans hfv⟩
          · exact ⟨v, hv, hfv⟩
      · have hedge' : K.Edge (f p.first) q.first := by rw [hqf]; exact hedge
        refine ⟨q.prepend (f p.first) hedge', rfl,
          (q.prepend_last _ _).trans (hql.trans (congrArg f hrends)), ?_, ?_⟩
        · change q.length + 1 ≤ n
          omega
        · intro w
          rw [Path.contains_prepend_iff, hqverts]
          constructor
          · rintro (rfl | ⟨v, hv, hfv⟩)
            · exact ⟨p.first, p.contains_first, rfl⟩
            · exact ⟨v, p.contains_drop _ _ hv, hfv⟩
          · rintro ⟨v, hv, hfv⟩
            rcases (p.contains_drop_one_iff hpos v).1 hv with rfl | hv
            · exact Or.inl hfv.symm
            · exact Or.inr ⟨v, hv, hfv⟩

end MaximumMatching.DDFS.Path
