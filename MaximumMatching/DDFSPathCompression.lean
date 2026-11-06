import MaximumMatching.DDFSPaths

/-! Compress a finite interval into a directed path by retaining exactly the
selected indices. The adjacency premise applies only to consecutive selected
indices; no path or reachability witness is assumed. -/
namespace MaximumMatching.DDFS
variable {V : Type} {H : LayeredGraph V}

private theorem least_index (P : Nat → Prop) (hex : ∃ k, P k) :
    ∃ k, P k ∧ ∀ l, l < k → ¬ P l := by
  classical
  obtain ⟨k, hk⟩ := hex
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hs : ∃ l, l < k ∧ P l
    · obtain ⟨l, hl, hp⟩ := hs
      exact ih l hl hp
    · exact ⟨k, hk, fun l hl hp => hs ⟨l, hl, hp⟩⟩

/-- Consecutive selected original indices give an actual directed path. Its
vertex set is exactly the selected indices in the interval, and compression
cannot increase the original interval's length. -/
theorem path_of_consecutive_indices {L : Nat} (x : Fin (L + 1) → V)
    (P : Fin (L + 1) → Prop) (A B : Fin (L + 1))
    (hAB : A.val ≤ B.val) (hA : P A) (hB : P B)
    (hedges : ∀ I J : Fin (L + 1), A.val ≤ I.val → I.val < J.val →
      J.val ≤ B.val → P I → P J →
      (∀ K : Fin (L + 1), I.val < K.val → K.val < J.val → ¬ P K) →
      H.Edge (x I) (x J)) :
    ∃ p : Path H, p.first = x A ∧ p.last = x B ∧ p.length ≤ B.val - A.val ∧
      ∀ v, p.Contains v ↔ ∃ I : Fin (L + 1),
        A.val ≤ I.val ∧ I.val ≤ B.val ∧ P I ∧ x I = v := by
  classical
  generalize hd : B.val - A.val = d
  induction d using Nat.strongRecOn generalizing A B with
  | ind d ih =>
    by_cases heq : A = B
    · subst B
      refine ⟨Path.trivial H (x A), rfl, rfl, ?_, ?_⟩
      · exact Nat.zero_le _
      · intro v
        constructor
        · rintro ⟨i, hi⟩
          exact ⟨A, Nat.le_refl _, Nat.le_refl _, hA, hi⟩
        · rintro ⟨I, hAI, hIA, hI, hi⟩
          have hIAeq : I = A := Fin.ext (by omega)
          subst I
          exact ⟨⟨0, by simp [Path.trivial]⟩, hi⟩
    · have hlt : A.val < B.val := by
        have hneq : A.val ≠ B.val := fun h => heq (Fin.ext h)
        omega
      obtain ⟨j, ⟨J, hj, hAJ, hJB, hJ⟩, hleast⟩ :=
        least_index (fun k => ∃ J : Fin (L + 1), J.val = k ∧
          A.val < J.val ∧ J.val ≤ B.val ∧ P J)
          ⟨B.val, B, rfl, hlt, Nat.le_refl _, hB⟩
      have hnext : ∀ K : Fin (L + 1), A.val < K.val → K.val < J.val → ¬ P K := by
        intro K hAK hKJ hK
        exact hleast K.val (by omega) ⟨K, rfl, hAK, by omega, hK⟩
      have hJBd : B.val - J.val < d := by omega
      obtain ⟨q, hqfirst, hqlast, hqlen, hqvertices⟩ :=
        ih (B.val - J.val) hJBd J B hJB hJ hB
          (fun I K hJI hIK hKB hI hK hgap =>
            hedges I K (by omega) hIK hKB hI hK hgap) rfl
      have he : H.Edge (x A) q.first := by
        rw [hqfirst]
        exact hedges A J (Nat.le_refl _) hAJ hJB hA hJ hnext
      refine ⟨q.prepend (x A) he, Path.prepend_first _ _ _,
        (Path.prepend_last _ _ _).trans hqlast, ?_, ?_⟩
      · change q.length + 1 ≤ d
        omega
      · intro v
        rw [Path.contains_prepend_iff, hqvertices]
        constructor
        · rintro (rfl | ⟨I, hJI, hIB, hI, hi⟩)
          · exact ⟨A, Nat.le_refl _, hAB, hA, rfl⟩
          · exact ⟨I, by omega, hIB, hI, hi⟩
        · rintro ⟨I, hAI, hIB, hI, hi⟩
          by_cases hIA : I = A
          · subst I
            exact Or.inl hi.symm
          · right
            have hAIlt : A.val < I.val := by
              have hn : I.val ≠ A.val := fun hh => hIA (Fin.ext hh)
              omega
            have hJI : J.val ≤ I.val := by
              by_cases hh : J.val ≤ I.val
              · exact hh
              · exact False.elim (hnext I hAIlt (by omega) hI)
            exact ⟨I, hJI, hIB, hI, hi⟩

/-- The same compression with edges directed towards decreasing original
indices. The resulting path retains exactly the selected interval, in reverse. -/
theorem path_of_reverse_consecutive_indices {L : Nat} (x : Fin (L + 1) → V)
    (P : Fin (L + 1) → Prop) (A B : Fin (L + 1))
    (hAB : A.val ≤ B.val) (hA : P A) (hB : P B)
    (hedges : ∀ I J : Fin (L + 1), A.val ≤ I.val → I.val < J.val →
      J.val ≤ B.val → P I → P J →
      (∀ K : Fin (L + 1), I.val < K.val → K.val < J.val → ¬ P K) →
      H.Edge (x J) (x I)) :
    ∃ p : Path H, p.first = x B ∧ p.last = x A ∧ p.length ≤ B.val - A.val ∧
      ∀ v, p.Contains v ↔ ∃ I : Fin (L + 1),
        A.val ≤ I.val ∧ I.val ≤ B.val ∧ P I ∧ x I = v := by
  let rev (i : Fin (L + 1)) : Fin (L + 1) := ⟨L - i.val, by omega⟩
  have hrev (i : Fin (L + 1)) : rev (rev i) = i := by
    apply Fin.ext
    dsimp only [rev]
    omega
  have hrevAB : (rev B).val ≤ (rev A).val := by dsimp only [rev]; omega
  have hrevA : P (rev (rev B)) := by rw [hrev]; exact hB
  have hrevB : P (rev (rev A)) := by rw [hrev]; exact hA
  have hrevedges : ∀ I J : Fin (L + 1), (rev B).val ≤ I.val → I.val < J.val →
      J.val ≤ (rev A).val → P (rev I) → P (rev J) →
      (∀ K : Fin (L + 1), I.val < K.val → K.val < J.val → ¬ P (rev K)) →
      H.Edge (x (rev I)) (x (rev J)) := by
    intro I J hBI hIJ hJA hI hJ hgap
    have hBI' : L - B.val ≤ I.val := hBI
    have hJA' : J.val ≤ L - A.val := hJA
    apply hedges (rev J) (rev I)
    · dsimp only [rev]; omega
    · dsimp only [rev]; omega
    · dsimp only [rev]; omega
    · exact hJ
    · exact hI
    · intro K hJK hKI hK
      have hJK' : L - J.val < K.val := hJK
      have hKI' : K.val < L - I.val := hKI
      apply hgap (rev K)
      · dsimp only [rev]; omega
      · dsimp only [rev]; omega
      · rwa [hrev]
  obtain ⟨p, hpfirst, hplast, hplen, hpvertices⟩ :=
    path_of_consecutive_indices (fun i => x (rev i)) (fun i => P (rev i))
      (rev B) (rev A) hrevAB hrevA hrevB hrevedges
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · simpa only [hrev] using hpfirst
  · simpa only [hrev] using hplast
  · have hl : p.length ≤ (L - A.val) - (L - B.val) := hplen
    omega
  · intro v
    rw [hpvertices]
    constructor
    · rintro ⟨I, hBI, hIA, hI, hi⟩
      have hBI' : L - B.val ≤ I.val := hBI
      have hIA' : I.val ≤ L - A.val := hIA
      exact ⟨rev I, by dsimp only [rev]; omega,
        by dsimp only [rev]; omega, hI, hi⟩
    · rintro ⟨I, hAI, hIB, hI, hi⟩
      refine ⟨rev I, ?_, ?_, ?_, ?_⟩
      · dsimp only [rev]; omega
      · dsimp only [rev]; omega
      · rwa [hrev]
      · rwa [hrev]

end MaximumMatching.DDFS
