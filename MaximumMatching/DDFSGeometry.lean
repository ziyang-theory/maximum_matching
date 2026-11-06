import MaximumMatching.DDFSPaths
import MaximumMatching.Foundations

section DDFSCut

/-! Sound terminal cut conditions for operational DDFS. These conditions are
proved sufficient below; no theorem here assumes that a DFS run establishes
them. DDFSInvariant separately derives closure at double exhaustion for
reachable states of the concrete stack transition system. -/
namespace MaximumMatching.DDFS
variable {V : Type} {H : LayeredGraph V}

/-- Every outgoing edge of the searched region is covered, except at the
candidate bottleneck whose outgoing edges are deliberately not searched. -/
def ClosedExcept (S : V → Prop) (b : V) : Prop :=
  ∀ u v, S u → u ≠ b → H.Edge u v → S v

/-- An avoided boundary cannot be escaped from a successor-closed region. -/
theorem Path.stays_in_closed_except (p : Path H) (S : V → Prop) (b : V)
    (hclosed : ClosedExcept (H := H) S b) (hfirst : S p.first)
    (havoid : ¬ p.Contains b) : ∀ i, S (p.vertex i) := by
  have aux : ∀ k (hk : k < p.length + 1), S (p.vertex ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero => intro hk; exact hfirst
    | succ k ih =>
      intro hk
      exact hclosed _ _ (ih (by omega))
        (fun he => havoid ⟨⟨k, by omega⟩, he⟩)
        (p.adjacent ⟨k, by omega⟩)
  intro i
  exact aux i.val i.isLt

/-- Coverage and absence of an alternative bottom vertex prove that the
candidate is a bottleneck. This is the exact universal-path consequence of
the closed-region invariant required at double exhaustion. -/
theorem bottleneck_of_closed_region (r g b : V) (S : V → Prop)
    (hr : S r) (hg : S g) (hclosed : ClosedExcept (H := H) S b)
    (hbottom : ∀ v, S v → H.level v = 0 → v = b) : Bottleneck H r g b := by
  intro p hp
  apply Classical.byContradiction
  intro havoid
  have hfirst : S p.first := by
    rcases hp with hp | hp
    · exact hp.1 ▸ hr
    · exact hp.1 ▸ hg
  have hall := p.stays_in_closed_except S b hclosed hfirst havoid
  have hzero : H.level p.last = 0 := hp.elim (fun h => h.2) (fun h => h.2)
  have hlast : p.last = b := hbottom p.last (hall ⟨p.length, by omega⟩) hzero
  exact havoid (hlast ▸ p.contains_last)

/-- Two active root-to-boundary paths with only their terminal vertex in common
certify highestness once coverage has established the bottleneck property. -/
theorem highestBottleneck_of_paths (r g b : V)
    (hb : Bottleneck H r g b) (hz : ∃ z : Path H, z.ToBottom b)
    (p q : Path H) (hpr : p.first = r) (hpb : p.last = b)
    (hqg : q.first = g) (hqb : q.last = b)
    (hmeet : ∀ v, p.Contains v → q.Contains v → v = b) :
    HighestBottleneck H r g b := by
  obtain ⟨z, hzb, hz0⟩ := hz
  refine ⟨hb, ?_⟩
  intro c hc
  have hpz : (p.append z (hpb.trans hzb.symm)).ToBottom r :=
    ⟨(p.append_first z _).trans hpr, by rw [p.append_last]; exact hz0⟩
  have hqz : (q.append z (hqb.trans hzb.symm)).ToBottom g :=
    ⟨(q.append_first z _).trans hqg, by rw [q.append_last]; exact hz0⟩
  have hcp := (Path.contains_append_iff p z _ c).1 (hc _ (Or.inl hpz))
  have hcq := (Path.contains_append_iff q z _ c).1 (hc _ (Or.inr hqz))
  rcases hcp with hcp | hcz
  · rcases hcq with hcq | hcz
    · rw [hmeet c hcp hcq]
      exact Nat.le_refl _
    · simpa only [hzb] using z.level_le_first hcz
  · simpa only [hzb] using z.level_le_first hcz

/-- A closed searched region and the two separated active chains are sufficient
terminal certificates for the highest-bottleneck outcome. -/
theorem highestBottleneck_of_closed_region (r g b : V) (S : V → Prop)
    (hr : S r) (hg : S g) (hclosed : ClosedExcept (H := H) S b)
    (hbottom : ∀ v, S v → H.level v = 0 → v = b)
    (hz : ∃ z : Path H, z.ToBottom b)
    (p q : Path H) (hpr : p.first = r) (hpb : p.last = b)
    (hqg : q.first = g) (hqb : q.last = b)
    (hmeet : ∀ v, p.Contains v → q.Contains v → v = b) :
    HighestBottleneck H r g b :=
  highestBottleneck_of_paths r g b (bottleneck_of_closed_region r g b S hr hg hclosed hbottom)
    hz p q hpr hpb hqg hqb hmeet

/-- Equal roots are an immediate highest-bottleneck outcome; no edge scan or
collision-recovery attempt is needed. Reachability prevents vacuity. -/
theorem highestBottleneck_same_root (r : V) (hr : ∃ p : Path H, p.ToBottom r) :
    HighestBottleneck H r r r := by
  refine ⟨?_, ?_⟩
  · intro p hp
    have he : p.first = r := hp.elim (fun h => h.1) (fun h => h.1)
    exact he ▸ p.contains_first
  · intro c hc
    obtain ⟨p, hp⟩ := hr
    simpa only [hp.1] using p.level_le_first (hc p (Or.inl hp))

end MaximumMatching.DDFS

end DDFSCut

section DDFSAltPath

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

end DDFSAltPath

section DDFSPathCompression

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

end DDFSPathCompression

section DDFSPathMap

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

end DDFSPathMap

section DDFSCertificate

/-! A two-path/dominator theorem for strictly layered directed graphs, proved by
induction on root layers. It is independent of an operational DDFS implementation. -/
namespace MaximumMatching.DDFS
variable {V : Type} (H : LayeredGraph V)

def Reaches (T : V → Prop) (r : V) : Prop := ∃ p : Path H, p.To T r

def Dominates (T : V → Prop) (r b : V) : Prop :=
  ∀ p : Path H, p.To T r → p.Contains b

def CommonDominator (T : V → Prop) (r g b : V) : Prop :=
  Dominates H T r b ∧ Dominates H T g b

def DisjointTo (T : V → Prop) (r g : V) : Prop :=
  ∃ p q : Path H, p.To T r ∧ q.To T g ∧ p.Disjoint q

theorem dominates_trans (T : V → Prop) (r c b : V)
    (hc : Dominates H T r c) (hb : Dominates H T c b) : Dominates H T r b := by
  intro p hp
  obtain ⟨i, hi⟩ := hc p hp
  have htail : (p.drop i.val (by omega)).To T c := by
    refine ⟨?_, ?_⟩
    · simpa using hi
    · simpa using hp.2
  exact p.contains_drop i.val (by omega) (hb _ htail)

/-- Dominators of one root are ordered by their layers: a lower one also
dominates every terminal continuation from a higher one. -/
theorem dominates_below (T : V → Prop) (g b c : V)
    (hg : Reaches H T g) (hb : Dominates H T g b) (hc : Dominates H T g c)
    (hl : H.level b ≤ H.level c) : Dominates H T c b := by
  obtain ⟨s, hs⟩ := hg
  obtain ⟨i, hi⟩ := hc s hs
  intro q hq
  let a := s.take i.val (by omega)
  have hj : a.last = q.first := by
    change s.vertex ⟨i.val, by omega⟩ = q.first
    rw [hi, hq.1]
  have hall : (a.append q hj).To T g := by
    exact ⟨by simpa [a] using hs.1, by simpa using hq.2⟩
  have hhit := (a.contains_append_iff q hj b).1 (hb _ hall)
  rcases hhit with ha | hqb
  · have hcl : H.level c ≤ H.level b := by
      have h := a.last_level_le ha
      simpa only [hj, hq.1] using h
    have hbc : b = c := by
      have h := a.eq_of_contains_level_eq ha a.contains_last (by rw [hj, hq.1]; omega)
      simpa only [hj, hq.1] using h
    rw [hbc, ← hq.1]
    exact q.contains_first
  · exact hqb

theorem disjointTo_symm (T : V → Prop) (r g : V) :
    DisjointTo H T r g → DisjointTo H T g r := by
  rintro ⟨p, q, hp, hq, hd⟩
  exact ⟨q, p, hq, hp, Path.disjoint_symm hd⟩

private theorem exists_minimum (P : Nat → Prop) (hex : ∃ k, P k) :
    ∃ k, P k ∧ ∀ j, P j → k ≤ j := by
  classical
  obtain ⟨k, hk⟩ := hex
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases h : ∃ j, j < k ∧ P j
    · obtain ⟨j, hj, hp⟩ := h
      exact ih j hj hp
    · exact ⟨k, hk, fun j hp => Nat.le_of_not_lt (fun hj => h ⟨j, hj, hp⟩)⟩

/-- Two reachable roots admit disjoint terminal paths, or all such paths from
both roots contain a common vertex. No Menger theorem is assumed. -/
theorem two_path_dichotomy (T : V → Prop) (r g : V)
    (hr : Reaches H T r) (hg : Reaches H T g) :
    DisjointTo H T r g ∨ ∃ b, CommonDominator H T r g b := by
  classical
  have aux : ∀ n : Nat, ∀ r g : V, H.level r + H.level g = n →
      Reaches H T r → Reaches H T g →
      DisjointTo H T r g ∨ ∃ b, CommonDominator H T r g b := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      have ordered (r g : V) (hsum : H.level r + H.level g = n)
          (hle : H.level g ≤ H.level r) (hr : Reaches H T r) (hg : Reaches H T g) :
          DisjointTo H T r g ∨ ∃ b, CommonDominator H T r g b := by
        by_cases heq : r = g
        · right
          refine ⟨r, ?_, ?_⟩
          · intro p hp; rw [← hp.1]; exact p.contains_first
          · intro p hp; rw [heq, ← hp.1]; exact p.contains_first
        have hnot (q : Path H) (hq : q.To T g) : ¬ q.Contains r := by
          intro hqr
          have hrg := q.contains_eq_first_of_level_ge hqr (by rw [hq.1]; exact hle)
          exact heq (hrg.trans hq.1)
        by_cases hrt : T r
        · left
          obtain ⟨q, hq⟩ := hg
          refine ⟨Path.trivial H r, q, ⟨rfl, hrt⟩, hq, ?_⟩
          intro v hv hqv
          obtain ⟨i, hi⟩ := hv
          have hrv : r = v := hi
          apply hnot q hq
          rw [hrv]
          exact hqv
        by_cases hdis : DisjointTo H T r g
        · exact Or.inl hdis
        have hsucc : ∀ x, H.Edge r x → Reaches H T x →
            ∃ b, CommonDominator H T x g b := by
          intro x hex hx
          have hdecr := H.decreases hex
          rcases ih (H.level x + H.level g) (by omega) x g rfl hx hg with hd | hb
          · obtain ⟨p, q, hp, hq, hpq⟩ := hd
            have he : H.Edge r p.first := by rw [hp.1]; exact hex
            apply False.elim
            apply hdis
            refine ⟨Path.prepend r p he, q, ⟨rfl, by simpa using hp.2⟩, hq, ?_⟩
            intro v hv hqv
            rcases (Path.contains_prepend_iff r p he v).1 hv with hv | hv
            · subst v; exact hnot q hq hqv
            · exact hpq v hv hqv
          · exact hb
        have hexist : ∃ k, ∃ b, H.level b = k ∧ ∃ x,
            H.Edge r x ∧ Reaches H T x ∧ CommonDominator H T x g b := by
          obtain ⟨p, hp⟩ := hr
          have hpos : 0 < p.length := by
            by_cases hz : p.length = 0
            · have he : p.first = p.last := congrArg p.vertex (Fin.ext (by omega))
              exact False.elim (hrt (by rw [← hp.1, he]; exact hp.2))
            · omega
          let x := p.vertex ⟨1, by omega⟩
          have hx : Reaches H T x := ⟨p.drop 1 (by omega), by simp [Path.To, x, hp.2]⟩
          have he : H.Edge r x := by
            have h := p.adjacent ⟨0, hpos⟩
            change H.Edge p.first x at h
            rwa [hp.1] at h
          obtain ⟨b, hb⟩ := hsucc x he hx
          exact ⟨H.level b, b, rfl, x, he, hx, hb⟩
        obtain ⟨k, ⟨b, hbk, x, hex, hx, hxb⟩, hmin⟩ := exists_minimum _ hexist
        right
        refine ⟨b, ?_, hxb.2⟩
        intro p hp
        have hpos : 0 < p.length := by
          by_cases hz : p.length = 0
          · have he : p.first = p.last := congrArg p.vertex (Fin.ext (by omega))
            exact False.elim (hrt (by rw [← hp.1, he]; exact hp.2))
          · omega
        let y := p.vertex ⟨1, by omega⟩
        have hy : Reaches H T y := ⟨p.drop 1 (by omega), by simp [Path.To, y, hp.2]⟩
        have he : H.Edge r y := by
          have h := p.adjacent ⟨0, hpos⟩
          change H.Edge p.first y at h
          rwa [hp.1] at h
        obtain ⟨c, hc⟩ := hsucc y he hy
        have hbc : H.level b ≤ H.level c := by
          rw [hbk]
          exact hmin (H.level c) ⟨c, rfl, y, he, hy, hc⟩
        have hcb := dominates_below H T g b c hg hxb.2 hc.2 hbc
        have hyb := dominates_trans H T y c b hc.1 hcb
        exact p.contains_drop 1 (by omega) (hyb _ (by simp [Path.To, y, hp.2]))
      intro r g hsum hr hg
      by_cases hle : H.level g ≤ H.level r
      · exact ordered r g hsum hle hr hg
      · rcases ordered g r (by omega) (by omega) hg hr with hd | ⟨b, hb⟩
        · exact Or.inl (disjointTo_symm H T g r hd)
        · exact Or.inr ⟨b, hb.2, hb.1⟩
  exact aux (H.level r + H.level g) r g rfl hr hg

/-- The graph-theoretic two outcomes of DDFS, without any operational machine
premise: either disjoint root-to-bottom paths or a highest bottleneck. -/
theorem bottom_dichotomy (r g : V)
    (hr : ∃ p : Path H, p.ToBottom r) (hg : ∃ q : Path H, q.ToBottom g) :
    (∃ p q : Path H, p.ToBottom r ∧ q.ToBottom g ∧ p.Disjoint q) ∨
      ∃ b, HighestBottleneck H r g b := by
  rcases two_path_dichotomy H (fun v => H.level v = 0) r g hr hg with hd | ⟨b, hb⟩
  · exact Or.inl hd
  · right
    apply highestBottleneck_exists H r g hr
    refine ⟨b, ?_⟩
    intro p hp
    rcases hp with hp | hp
    · exact hb.1 p hp
    · exact hb.2 p hp

/-- Two vertex-disjoint directed paths, with specified roots and endpoints. -/
def Linkage (r g a b : V) : Prop :=
  ∃ p q : Path H, p.first = r ∧ p.last = a ∧
    q.first = g ∧ q.last = b ∧ p.Disjoint q

/-- The per-vertex certificate above a highest bottleneck. A vertex `w` reachable
from either root and strictly above `b` can be linked to one root while the other
root is linked disjointly to `b`. The orientation may depend on `w`.

This proves the existence used in Lemma 6.13 Claim 4; it does not assert that an
operational DDFS machine computes a globally consistent coloring or search trees. -/
theorem highestBottleneck_certificate (r g b w : V)
    (hr : ∃ p : Path H, p.ToBottom r) (hg : ∃ q : Path H, q.ToBottom g)
    (hb : HighestBottleneck H r g b) (hw : H.level b < H.level w)
    (a : Path H) (ha : a.first = r ∨ a.first = g) (haw : a.last = w) :
    Linkage H r g w b ∨ Linkage H g r w b := by
  let T : V → Prop := fun v => v = w ∨ v = b
  have reachesT (u : V) (hu : u = r ∨ u = g)
      (hre : ∃ p : Path H, p.ToBottom u) : Reaches H T u := by
    obtain ⟨p, hp⟩ := hre
    have hpRG : p.ToBottom r ∨ p.ToBottom g := by
      rcases hu with rfl | rfl
      · exact Or.inl hp
      · exact Or.inr hp
    obtain ⟨i, hi⟩ := hb.1 p hpRG
    refine ⟨p.take i.val (by omega), ?_, ?_⟩
    · simpa using hp.1
    · exact Or.inr (by simpa using hi)
  have hrT := reachesT r (Or.inl rfl) hr
  have hgT := reachesT g (Or.inr rfl) hg
  rcases two_path_dichotomy H T r g hrT hgT with hd | ⟨c, hc⟩
  · obtain ⟨p, q, hp, hq, hpq⟩ := hd
    have hend := disjoint_paths_distinct_bottoms H p q hpq
    rcases hp.2 with hpw | hpb
    · rcases hq.2 with hqw | hqb
      · exact False.elim (hend (hpw.trans hqw.symm))
      · exact Or.inl ⟨p, q, hp.1, hpw, hq.1, hqb, hpq⟩
    · rcases hq.2 with hqw | hqb
      · exact Or.inr ⟨q, p, hq.1, hqw, hp.1, hpb, Path.disjoint_symm hpq⟩
      · exact False.elim (hend (hpb.trans hqb.symm))
  · have hcb : Bottleneck H r g c := by
      intro p hp
      obtain ⟨i, hi⟩ := hb.1 p hp
      let q := p.take i.val (by omega)
      have hqt : T q.last := Or.inr (by simpa [q] using hi)
      have hhit : q.Contains c := by
        rcases hp with hp | hp
        · exact hc.1 q ⟨by simpa [q] using hp.1, hqt⟩
        · exact hc.2 q ⟨by simpa [q] using hp.1, hqt⟩
      exact p.contains_take i.val (by omega) hhit
    have hcbelow := hb.2 c hcb
    have hca : a.Contains c := by
      rcases ha with har | hag
      · exact hc.1 a ⟨har, Or.inl haw⟩
      · exact hc.2 a ⟨hag, Or.inl haw⟩
    have hwbelow := a.last_level_le hca
    rw [haw] at hwbelow
    omega

end MaximumMatching.DDFS

end DDFSCertificate

section BridgePath

namespace MaximumMatching
namespace DDFS
variable {V : Type} {G : Graph V} {M : Matching G} {H : LayeredGraph V}

/-- Unit layer drops identify the layer of each path vertex. -/
theorem Path.level_add_index (q : Path H)
    (hstep : ∀ {u v}, H.Edge u v → H.level u = H.level v + 1)
    (i : Fin (q.length + 1)) :
    H.level (q.vertex i) + i.val = H.level q.first := by
  have aux : ∀ k (hk : k < q.length + 1),
      H.level (q.vertex ⟨k, hk⟩) + k = H.level q.first := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hs := hstep (q.adjacent ⟨k, by omega⟩)
      dsimp only at hprev hs
      omega
  exact aux i.val i.isLt

/-- Extend an alternating path down a disjoint layered suffix. The layer parity
is reversed after crossing the horizontal bridge. -/
def appendDown (q : Path H) (p : AltPath M)
    (hedge : ∀ {u v}, H.Edge u v → G.Adj u v)
    (hstep : ∀ {u v}, H.Edge u v → H.level u = H.level v + 1)
    (hmatch : ∀ {u v}, H.Edge u v → ((M.mate v = some u) ↔ H.level v % 2 = 1))
    (hjoin : p.last = q.first)
    (hshift : p.length % 2 = (H.level q.first + 1) % 2)
    (hdisj : ∀ (i : Fin (p.length + 1)) (j : Fin (q.length + 1)),
      0 < j.val → p.vertex i ≠ q.vertex j) : AltPath M where
  length := p.length + q.length
  vertex := fun i => if hi : i.val ≤ p.length then p.vertex ⟨i.val, by omega⟩
    else q.vertex ⟨i.val - p.length, by omega⟩
  injective := by
    intro i j he
    split at he <;> split at he
    · have hi := p.injective _ _ he
      apply Fin.ext
      exact congrArg (fun x : Fin (p.length + 1) => x.val) hi
    · exact False.elim (hdisj _ _ (by change 0 < j.val - p.length; omega) he)
    · exact False.elim (hdisj _ _ (by change 0 < i.val - p.length; omega) he.symm)
    · have hi := q.injective _ _ he
      have hi' := congrArg Fin.val hi
      dsimp only at hi'
      apply Fin.ext
      omega
  adjacent := by
    intro i
    by_cases hi : i.val < p.length
    · simpa only [dite_eq_left (show i.val ≤ p.length by omega),
        dite_eq_left (show i.val + 1 ≤ p.length by omega)] using p.adjacent ⟨i.val, hi⟩
    · by_cases he : i.val = p.length
      · simp only [he, Nat.le_refl, dite_true,
          show ¬ p.length + 1 ≤ p.length by omega, dite_false]
        change G.Adj p.last _
        rw [hjoin]
        simpa only [Path.first, Nat.zero_add, show p.length + 1 - p.length = 1 by omega] using
          hedge (q.adjacent ⟨0, by omega⟩)
      · simp only [dite_eq_right (show ¬ i.val ≤ p.length by omega),
          dite_eq_right (show ¬ i.val + 1 ≤ p.length by omega)]
        simpa only [show i.val + 1 - p.length = (i.val - p.length) + 1 by omega] using
          hedge (q.adjacent ⟨i.val - p.length, by omega⟩)
  start_free := by simpa using p.start_free
  alternating := by
    intro i
    by_cases hi : i.val < p.length
    · simpa only [dite_eq_left (show i.val ≤ p.length by omega),
        dite_eq_left (show i.val + 1 ≤ p.length by omega)] using p.alternating ⟨i.val, hi⟩
    · have hbound : i.val - p.length < q.length := by omega
      have hs := hmatch (q.adjacent ⟨i.val - p.length, hbound⟩)
      have hl := q.level_add_index hstep ⟨i.val - p.length + 1, by omega⟩
      dsimp only at hl hs
      have hpar : H.level (q.vertex ⟨i.val - p.length + 1, by omega⟩) % 2 = i.val % 2 := by
        omega
      have hmat : (M.mate (q.vertex ⟨i.val - p.length, by omega⟩) =
          some (q.vertex ⟨i.val - p.length + 1, by omega⟩)) ↔ i.val % 2 = 1 := by
        constructor
        · intro hm
          rw [← hpar]
          exact hs.1 (M.symm hm)
        · intro hp
          exact M.symm (hs.2 (hpar.trans hp))
      by_cases he : i.val = p.length
      · simp only [he, Nat.le_refl, dite_true,
          show ¬ p.length + 1 ≤ p.length by omega, dite_false]
        change (M.mate p.last = some _) ↔ p.length % 2 = 1
        rw [hjoin]
        simpa only [Path.first, he, Nat.sub_self, Nat.zero_add, show p.length + 1 - p.length = 1 by omega] using hmat
      · simp only [dite_eq_right (show ¬ i.val ≤ p.length by omega),
          dite_eq_right (show ¬ i.val + 1 ≤ p.length by omega)]
        simpa only [show i.val + 1 - p.length = (i.val - p.length) + 1 by omega] using hmat

@[simp] theorem appendDown_length (q : Path H) (p : AltPath M)
    (hedge) (hstep) (hmatch) (hjoin) (hshift) (hdisj) :
    (appendDown q p hedge hstep hmatch hjoin hshift hdisj).length = p.length + q.length := rfl

@[simp] theorem appendDown_first (q : Path H) (p : AltPath M)
    (hedge) (hstep) (hmatch) (hjoin) (hshift) (hdisj) :
    (appendDown q p hedge hstep hmatch hjoin hshift hdisj).first = p.first := by
  simp only [AltPath.first, appendDown, Nat.zero_le, dite_true]

@[simp] theorem appendDown_last (q : Path H) (p : AltPath M)
    (hedge) (hstep) (hmatch) (hjoin) (hshift) (hdisj) :
    (appendDown q p hedge hstep hmatch hjoin hshift hdisj).last = q.last := by
  simp only [AltPath.last, appendDown]
  split
  next h =>
    have hzero : q.length = 0 := by omega
    have hlen : p.length + q.length = p.length := by omega
    simp only [hlen]
    change p.last = q.last
    rw [hjoin]
    exact congrArg q.vertex (Fin.ext (by exact hzero.symm))
  next h => congr 1; apply Fin.ext; change p.length + q.length - p.length = q.length; omega

/-- The bridge detour used by Claim 4 on p.25: lift the path from the
opposite bridge endpoint to the bottleneck, cross the bridge, and descend to
`w`. Layer separation and the DDFS certificate prove simplicity. -/
theorem bridge_detour (compat : LayeredMatching M H)
    (r g b w : V) (α : Nat)
    (hr : H.level r = α) (hg : H.level g = α)
    (hbridge : G.Adj g r) (hbridge_match : (M.mate g = some r) ↔ α % 2 = 1)
    (a q : Path H) (ha : a.first = r) (haw : a.last = w)
    (hq : q.first = g) (hqb : q.last = b) (hdisj : a.Disjoint q)
    (hw : H.level b < H.level w)
    (p : AltPath M) (hp : p.last = b)
    (hlevels : ∀ i, H.level (p.vertex i) = i.val) :
    ∃ z : AltPath M, z.first = p.first ∧ z.last = w ∧
      z.length = 2 * α + 1 - H.level w := by
  obtain ⟨s, hsfirst, hslast, hslen, _, hsmem⟩ := lift_path compat q p
    (hp.trans hqb.symm) hlevels
  have hplen : H.level b = p.length := by
    have hh : H.level p.last = p.length := hlevels ⟨p.length, by omega⟩
    simpa only [hp] using hh
  have hsavoid : ∀ (i : Fin (s.length + 1)) (j : Fin (a.length + 1)),
      s.vertex i ≠ a.vertex j := by
    intro i j he
    have hm := (hsmem (s.vertex i)).1 ⟨i, rfl⟩
    rcases hm with ⟨k, hk⟩ | hqmem
    · have hlow := hlevels k
      have hhigh := a.last_level_le (show a.Contains (a.vertex j) from ⟨j, rfl⟩)
      rw [haw] at hhigh
      rw [hk, he] at hlow
      omega
    · exact hdisj (a.vertex j) ⟨j, rfl⟩ (he ▸ hqmem)
  have hsr : ∀ i, s.vertex i ≠ r := by
    intro i
    simpa only [← ha, Path.first] using hsavoid i ⟨0, by omega⟩
  have hsg : s.last = g := hslast.trans hq
  have hsα : s.length = α := hslen.trans (by rw [hq, hg])
  have hedge : G.Adj s.last r := hsg ▸ hbridge
  have hpar : (M.mate s.last = some r) ↔ s.length % 2 = 1 := by
    simpa only [hsg, hsα] using hbridge_match
  let t := s.append r hsr hedge hpar
  have htlast : t.last = a.first := (s.append_last r hsr hedge hpar).trans ha.symm
  have htshift : t.length % 2 = (H.level a.first + 1) % 2 := by
    change (s.length + 1) % 2 = _
    rw [hsα, ha, hr]
  have htavoid : ∀ (i : Fin (t.length + 1)) (j : Fin (a.length + 1)),
      0 < j.val → t.vertex i ≠ a.vertex j := by
    intro i j hj he
    change (if hi : i.val ≤ s.length then s.vertex ⟨i.val, by omega⟩ else r) = a.vertex j at he
    split at he
    · exact hsavoid _ j he
    · have ha0 : a.vertex ⟨0, by omega⟩ = r := ha
      have hh := a.injective _ j (ha0.trans he)
      have hv : 0 = j.val := congrArg (fun x : Fin (a.length + 1) => x.val) hh
      omega
  let z := appendDown a t compat.adjacent compat.consecutive compat.alternating
    htlast htshift htavoid
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [appendDown_first]
    change (if h : 0 ≤ s.length then s.vertex ⟨0, by omega⟩ else r) = p.first
    simpa only [AltPath.first, Nat.zero_le, dite_true] using hsfirst
  · exact (appendDown_last a t compat.adjacent compat.consecutive compat.alternating
      htlast htshift htavoid).trans haw
  · have hal := a.level_add_index compat.consecutive ⟨a.length, by omega⟩
    change H.level a.last + a.length = H.level a.first at hal
    rw [haw, ha, hr] at hal
    change s.length + 1 + a.length = _
    omega

end DDFS
end MaximumMatching

end BridgePath
