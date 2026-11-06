import MaximumMatching.DDFSPaths

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
