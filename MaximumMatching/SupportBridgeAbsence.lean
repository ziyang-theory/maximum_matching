import MaximumMatching.GeneralBridge

namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A shortest path shorter than half a permitted odd threshold contains no
bridge of that threshold. Lower structural facts are discharged internally. -/
theorem short_shortest_no_current_bridge (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (ht : AtMostShortestAugmenting M t) (hodd : t % 2 = 1)
    (hshort : 2 * p.length < t) : p.NoBridgeOfTenacity t := by
  have hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b := by
    intro v s hs hst
    have helig : EligibleTenacity M s := by
      refine ⟨tenacity_odd M v s hs, ⟨v, ?_⟩, ?_⟩
      · rw [hs]; exact Nat.le_refl _
      · intro q hq; have := ht q hq; omega
    obtain ⟨b, hb, _⟩ := general_unique_base M s helig v hs
    exact ⟨b, s, hs, hb⟩
  apply short_shortest_no_bridge t hodd hexists ?_ p hp hshort
  intro b v hv hb q hq hqb hqv k
  obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound (t - 2) b v hv
  have hsodd := tenacity_odd M v s hs
  have helig : EligibleTenacity M (t - 2) := by
    refine ⟨by omega, ⟨v, ?_⟩, ?_⟩
    · rw [hs]; exact hst
    · intro r hr; have := ht r hr; omega
  exact general_blossom_relative_edge_bound M (t - 2) helig b v hv hb q hq hqb hqv k

end MaximumMatching.AltPath
