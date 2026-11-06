import MaximumMatching.BlossomRelative
import MaximumMatching.BlossomCover

/-! Identify the blossom of an endpoint from the actual boundary on one
shortest path, once bases exist up to the cutoff. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

theorem blossom_of_shortest_base (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b)
    (b : V) (hb : p.BaseOnPath t b) (hv : levelLE (tenacity M p.last) (some t)) :
    Blossom M t b p.last := by
  have hfinite : ∃ s, tenacity M p.last = some s ∧ s ≤ t := by
    cases hs : tenacity M p.last with
    | none => simp only [hs, levelLE] at hv
    | some s => exact ⟨s, rfl, by simpa only [hs, levelLE] using hv⟩
  obtain ⟨s, hs, hst⟩ := hfinite
  obtain ⟨c, hc, hmem⟩ := blossom_cover_of_base_existence t ht hexists p.last s hs hst
  have hcb := p.baseOnPath_unique t c b (blossom_baseOnPath t c p.last hmem hc p rfl hp) hb
  exact hcb ▸ hmem

end MaximumMatching.AltPath
