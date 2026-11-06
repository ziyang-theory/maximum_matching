import MaximumMatching.BlossomLaminar

/-! Coverage by a unique boundary blossom from a proved base-existence
hypothesis below a specified cutoff. The premise is explicit: this is an
induction assembly lemma, not unconditional general base existence. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- If all vertices at or below an odd threshold have actual common bases,
following those bases terminates at a vertex above that threshold. The source
blossom contains the original vertex. Strictly decreasing minimum levels prove
termination even on an infinite vertex type. -/
theorem blossom_cover_of_base_existence (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b)
    (v : V) (s : Nat) (hvs : tenacity M v = some s) (hst : s ≤ t) :
    ∃ b, levelLT (some t) (tenacity M b) ∧ Blossom M t b v := by
  have aux : ∀ k (v : V) (s : Nat), minlevel M v = some k →
      tenacity M v = some s → s ≤ t →
      ∃ b, levelLT (some t) (tenacity M b) ∧ Blossom M t b v := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro v s hvk hvs hst
      obtain ⟨w, hvw⟩ := hexists v s hvs hst
      have hdirect : Blossom M t w v := blossom_of_base_le t ht w v hvw (by
        rw [hvs]; exact hst)
      cases hw : tenacity M w with
      | none => exact ⟨w, by simp only [hw, levelLT], hdirect⟩
      | some r =>
        by_cases hhigh : t < r
        · exact ⟨w, by simpa only [hw, levelLT] using hhigh, hdirect⟩
        · obtain ⟨j, hwj, hjk⟩ := hvw.minlevel_lt k hvk
          obtain ⟨b, hb, hwb⟩ := ih j hjk w r hwj hw (by omega)
          exact ⟨b, hb, blossom_downward_closed t ht b w v hwb hvw⟩
  obtain ⟨e, o, he, ho, _, _, _⟩ := finite_levels_of_tenacity v s hvs
  exact aux (min e o) v s (by simp only [minlevel, he, ho, levelMin]) hvs hst

/-- The boundary blossom supplied by coverage is unique, by the independently
proved cut/recursive-blossom laminarity theorem at a fixed threshold. -/
theorem unique_blossom_cover_of_base_existence (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b)
    (v : V) (s : Nat) (hvs : tenacity M v = some s) (hst : s ≤ t) :
    ∃ b, levelLT (some t) (tenacity M b) ∧ Blossom M t b v ∧
      ∀ c, levelLT (some t) (tenacity M c) → Blossom M t c v → c = b := by
  obtain ⟨b, hb, hvb⟩ := blossom_cover_of_base_existence t ht hexists v s hvs hst
  refine ⟨b, hb, hvb, ?_⟩
  intro c hc hvc
  apply Classical.byContradiction
  intro hne
  exact blossoms_disjoint_same_tenacity t c b hc hb hne v ⟨hvc, hvb⟩

end MaximumMatching
