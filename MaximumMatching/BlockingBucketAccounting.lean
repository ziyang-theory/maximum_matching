import MaximumMatching.ActiveSearchGraph

/-! Trigger accounting for a deletion-aware blocking bucket. A processed
trigger either has one current bud or has lost an endpoint's live bud. Both
conditions persist through later live-only contractions and removals. -/
namespace MaximumMatching.Search.ActiveSearchState
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G} {i cut : Nat}

/-- A trigger no longer needs a distinct-live-root DDFS call. -/
def Accounted (S : ActiveSearchState M i cut) (u v : Fin n) : Prop :=
  S.B.forest.root u = S.B.forest.root v ∨
    S.B.forest.root u ∉ S.live ∨ S.B.forest.root v ∉ S.live

/-- Later operations do not split old classes or revive an inactive class.
The relation concerns original vertices, so a live contraction may change
which fixed root names a surviving class. -/
structure Monotone (S T : ActiveSearchState M i cut) : Prop where
  roots : ∀ u v, S.B.forest.root u = S.B.forest.root v →
    T.B.forest.root u = T.B.forest.root v
  inactive : ∀ v, S.B.forest.root v ∉ S.live → T.B.forest.root v ∉ T.live

namespace Monotone

theorem refl (S : ActiveSearchState M i cut) : Monotone S S :=
  ⟨fun _ _ h => h, fun _ h => h⟩

theorem trans {S T U : ActiveSearchState M i cut} (hST : Monotone S T)
    (hTU : Monotone T U) : Monotone S U :=
  ⟨fun u v h => hTU.roots u v (hST.roots u v h),
    fun v h => hTU.inactive v (hST.inactive v h)⟩

/-- Removing vertices while retaining the forest is monotone. -/
theorem of_live_subset {S T : ActiveSearchState M i cut}
    (hroot : ∀ v, T.B.forest.root v = S.B.forest.root v)
    (hsub : ∀ v, v ∈ T.live → v ∈ S.live) : Monotone S T := by
  constructor
  · intro u v h
    rw [hroot, hroot]
    exact h
  · intro v h hv
    apply h
    rw [hroot] at hv
    exact hsub _ hv

end Monotone

namespace Accounted

theorem symm {S : ActiveSearchState M i cut} {u v : Fin n}
    (h : S.Accounted u v) : S.Accounted v u := by
  rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem mono {S T : ActiveSearchState M i cut} (hST : Monotone S T)
    {u v : Fin n} (h : S.Accounted u v) : T.Accounted u v := by
  rcases h with h | h | h
  · exact Or.inl (hST.roots u v h)
  · exact Or.inr (Or.inl (hST.inactive u h))
  · exact Or.inr (Or.inr (hST.inactive v h))

/-- A surviving pair of disjoint live-root arms witnesses an unaccounted
trigger. This is the final contradiction used for maximality. -/
theorem excludes_disjoint_arms {S : ActiveSearchState M i cut} {u v : Fin n}
    (h : S.Accounted u v) (hu : S.B.forest.root u ∈ S.live)
    (hv : S.B.forest.root v ∈ S.live)
    (p q : DDFS.Path S.graph) (hp : p.first = S.B.forest.root u)
    (hq : q.first = S.B.forest.root v) (hd : p.Disjoint q) : False := by
  rcases h with he | he | he
  · have hh : p.first = q.first := hp.trans (he.trans hq.symm)
    exact hd p.first p.contains_first (hh ▸ q.contains_first)
  · exact he hu
  · exact he hv

end Accounted
end MaximumMatching.Search.ActiveSearchState
