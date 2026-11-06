import MaximumMatching.BlockingBucketRemoval

/-! The invariant returned by a continued blocking-bucket scan. All returned
paths have the original matching and level. Surviving bottom arms transport
through the same contractions and recursive removals used by the execution. -/
namespace MaximumMatching.Search
variable {n i cut : Nat} {G : Graph (Fin n)} {M : Matching G}

structure BlockingBucketResult (S : ActiveSearchState M i cut)
    (es : List (Fin n × Fin n)) where
  state : ActiveSearchState M i cut
  family : AugmentingFamily M
  monotone : S.Monotone state
  queued : ∀ u v t, (u, v) ∈ S.B.state.bucket t → (u, v) ∈ state.B.state.bucket t
  accounted : ∀ e, e ∈ es → state.Accounted e.1 e.2
  lengths : ∀ j, (family.path j).length = 2 * i + 1
  live : ∀ j k, S.B.forest.root ((family.path j).vertex k) ∈ S.live
  inactive : ∀ j k, state.B.forest.root ((family.path j).vertex k) ∉ state.live
  survives : ∀ q : AltPath M, (∀ j, (family.path j).Disjoint q) →
    ∀ u v, S.LiveBridgeArms u v (fun w => ∃ k, q.vertex k = w) →
      state.LiveBridgeArms u v (fun w => ∃ k, q.vertex k = w)

namespace BlockingBucketResult

/-- The completed scan has no remaining trigger and adds no path. -/
def done (S : ActiveSearchState M i cut) : BlockingBucketResult S [] where
  state := S
  family := .empty
  monotone := .refl S
  queued _ _ _ h := h
  accounted _ h := False.elim (List.not_mem_nil h)
  lengths j := nomatch j
  live j := nomatch j
  inactive j := nomatch j
  survives _ _ _ _ h := h

/-- Record a discharged head trigger after the remaining scan has finished. -/
def account {S : ActiveSearchState M i cut} {e : Fin n × Fin n}
    {es : List (Fin n × Fin n)} (R : BlockingBucketResult S es)
    (ha : R.state.Accounted e.1 e.2) : BlockingBucketResult S (e :: es) where
  state := R.state
  family := R.family
  monotone := R.monotone
  queued := R.queued
  accounted f hf := by
    rcases List.mem_cons.mp hf with he | hf
    · cases he
      exact ha
    · exact R.accounted f hf
  lengths := R.lengths
  live := R.live
  inactive := R.inactive
  survives := R.survives

/-- A trigger already accounted in the input needs no DDFS operation. -/
def skip {S : ActiveSearchState M i cut} {e : Fin n × Fin n}
    {es : List (Fin n × Fin n)} (ha : S.Accounted e.1 e.2)
    (R : BlockingBucketResult S es) : BlockingBucketResult S (e :: es) where
  state := R.state
  family := R.family
  monotone := R.monotone
  queued := R.queued
  accounted f hf := by
    rcases List.mem_cons.mp hf with he | hf
    · cases he
      exact ha.mono R.monotone
    · exact R.accounted f hf
  lengths := R.lengths
  live := R.live
  inactive := R.inactive
  survives := R.survives

/-- Compose a live contraction with the rest of the actual scan. -/
def advance {S T : ActiveSearchState M i cut} {es : List (Fin n × Fin n)}
    (hmono : S.Monotone T)
    (hqueue : ∀ u v t, (u, v) ∈ S.B.state.bucket t → (u, v) ∈ T.B.state.bucket t)
    (htransport : ∀ q : AltPath M, ∀ u v,
      S.LiveBridgeArms u v (fun w => ∃ k, q.vertex k = w) →
      T.LiveBridgeArms u v (fun w => ∃ k, q.vertex k = w))
    (R : BlockingBucketResult T es) : BlockingBucketResult S es where
  state := R.state
  family := R.family
  monotone := hmono.trans R.monotone
  queued u v t h := R.queued u v t (hqueue u v t h)
  accounted := R.accounted
  lengths := R.lengths
  live j k := by
    by_cases hh : S.B.forest.root ((R.family.path j).vertex k) ∈ S.live
    · exact hh
    · exact False.elim (hmono.inactive _ hh (R.live j k))
  inactive := R.inactive
  survives q hd u v h := R.survives q hd u v (htransport q u v h)

/-- Add a recovered augmentation, remove its root classes, and continue on
that exact pruned state. Future paths are disjoint because their initial roots
remain live after this removal. -/
def prependRemoved (S : ActiveSearchState M i cut) (p : AltPath M)
    (hp : p.Augmenting) (hlen : p.length = 2 * i + 1)
    (hlive : ∀ j, S.B.forest.root (p.vertex j) ∈ S.live)
    (hclosed : ∀ j, ∃ k, p.vertex k = S.B.forest.root (p.vertex j))
    {es : List (Fin n × Fin n)} (R : BlockingBucketResult (S.remove (S.pathRoots p)) es) :
    BlockingBucketResult S es := by
  have hd : ∀ j, p.Disjoint (R.family.path j) := by
    intro j a b he
    have hh := (S.remove_live _ _ (R.live j b)).2
    apply hh
    exact (S.mem_pathRoots p _).2 ⟨a, congrArg S.B.forest.root he⟩
  let F := R.family.prepend p hp hd
  refine {
    state := R.state
    family := F
    monotone := (S.remove_monotone _).trans R.monotone
    queued := R.queued
    accounted := R.accounted
    lengths := ?_
    live := ?_
    inactive := ?_
    survives := ?_ }
  · intro j
    change (if h : j.val = 0 then p else R.family.path ⟨j.val - 1, _⟩).length = _
    split
    · exact hlen
    · exact R.lengths _
  · intro j
    by_cases hz : j.val = 0
    · have he : F.path j = p := dite_eq_left hz
      rw [he]
      exact hlive
    · have he : F.path j = R.family.path ⟨j.val - 1, by have := j.isLt; change j.val < R.family.count + 1 at this; omega⟩ := dite_eq_right hz
      rw [he]
      intro k
      exact (S.remove_live _ _ (R.live _ k)).1
  · intro j
    by_cases hz : j.val = 0
    · have he : F.path j = p := dite_eq_left hz
      rw [he]
      intro k
      exact R.monotone.inactive _ (S.pathRoots_inactive p k)
    · have he : F.path j = R.family.path ⟨j.val - 1, by have := j.isLt; change j.val < R.family.count + 1 at this; omega⟩ := dite_eq_right hz
      rw [he]
      exact R.inactive _
  · intro q hdis u v h
    have hpq : p.Disjoint q := hdis ⟨0, by change 0 < R.family.count + 1; omega⟩
    have hRq : ∀ j, (R.family.path j).Disjoint q := by
      intro j
      have hh := hdis ⟨j.val + 1, by change j.val + 1 < R.family.count + 1; omega⟩
      simpa only [F, AugmentingFamily.prepend, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, dite_false, Nat.add_sub_cancel, Fin.eta] using hh
    exact R.survives q hRq u v (h.remove_path hclosed hpq)

/-- Exhausting a complete trigger list yields a maximal family of shortest
augmentations: a disjoint shortest path would retain live disjoint arms at an
accounted trigger. -/
theorem maximalShortest {S : ActiveSearchState M i cut} {es : List (Fin n × Fin n)}
    (R : BlockingBucketResult S es) (htop : AtMostShortestAugmenting M (2 * i + 1))
    (hcover : ∀ p : AltPath M, p.Augmenting → p.length = 2 * i + 1 →
      ∃ u v, (u, v) ∈ es ∧ S.LiveBridgeArms u v (fun w => ∃ j, p.vertex j = w)) :
    R.family.MaximalShortest (2 * i + 1) := by
  refine ⟨htop, R.lengths, ?_⟩
  intro p hp hlen hd
  obtain ⟨u, v, he, ha⟩ := hcover p hp hlen
  obtain ⟨hu, hv, a, b, haf, hbf, hab, _⟩ := R.survives p hd u v ha
  exact (R.accounted (u, v) he).excludes_disjoint_arms hu hv a b haf.1 hbf.1 hab

end BlockingBucketResult
end MaximumMatching.Search
