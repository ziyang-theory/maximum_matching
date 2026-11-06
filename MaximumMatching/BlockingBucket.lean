import MaximumMatching.BlockingBucketResult
import MaximumMatching.ActivePetalState
import MaximumMatching.ActivePathRecovery

/-! The deletion-aware continuation of the current bridge bucket. Each live
trigger runs DDFS on the current restricted graph. A bottleneck updates MAX
and contracts that live petal; disjoint bottom arms recover an augmentation,
remove its root fibers, and recursively prune predecessors before the next
trigger. The matching and MIN labels are held fixed throughout this phase. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G} {i cut : Nat}
    [DecidableRel G.Adj]

/-- Scan the supplied current-level bridges once, continuing after every
recovered augmentation. The result carries the proved accounting and
surviving-path invariant of the actual computed execution. -/
def runBlockingBucket
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)
    (S : ActiveSearchState M i cut) (es : List (Fin n × Fin n))
    (hqueued : ∀ e, e ∈ es → e ∈ S.B.state.bucket (2 * i + 1)) :
    BlockingBucketResult S es :=
  match es with
  | [] => .done S
  | (u, v) :: rest =>
    have he := hqueued (u, v) List.mem_cons_self
    have hrest : ∀ e, e ∈ rest → e ∈ S.B.state.bucket (2 * i + 1) :=
      fun e h => hqueued e (List.mem_cons_of_mem (u, v) h)
    if hsame : S.B.forest.root u = S.B.forest.root v then
      (runBlockingBucket hc htop hstageTen S rest hrest).skip (Or.inl hsame)
    else if hu : S.B.forest.root u ∈ S.live then
      if hv : S.B.forest.root v ∈ S.live then
        match hout : DDFS.Machine.executeFull S.reach (S.B.forest.root u) (S.B.forest.root v) with
        | .disjoint p q hp hq hd =>
          let z := S.recoverLivePath htop hstageTen u v he hu hv p q hp hq hd
          let T := S.remove (S.pathRoots z.val)
          let result := runBlockingBucket hc htop hstageTen T rest hrest
          let recovered := BlockingBucketResult.prependRemoved S z.val z.property.1 z.property.2.1
            (fun j => z.property.2.2.1 _ ⟨j, rfl⟩)
            (fun j => z.property.2.2.2.1 _ ⟨j, rfl⟩) result
          recovered.account (by
            apply Or.inr
            apply Or.inl
            apply result.monotone.inactive u
            intro hlive
            have hn := (S.remove_live (S.pathRoots z.val) (S.B.forest.root u) hlive).2
            apply hn
            obtain ⟨j, hj⟩ := z.property.2.2.2.2.1
            apply (S.mem_pathRoots z.val _).2
            exact ⟨j, (congrArg S.B.forest.root hj).trans (S.B.forest.root_idempotent u)⟩)
        | .bottleneck b selected trees highest region =>
          let R : ActivePetalRecord M i cut := {
            input := S, left := u, right := v, queued := he,
            left_live := hu, right_live := hv, different := hsame,
            bottleneck := b, selected := selected, trees := trees,
            highest := highest, region := region, computed := hout }
          let T := R.afterPetal hc htop hstageTen
          let result := runBlockingBucket hc htop hstageTen T rest (fun e h =>
            R.afterPetal_bucket_mono hc htop hstageTen e.1 e.2 (2 * i + 1) (hrest e h))
          let advanced := BlockingBucketResult.advance
            (R.afterPetal_monotone hc htop hstageTen)
            (R.afterPetal_bucket_mono hc htop hstageTen)
            (fun _ _ _ h => R.afterPetal_liveBridgeArms hc htop hstageTen h) result
          advanced.account ((R.afterPetal_accounted hc htop hstageTen).mono result.monotone)
      else
        (runBlockingBucket hc htop hstageTen S rest hrest).skip (Or.inr (Or.inr hv))
    else
      (runBlockingBucket hc htop hstageTen S rest hrest).skip (Or.inr (Or.inl hu))
termination_by es.length

/-- A complete supplied bucket produces a maximal family of vertex-disjoint
shortest augmentations, using the initial vertex-contained arm coverage. -/
theorem runBlockingBucket_maximalShortest
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)
    (S : ActiveSearchState M i cut) (es : List (Fin n × Fin n))
    (hqueued : ∀ e, e ∈ es → e ∈ S.B.state.bucket (2 * i + 1))
    (hcover : ∀ p : AltPath M, p.Augmenting → p.length = 2 * i + 1 →
      ∃ u v, (u, v) ∈ es ∧ S.LiveBridgeArms u v (fun w => ∃ j, p.vertex j = w)) :
    (runBlockingBucket hc htop hstageTen S es hqueued).family.MaximalShortest (2 * i + 1) :=
  (runBlockingBucket hc htop hstageTen S es hqueued).maximalShortest (hstageTen ▸ htop) hcover

end MaximumMatching.Search
