import MaximumMatching.CurrentBucket
import MaximumMatching.OperationalMaxRoutes

/-! The actual current-bucket loop with computational parity arms retained.
Erasing these additional path data gives exactly the existing MIN/MAX bucket
execution, including the same raw DDFS witness and recorded petal history. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)}

inductive RecoverableBucketOutcome (M : Matching G) (i cut : Nat) where
  | exhausted (state : CurrentBucketState M i cut)
      (arms : OperationalArms M state.state state.forest)
  | found (state : CurrentBucketState M i cut)
      (arms : OperationalArms M state.state state.forest)
      (witness : CurrentBucketWitness state)

namespace RecoverableBucketOutcome
variable {M : Matching G} {i cut : Nat}

def erase : RecoverableBucketOutcome M i cut → CurrentBucketOutcome M i cut
  | .exhausted B _ => .exhausted B
  | .found B _ W => .found B W

end RecoverableBucketOutcome

/-- Process exactly the same triggers as `runCurrentBucket`, carrying the
computed parity arms through each actual MAX assignment and petal merge. -/
def runRecoverableBucket [DecidableRel G.Adj] {M : Matching G} {i cut : Nat}
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)
    (B : CurrentBucketState M i cut) (A : OperationalArms M B.state B.forest)
    (es : List (Fin n × Fin n))
    (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1)) :
    RecoverableBucketOutcome M i cut × List (PetalRecord M) :=
  match es with
  | [] => (.exhausted B A, [])
  | (u, v) :: rest =>
    have he := hqueued (u, v) List.mem_cons_self
    have hb := B.stage.classification.2.2 (2 * i + 1) u v he
    have hknown := B.stage.current_bridge_known u v hb.1 hb.2
    if hsame : B.forest.root u = B.forest.root v then
      runRecoverableBucket hc htop hstageTen B A rest
        (fun e he => hqueued e (List.mem_cons_of_mem (u, v) he))
    else
      match hout : DDFS.Machine.executeFull B.bud.reachBottom (B.forest.root u) (B.forest.root v) with
      | .disjoint p q hp hq hd =>
        (.found B A {
          left := u, right := v, queued := he, red := p, green := q,
          red_bottom := hp, green_bottom := hq, disjoint := hd, computed := hout }, [])
      | .bottleneck b S trees highest region =>
        let R : PetalRecord M := {
          cap := i + 1, prior := B.state, forest := B.forest, invariant := B.bud,
          queueSound := B.stage.classification.2.2, tenacity := 2 * i + 1,
          left := u, right := v, queued := he, known := hknown, different := hsame,
          bottleneck := b, selected := S, trees := trees, highest := highest,
          region := region, computed := hout }
        let next := CurrentBucketState.afterPetal R B.represented hc htop hstageTen.symm hstageTen rfl B.stage
        let nextArms := OperationalArms.afterMax R A i cut B.represented hc htop
          hstageTen.symm hstageTen rfl B.stage
        let result := runRecoverableBucket hc htop hstageTen next nextArms rest (by
          intro e he'
          exact R.maxEvent_bucket_mono i e.1 e.2 (2 * i + 1)
            (hqueued e (List.mem_cons_of_mem (u, v) he')))
        (result.1, R :: result.2)
termination_by es.length

section
variable [DecidableRel G.Adj] {M : Matching G} {i cut : Nat}
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)

/-- Computational path data do not change any actual MIN/MAX/DDFS decision
or the returned operational state and raw search certificate. -/
theorem runRecoverableBucket_erase (B : CurrentBucketState M i cut)
    (A : OperationalArms M B.state B.forest) (es : List (Fin n × Fin n))
    (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1)) :
    (runRecoverableBucket hc htop hstageTen B A es hqueued).1.erase =
      (runCurrentBucket hc htop hstageTen B es hqueued).1 := by
  induction es generalizing B with
  | nil => simp only [runRecoverableBucket, runCurrentBucket, RecoverableBucketOutcome.erase]
  | cons e es ih =>
    rcases e with ⟨u, v⟩
    rw [runRecoverableBucket, runCurrentBucket]
    split
    · exact ih B A _
    · split
      · rename_i p q hp hq hd hout
        split
        · rename_i p' q' hp' hq' hd' hout'
          have he := hout.symm.trans hout'
          cases he
          rfl
        · rename_i b S trees highest region hout'
          have he := hout.symm.trans hout'
          cases he
      · rename_i b S trees highest region hout
        split
        · rename_i p q hp hq hd hout'
          have he := hout.symm.trans hout'
          cases he
        · rename_i b' S' trees' highest' region' hout'
          have he := hout.symm.trans hout'
          cases he
          exact ih _ _ _

/-- The recovered execution also retains exactly the original actual petal
history, in the same chronological order. -/
theorem runRecoverableBucket_history (B : CurrentBucketState M i cut)
    (A : OperationalArms M B.state B.forest) (es : List (Fin n × Fin n))
    (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1)) :
    (runRecoverableBucket hc htop hstageTen B A es hqueued).2 =
      (runCurrentBucket hc htop hstageTen B es hqueued).2 := by
  induction es generalizing B with
  | nil => simp only [runRecoverableBucket, runCurrentBucket]
  | cons e es ih =>
    rcases e with ⟨u, v⟩
    rw [runRecoverableBucket, runCurrentBucket]
    split
    · exact ih B A _
    · split
      · rename_i p q hp hq hd hout
        split
        · rfl
        · rename_i b S trees highest region hout'
          have he := hout.symm.trans hout'
          cases he
      · rename_i b S trees highest region hout
        split
        · rename_i p q hp hq hd hout'
          have he := hout.symm.trans hout'
          cases he
        · rename_i b' S' trees' highest' region' hout'
          have he := hout.symm.trans hout'
          cases he
          exact congrArg (List.cons _) (ih _ _ _)

end
end MaximumMatching.Search
