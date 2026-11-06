import MaximumMatching.CurrentBucketFacts
import MaximumMatching.PetalCurrentMax

/-! Concrete processing of a fixed current-tenacity bucket. Each distinct-root
trigger runs DDFS once; bottleneck events execute actual MAX and contraction.
The executable result retains raw disjoint DDFS paths, not a path selected by
classical choice. Matching-path recovery and complete support coverage remain
separate theorems. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)}

/-- Operational state plus erased correctness and path-representation proofs.
The representation is existential in Prop, so it is not a runtime oracle. -/
structure CurrentBucketState (M : Matching G) (i cut : Nat) where
  state : State (Fin n)
  forest : BudForest (Fin n)
  stage : StageState M (i + 1) (2 * i + 1) state
  bud : BudGraphInvariant M (i + 1) state forest
  represented : Nonempty (CurrentBridgeRepresentation M cut bud)

namespace CurrentBucketState
variable {M : Matching G} {i cut : Nat}

/-- Build the next operational node from the actual recorded MAX event.
Its representation proof is erased, while all state and forest operations
remain the executable ones already defined. -/
def afterPetal [DecidableRel G.Adj] (R : PetalRecord M)
    (hP : Nonempty (CurrentBridgeRepresentation M cut R.invariant))
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hten : R.tenacity = cut + 2) (hstageTen : cut + 2 = 2 * i + 1)
    (hcap : R.cap = i + 1) (hstage : StageState M (i + 1) (2 * i + 1) R.prior) :
    CurrentBucketState M i cut where
  state := (R.maxEvent i).1
  forest := R.after
  stage := by
    obtain ⟨P⟩ := hP
    exact (R.maxEvent_correct_of_current P i (2 * i + 1) hc htop hten hstageTen hcap hstage).1
  bud := by
    obtain ⟨P⟩ := hP
    exact (R.maxEvent_correct_of_current P i (2 * i + 1) hc htop hten hstageTen hcap hstage).2.1
  represented := by
    obtain ⟨P⟩ := hP
    exact ⟨R.maxEvent_representation P i _⟩

end CurrentBucketState

/-- A disjoint output from the actual call at its precise matching state. -/
structure CurrentBucketWitness {M : Matching G} {i cut : Nat} (B : CurrentBucketState M i cut) where
  left : Fin n
  right : Fin n
  queued : (left, right) ∈ B.state.bucket (2 * i + 1)
  red : DDFS.Path (predecessorGraph B.state B.forest B.bud)
  green : DDFS.Path (predecessorGraph B.state B.forest B.bud)
  red_bottom : red.ToBottom (B.forest.root left)
  green_bottom : green.ToBottom (B.forest.root right)
  disjoint : red.Disjoint green
  computed : DDFS.Machine.executeFull B.bud.reachBottom (B.forest.root left) (B.forest.root right) =
    .disjoint red green red_bottom green_bottom disjoint

inductive CurrentBucketOutcome (M : Matching G) (i cut : Nat) where
  | exhausted (state : CurrentBucketState M i cut)
  | found (state : CurrentBucketState M i cut) (witness : CurrentBucketWitness state)

/-- Execute a fixed list of queued current bridges. The list may have
repetitions; already-contracted equal roots are skipped. Each newly formed
petal is retained with its actual prior state for later path recovery. -/
def runCurrentBucket [DecidableRel G.Adj] {M : Matching G} {i cut : Nat}
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1)
    (B : CurrentBucketState M i cut) (es : List (Fin n × Fin n))
    (hqueued : ∀ e, e ∈ es → e ∈ B.state.bucket (2 * i + 1)) :
    CurrentBucketOutcome M i cut × List (PetalRecord M) :=
  match es with
  | [] => (.exhausted B, [])
  | (u, v) :: rest =>
    have he := hqueued (u, v) List.mem_cons_self
    have hb := B.stage.classification.2.2 (2 * i + 1) u v he
    have hknown := B.stage.current_bridge_known u v hb.1 hb.2
    if hsame : B.forest.root u = B.forest.root v then
      runCurrentBucket hc htop hstageTen B rest
        (fun e he => hqueued e (List.mem_cons_of_mem (u, v) he))
    else
      match hout : DDFS.Machine.executeFull B.bud.reachBottom (B.forest.root u) (B.forest.root v) with
      | .disjoint p q hp hq hd =>
        (.found B {
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
        let result := runCurrentBucket hc htop hstageTen next rest (by
          intro e he'
          exact R.maxEvent_bucket_mono i e.1 e.2 (2 * i + 1)
            (hqueued e (List.mem_cons_of_mem (u, v) he')))
        (result.1, R :: result.2)
termination_by es.length

namespace CurrentBucketWitness
variable {M : Matching G} {i cut : Nat} {B : CurrentBucketState M i cut}

/-- A returned raw disjoint certificate has a real shortest augmenting path
through its actual queued trigger. This is a soundness theorem, not an
executable path reconstruction by classical choice. -/
theorem shortest_augmenting (W : CurrentBucketWitness B)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) :
    ∃ p : AltPath M, p.Augmenting ∧ p.length = 2 * i + 1 ∧
      p.ContainsEdge W.left W.right ∧
      ∀ q : AltPath M, q.Augmenting → p.length ≤ q.length := by
  obtain ⟨P⟩ := B.represented
  have hb := B.stage.classification.2.2 (2 * i + 1) W.left W.right W.queued
  have hk := B.stage.current_bridge_known W.left W.right hb.1 hb.2
  obtain ⟨hu, hv⟩ := edgeTenacity_has_minLabels B.state W.left W.right (2 * i + 1) hk
  obtain ⟨p, hp, hlen, hedge, hshort⟩ := P.disjoint_bridge_paths_shortest hc htop
    W.left W.right hb.1 (by rw [hstageTen]; exact hb.2) hu hv
    W.red W.green W.red_bottom W.green_bottom W.disjoint
  exact ⟨p, hp, hlen.trans hstageTen, hedge, hshort⟩

end CurrentBucketWitness
end MaximumMatching.Search
