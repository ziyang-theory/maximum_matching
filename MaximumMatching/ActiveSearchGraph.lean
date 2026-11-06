import MaximumMatching.RecoverableBucket
import MaximumMatching.RecursiveRemoval
import MaximumMatching.OperationalRepresentation

/-! The live predecessor graph used after paths have been removed during a
blocking phase. Labels and original predecessor lists retain their full-graph
meaning; live DDFS searches use the explicitly restricted root graph. -/
namespace MaximumMatching.Search
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}

/-- A current-level state with computed routes and an explicit list of live
bud roots. Original vertices are live through membership of their bud root. -/
structure ActiveSearchState (M : Matching G) (i cut : Nat) where
  B : CurrentBucketState M i cut
  A : OperationalArms M B.state B.forest
  live : List (Fin n)
  live_fixed : ∀ v, v ∈ live → B.forest.root v = v
  reach : DDFS.ReachBottom (DDFS.RecursiveRemoval.restricted
    (predecessorGraph B.state B.forest B.bud) live)

namespace ActiveSearchState
variable {i cut : Nat}

abbrev graph (S : ActiveSearchState M i cut) :=
  DDFS.RecursiveRemoval.restricted (predecessorGraph S.B.state S.B.forest S.B.bud) S.live

instance (S : ActiveSearchState M i cut) : DecidableRel S.graph.Edge :=
  inferInstanceAs (DecidableRel (DDFS.RecursiveRemoval.restricted _ _).Edge)

/-- Lift a live graph path by retaining its actual vertex sequence. -/
def liftPath (S : ActiveSearchState M i cut) (p : DDFS.Path S.graph) :
    DDFS.Path (predecessorGraph S.B.state S.B.forest S.B.bud) where
  length := p.length
  vertex := p.vertex
  adjacent j := (p.adjacent j).2.2

theorem path_live (S : ActiveSearchState M i cut) (p : DDFS.Path S.graph)
    (hf : p.first ∈ S.live) (v : Fin n) (hv : p.Contains v) : v ∈ S.live := by
  obtain ⟨j, rfl⟩ := hv
  exact DDFS.RecursiveRemoval.restricted_path_live _ _ p hf j

theorem level_live (S : ActiveSearchState M i cut) (v : Fin n) (hv : v ∈ S.live) :
    S.graph.level v = (S.B.state.minLabel v).getD 0 := by
  change (if v ∈ S.live then _ else 0) = _
  exact ite_eq_left hv

theorem liftPath_bottom (S : ActiveSearchState M i cut) (p : DDFS.Path S.graph)
    (hf : p.first ∈ S.live) (hb : S.graph.level p.last = 0) :
    (predecessorGraph S.B.state S.B.forest S.B.bud).level (S.liftPath p).last = 0 := by
  have hv := S.path_live p hf p.last p.contains_last
  exact (S.level_live p.last hv).symm.trans hb

end ActiveSearchState
end MaximumMatching.Search
