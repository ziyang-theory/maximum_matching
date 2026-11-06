import MaximumMatching.ActiveSearchGraph
import MaximumMatching.RecoveryContainment

/-! Recover a shortest augmentation from the actual live DDFS arms. Expansion
uses stored parity routes, remains in live fibers, and contains both trigger
roots. The latter facts justify the next path deletion. -/
namespace MaximumMatching.Search.ActiveSearchState
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G} {i cut : Nat}

def recoverLivePath (S : ActiveSearchState M i cut)
    (htop : AtMostShortestAugmenting M (cut + 2)) (hstageTen : cut + 2 = 2 * i + 1)
    (u v : Fin n) (he : (u, v) ∈ S.B.state.bucket (2 * i + 1))
    (hu : S.B.forest.root u ∈ S.live) (hv : S.B.forest.root v ∈ S.live)
    (p q : DDFS.Path S.graph) (hp : p.ToBottom (S.B.forest.root u))
    (hq : q.ToBottom (S.B.forest.root v)) (hd : p.Disjoint q) :
    { z : AltPath M // z.Augmenting ∧ z.length = 2 * i + 1 ∧
      (∀ w, (∃ j, z.vertex j = w) → S.B.forest.root w ∈ S.live) ∧
      RootClosed S.B.forest z ∧
      (∃ j, z.vertex j = S.B.forest.root u) ∧ (∃ j, z.vertex j = S.B.forest.root v) } := by
  have hb := S.B.stage.classification.2.2 (2 * i + 1) u v he
  have hk := S.B.stage.current_bridge_known u v hb.1 hb.2
  have hpLive : p.first ∈ S.live := hp.1.symm ▸ hu
  have hqLive : q.first ∈ S.live := hq.1.symm ▸ hv
  let z := S.A.recoverShortestAugmentingWithCore S.B.stage.min.1 (S.A.weighted S.B.stage S.B.bud)
    (fun _ => rfl) (fun e => S.A.weighted_drop S.B.stage S.B.bud e)
    u v (2 * i + 1) hb.1.1 hk (by omega) (hstageTen ▸ htop)
    (S.liftPath p) (S.liftPath q)
    ⟨hp.1, S.liftPath_bottom p hpLive hp.2⟩
    ⟨hq.1, S.liftPath_bottom q hqLive hq.2⟩ hd
  have hfibers := z.property.2.2.2.2.2.2.1
  have hcore := z.property.2.2.2.2.2.2.2
  refine ⟨z.val, z.property.1, z.property.2.2.2.1, ?_,
    rootClosed_of_core_coverage S.B.forest z.val _ hfibers hcore, ?_, ?_⟩
  · intro w hw
    rcases hfibers w hw with hr | hg
    · exact S.path_live p hpLive _ hr
    · exact S.path_live q hqLive _ hg
  · exact hcore _ (Or.inl (hp.1 ▸ p.contains_first))
  · exact hcore _ (Or.inr (hq.1 ▸ q.contains_first))

end MaximumMatching.Search.ActiveSearchState
