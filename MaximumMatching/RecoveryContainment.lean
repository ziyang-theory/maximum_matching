import MaximumMatching.OperationalBridgeArms

/-! Containment of the actual recovered matching path. Every compressed root
occurs on its expansion, and each expanded vertex belongs to a root on the
compressed path. These two directions give closure under current bud lookup. -/
namespace MaximumMatching.Search
variable {V : Type} [DecidableEq V] {G : Graph V} {M : Matching G}

/-- Looking up the current bud of a path vertex stays on that same path. -/
def RootClosed (F : BudForest V) (p : AltPath M) : Prop :=
  ∀ v, (∃ j, p.vertex j = v) → ∃ j, p.vertex j = F.root v

/-- Two-way core coverage proves root closure without an assumption about
whole blossom membership or the choice of a shortest matching path. -/
theorem rootClosed_of_core_coverage (F : BudForest V) (p : AltPath M) (core : V → Prop)
    (hfibers : ∀ v, (∃ j, p.vertex j = v) → core (F.root v))
    (hcore : ∀ v, core v → ∃ j, p.vertex j = v) : RootClosed F p :=
  fun v hv => hcore (F.root v) (hfibers v hv)

/-- If every compressed root is live, the expansion avoids every dead fiber. -/
theorem recovered_fibers_live (F : BudForest V) (p : AltPath M) (core live : V → Prop)
    (hfibers : ∀ v, (∃ j, p.vertex j = v) → core (F.root v))
    (hlive : ∀ v, core v → live v) :
    ∀ v, (∃ j, p.vertex j = v) → live (F.root v) :=
  fun v hv => hlive (F.root v) (hfibers v hv)

namespace OperationalArms
variable {s : State V} {F : BudForest V} {cap : Nat} {h : BudGraphInvariant M cap s F}

/-- Exact core/fiber coverage for the compatibility API's computed path.
In particular the recovered path is closed under the current bud map. -/
theorem recoverShortestAugmenting_coverage (A : OperationalArms M s F) (hs : LabelsSound M s)
    (W : DDFS.FiberWeightedMatching M (DDFS.fixedRootGraph (predecessorGraph s F h) F) F)
    (hphase : ∀ v, W.phase v % 2 = ((s.minLabel v).getD 0 + 1) % 2)
    (hdrop : ∀ {u v} (he : (DDFS.fixedRootGraph (predecessorGraph s F h) F).Edge u v),
      (W.segment he).length + (s.minLabel v).getD 0 = (s.minLabel u).getD 0)
    (u v : V) (t : Nat) (hadj : G.Adj u v) (ht : edgeTenacity M s u v = some t)
    (hodd : t % 2 = 1) (hbound : AtMostShortestAugmenting M t)
    (p q : DDFS.Path (predecessorGraph s F h))
    (hp : p.ToBottom (F.root u)) (hq : q.ToBottom (F.root v)) (hdis : p.Disjoint q) :
    let z := (A.recoverShortestAugmenting hs W hphase hdrop u v t hadj ht hodd hbound p q hp hq hdis).val
    (∀ w, (∃ j, z.vertex j = w) → p.Contains (F.root w) ∨ q.Contains (F.root w)) ∧
      (∀ w, p.Contains w ∨ q.Contains w → ∃ j, z.vertex j = w) ∧ RootClosed F z := by
  let z := A.recoverShortestAugmentingWithCore hs W hphase hdrop u v t hadj ht hodd hbound p q hp hq hdis
  have hfibers := z.property.2.2.2.2.2.2.1
  have hcore := z.property.2.2.2.2.2.2.2
  exact ⟨hfibers, hcore, rootClosed_of_core_coverage F z.val _ hfibers hcore⟩

end OperationalArms

namespace CurrentBucketWitness
variable {n : Nat} {G : Graph (Fin n)} {M : Matching G}
    {i cut : Nat} {B : CurrentBucketState M i cut}

/-- The exact matching path recovered from this computed DDFS certificate
contains both compressed cores and is closed under the certificate's bud map. -/
theorem recover_coverage (certificate : CurrentBucketWitness B)
    (A : OperationalArms M B.state B.forest)
    (hc : cut % 2 = 1) (htop : AtMostShortestAugmenting M (cut + 2))
    (hstageTen : cut + 2 = 2 * i + 1) :
    let p := (certificate.recover A hc htop hstageTen).val
    (∀ w, (∃ j, p.vertex j = w) →
      certificate.red.Contains (B.forest.root w) ∨ certificate.green.Contains (B.forest.root w)) ∧
      (∀ w, certificate.red.Contains w ∨ certificate.green.Contains w → ∃ j, p.vertex j = w) ∧
      RootClosed B.forest p := by
  let p := certificate.recoverWithCore A hc htop hstageTen
  have hfibers := p.property.2.2.2.2.2.2.1
  have hcore := p.property.2.2.2.2.2.2.2
  exact ⟨hfibers, hcore, rootClosed_of_core_coverage B.forest p.val _ hfibers hcore⟩

end CurrentBucketWitness
end MaximumMatching.Search
