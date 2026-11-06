import MaximumMatching.GeneralStructureInduction

/-! Canonical-base transfer along actual shortest paths. A suffix containing
only vertices of tenacity at most the current cutoff preserves its prefix's
last high vertex. These are path statements, with no support-discovery or
mutable-bud premise. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The proved common-base theorem turns a base witnessed on one actual
shortest path into the semantic base of its endpoint. -/
theorem isBase_of_baseOnPath (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (ht : EligibleTenacity M t) (hpt : tenacity M p.last = some t)
    (b : V) (hb : p.BaseOnPath t b) : IsBase M p.last b := by
  obtain ⟨c, hc, _⟩ := general_unique_base M t ht p.last hpt
  have hcb := p.baseOnPath_unique t c b (hc p rfl hp) hb
  exact hcb ▸ (show IsBase M p.last c from ⟨t, hpt, hc⟩)

/-- If the named prefix endpoint is above the cutoff and all later vertices
are at or below it, that vertex is the endpoint's canonical base. -/
theorem isBase_of_high_suffix_boundary (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (ht : EligibleTenacity M t) (hpt : tenacity M p.last = some t)
    (i : Fin (p.length + 1)) (hi : levelLT (some t) (tenacity M (p.vertex i)))
    (htail : ∀ j : Fin (p.length + 1), i.val < j.val →
      levelLE (tenacity M (p.vertex j)) (some t)) : IsBase M p.last (p.vertex i) := by
  apply p.isBase_of_baseOnPath hp t ht hpt
  refine ⟨i, rfl, hi, ?_⟩
  intro j hij hj
  have hl := htail j hij
  cases he : tenacity M (p.vertex j) with
  | none => simp only [he, levelLE] at hl
  | some k =>
    rw [he] at hl hj
    change t < k at hj
    change k ≤ t at hl
    omega

/-- An honest prefix ending at the current tenacity and a suffix with no
higher-tenacity vertex have the same canonical base. This permits an
intermediate bud itself to have the current tenacity. -/
theorem common_base_of_shortest_prefix (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (ht : EligibleTenacity M t) (hpt : tenacity M p.last = some t)
    (i : Fin (p.length + 1)) (hi : tenacity M (p.vertex i) = some t)
    (hprefix : (p.take i.val (by omega)).Shortest)
    (htail : ∀ j : Fin (p.length + 1), i.val < j.val →
      levelLE (tenacity M (p.vertex j)) (some t)) :
    ∃ b, IsBase M p.last b ∧ IsBase M (p.vertex i) b := by
  obtain ⟨b, hb, _⟩ := general_unique_base M t ht (p.vertex i) hi
  have hqb := hb (p.take i.val (by omega)) rfl hprefix
  have hpb : p.BaseOnPath t b := by
    apply ((p.take i.val (by omega)).baseOnPath_initial_iff p
      (by simp only [take_length]; omega) (fun _ => rfl) t ?_ b).1 hqb
    intro j hj hhigh
    have hl := htail j hj
    cases he : tenacity M (p.vertex j) with
    | none => simp only [he, levelLE] at hl
    | some k =>
      rw [he] at hl hhigh
      change k ≤ t at hl
      change t < k at hhigh
      omega
  exact ⟨b, p.isBase_of_baseOnPath hp t ht hpt b hpb, t, hi, hb⟩

theorem base_eq_of_shortest_prefix (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (ht : EligibleTenacity M t) (hpt : tenacity M p.last = some t)
    (i : Fin (p.length + 1)) (hi : tenacity M (p.vertex i) = some t)
    (hprefix : (p.take i.val (by omega)).Shortest)
    (htail : ∀ j : Fin (p.length + 1), i.val < j.val →
      levelLE (tenacity M (p.vertex j)) (some t)) :
    base M p.last = base M (p.vertex i) := by
  obtain ⟨b, hb, hi⟩ := p.common_base_of_shortest_prefix hp t ht hpt i hi hprefix htail
  exact ((base_eq_some_iff p.last b).2 hb).trans
    ((base_eq_some_iff (p.vertex i) b).2 hi).symm

end MaximumMatching.AltPath
