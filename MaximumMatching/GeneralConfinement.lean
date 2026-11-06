import MaximumMatching.GeneralLowerConfinement
import MaximumMatching.GeneralBlossomMembership
import MaximumMatching.GeneralFirstEntryPrefix
import MaximumMatching.GeneralMaxCapPredecessor

/-! The confinement step at an arbitrary odd tenacity. Induction on actual
shortest-path length handles honest prefixes. At a dishonest predecessor,
the first entry into the endpoint's lower blossom supplies a shorter honest
prefix and a confined tail. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Current-tenacity shortest paths stay in their actual boundary blossom.
The only confinement premise is at the preceding odd cutoff. -/
theorem current_blossom_suffix_mem (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w)
    (hcurrent : ∀ v : V, tenacity M v = some t → ∃ b, IsBase M v b)
    (r : AltPath M) (hr : r.Shortest) (hrt : tenacity M r.last = some t)
    (b : V) (hb : levelLT (some t) (tenacity M b)) (hbl : Blossom M t b r.last)
    (i j : Fin (r.length + 1)) (hi : r.vertex i = b) (hij : i.val < j.val) :
    Blossom M t b (r.vertex j) := by
  have hall : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b := by
    intro v s hs hst
    by_cases he : s = t
    · exact hcurrent v (he ▸ hs)
    · have hsodd := tenacity_odd M v s hs
      exact hexists v s hs (by omega)
  have aux : ∀ L (p : AltPath M), p.length = L → p.Shortest → tenacity M p.last = some t →
      ∀ (b : V), levelLT (some t) (tenacity M b) → Blossom M t b p.last →
      ∀ (i j : Fin (p.length + 1)), p.vertex i = b → i.val < j.val →
        Blossom M t b (p.vertex j) := by
    intro L
    induction L using Nat.strongRecOn with
    | ind L ih =>
      intro p hpL hp hpt b hb hbl i j hi hij
      have hbase := blossom_baseOnPath t b p.last hbl hb p rfl hp
      by_cases hjlast : j.val = p.length
      · have hj : j = ⟨p.length, by omega⟩ := Fin.ext hjlast
        rw [hj]
        exact hbl
      have hjlt : j.val < p.length := by have := j.isLt; omega
      have hpos : 0 < p.length := by omega
      have hprefix (K : Fin (p.length + 1)) (hK : K.val < p.length)
          (hshort : (p.take K.val (by omega)).Shortest)
          (hjK : j.val ≤ K.val) : Blossom M t b (p.vertex j) := by
        have hiK : i.val < K.val := by omega
        obtain ⟨s, hs, hst⟩ := blossom_suffix_tenacity_bound t b p.last hbl hb p rfl hp i K hi hiK
        let a := p.take K.val (by omega)
        have habase := p.baseOnPath_take_after t b hbase i K hi (by omega)
        have hamem : Blossom M t b a.last := a.blossom_of_shortest_base hshort t ht hall b habase
          (by change levelLE (tenacity M (p.vertex K)) (some t); rw [hs]; exact hst)
        by_cases he : s = t
        · exact ih K.val (by omega) a rfl hshort (by change tenacity M (p.vertex K) = some t; simpa only [he] using hs)
            b hb hamem ⟨i.val, by change i.val < K.val + 1; omega⟩
            ⟨j.val, by change j.val < K.val + 1; omega⟩ hi hij
        · exact a.lower_endpoint_blossom_suffix_mem hshort t ht hexists hconf hcurrent b hb hamem
            s hs (by omega) ⟨i.val, by change i.val < K.val + 1; omega⟩
            ⟨j.val, by change j.val < K.val + 1; omega⟩ hi hij
      let pred : Fin (p.length + 1) := ⟨p.length - 1, by omega⟩
      by_cases hpred : p.BFSHonest pred
      · exact hprefix pred (by change p.length - 1 < p.length; omega) hpred
          (by change j.val ≤ p.length - 1; omega)
      · obtain ⟨hpo, houter⟩ := p.dishonest_last_predecessor_outer hp t hpt hpos hpred
        obtain ⟨s, hs, hst⟩ := blossom_suffix_tenacity_bound t b p.last hbl hb p rfl hp i pred hi
          (by change i.val < p.length - 1; omega)
        have hst' : s < t := by
          by_cases he : s = t
          · have hhon := (p.limited_bfs_honesty hp pred (by rw [hpt, hs, he]; exact Nat.le_refl _)).1
            exact False.elim (hpred hhon)
          · omega
        have hsodd := tenacity_odd M (p.vertex pred) s hs
        have hcutodd : (t - 2) % 2 = 1 := by omega
        have hclow : levelLT (some (t - 2)) (tenacity M p.last) := by
          rw [hpt]
          change t - 2 < t
          omega
        have hmember := (p.dishonest_outer_predecessor_base hp hpo houter t s hpt hs hst'
          (hexists (p.vertex pred) s hs (by omega)) hpred).2
        obtain ⟨D, hDo, hDmem, hfirst, htailshort, htail⟩ := p.exists_first_entry_confined_tail hp hpo
          (t - 2) hclow (by intro v hv q hq hqf hql; exact hconf p.last v hv hclow q hq hqf hql)
          ⟨pred, hmember⟩
        have htailcurrent : ∀ k : Fin (p.length + 1), D.val ≤ k.val → Blossom M t b (p.vertex k) := by
          intro k hDk
          rcases htail k hDk with he | hm
          · rw [he]
            exact hbl
          · exact (blossom_strict_nested_of_base_mem (t - 2) t ht p.last b hclow hbl).1 _ hm
        have hiD : i.val < D.val := by
          by_cases hDi : D.val ≤ i.val
          · exact False.elim (blossom_excludes_base t b hb (hi ▸ htailcurrent i hDi))
          · omega
        by_cases hDj : D.val ≤ j.val
        · exact htailcurrent j hDj
        · have hhon := p.first_entry_prefix_honest hp hpo t hpt hexists hconf D hDo hDmem hfirst htailshort
          exact hprefix ⟨D.val - 1, by have := D.isLt; omega⟩
            (by change D.val - 1 < p.length; have := D.isLt; omega) hhon
            (by change j.val ≤ D.val - 1; omega)
  exact aux r.length r rfl hr hrt b hb hbl i j hi hij

/-- Global shortest-path confinement for every member of the current blossom,
combining the current-tenacity and lower-tenacity endpoint cases. -/
theorem general_blossom_suffix_mem_of_current (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w)
    (hcurrent : ∀ v : V, tenacity M v = some t → ∃ b, IsBase M v b)
    (r : AltPath M) (hr : r.Shortest)
    (b : V) (hb : levelLT (some t) (tenacity M b)) (hbl : Blossom M t b r.last)
    (i j : Fin (r.length + 1)) (hi : r.vertex i = b) (hij : i.val < j.val) :
    Blossom M t b (r.vertex j) := by
  obtain ⟨s, hs, hst⟩ := blossom_tenacity_bound t b r.last hbl
  by_cases he : s = t
  · exact current_blossom_suffix_mem t ht hexists hconf hcurrent r hr
      (he ▸ hs) b hb hbl i j hi hij
  · exact r.lower_endpoint_blossom_suffix_mem hr t ht hexists hconf hcurrent b hb hbl
      s hs (by omega) i j hi hij

end MaximumMatching.AltPath

namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The full current-cutoff relative confinement step. Every shortest relative
path is joined to a shortest even boundary prefix using derived disjointness. -/
theorem general_blossom_relative_confined_of_current
    (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t - 2 → ∃ b, IsBase M v b)
    (hconf : ∀ (b v : V), Blossom M (t - 2) b v → levelLT (some (t - 2)) (tenacity M b) →
      ∀ q : AltSegment M, q.Shortest → q.first = b → q.last = v →
        ∀ w, q.Contains w → w = b ∨ Blossom M (t - 2) b w)
    (hcurrent : ∀ v : V, tenacity M v = some t → ∃ b, IsBase M v b)
    (b v : V) (hv : Blossom M t b v) (hb : levelLT (some t) (tenacity M b))
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v) :
    ∀ w, q.Contains w → w = b ∨ Blossom M t b w := by
  obtain ⟨s, hs, _⟩ := blossom_tenacity_bound t b v hv
  obtain ⟨r, hrv, hr, _⟩ := finite_tenacity_shortest_parity v s 0 hs
  obtain ⟨i, hib, hie, _, _, hip⟩ := blossom_on_shortest t b v hv r hrv hr
  let p := r.take i.val (by omega)
  have hp : p.Shortest := hip
  have hpe : p.length % 2 = 0 := hie
  have hpb : p.last = b := hib
  let hdis := blossom_relative_avoids_prefix t b v hv hb p hp hpe hpb q hq hqb hqv
  let joined := p.appendSegment q hpe (hpb.trans hqb.symm) hdis
  have hjshort : joined.Shortest := blossom_append_relative_shortest t b v hv hb p hp hpe hpb q hq hqb hqv
  have hjend : joined.last = v := (p.appendSegment_last q hpe (hpb.trans hqb.symm) hdis).trans hqv
  let baseIndex : Fin (joined.length + 1) := ⟨p.length, by change p.length < p.length + q.length + 1; omega⟩
  have hbase : joined.vertex baseIndex = b := by
    change (if h : p.length ≤ p.length then p.vertex ⟨p.length, _⟩ else _) = b
    simpa only [Nat.le_refl, dite_true, AltPath.last] using hpb
  intro w hw
  obtain ⟨j, rfl⟩ := hw
  by_cases hj : j.val = 0
  · have hj0 : j = ⟨0, by omega⟩ := Fin.ext hj
    exact Or.inl (by rw [hj0]; exact hqb)
  · apply Or.inr
    have hc := AltPath.general_blossom_suffix_mem_of_current t ht hexists hconf hcurrent joined hjshort b hb
      (by rw [hjend]; exact hv) baseIndex
      ⟨p.length + j.val, by change p.length + j.val < p.length + q.length + 1; omega⟩
      hbase (by change p.length < p.length + j.val; omega)
    rwa [p.appendSegment_vertex_suffix q hpe (hpb.trans hqb.symm) hdis j] at hc

end MaximumMatching
