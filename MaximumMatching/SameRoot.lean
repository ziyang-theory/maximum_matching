import MaximumMatching.Base

/-! Same-free-root paths of opposite parity, for Lemma 6.9. -/
namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Strict prefix of p before i avoids the prefix of q through j. -/
def PrefixAvoids (p q : AltPath M) (i : Fin (p.length + 1))
    (j : Fin (q.length + 1)) : Prop :=
  ∀ (a : Fin (p.length + 1)) (b : Fin (q.length + 1)),
    a.val < i.val → b.val ≤ j.val → p.vertex a ≠ q.vertex b

theorem prefix_reverse_disjoint_right (p q : AltPath M)
    (i : Fin (p.length + 1)) (j : Fin (q.length + 1))
    (hd : p.PrefixAvoids q i j) :
    (q.take j.val (by omega)).ReverseDisjoint p 0 i.val := by
  intro a b _ hb he
  have ha : a.val ≤ j.val := by have := a.isLt; change a.val < j.val + 1 at this; omega
  exact hd b ⟨a.val, by omega⟩ hb ha he.symm

theorem prefix_reverse_disjoint_left (p q : AltPath M)
    (i : Fin (p.length + 1)) (j : Fin (q.length + 1))
    (hj : p.vertex i = q.vertex j) (hd : p.PrefixAvoids q i j) :
    (p.take i.val (by omega)).ReverseDisjoint q 0 j.val := by
  intro a b _ hb he
  have ha : a.val ≤ i.val := by have := a.isLt; change a.val < i.val + 1 at this; omega
  change p.vertex ⟨a.val, _⟩ = q.vertex b at he
  by_cases hal : a.val < i.val
  · exact hd ⟨a.val, by omega⟩ b hal (by omega) he
  · have hai : (⟨a.val, by omega⟩ : Fin (p.length + 1)) = i := Fin.ext (by change a.val = i.val; omega)
    rw [hai, hj] at he
    have hbi : j.val = b.val := congrArg Fin.val (q.injective _ _ he)
    omega

/-- If disjoint prefixes meet at opposite parities, reversing one gives a short
augmenting path. Excluding such paths forces equal parity at the meeting point. -/
theorem intersection_parity (p q : AltPath M)
    (i : Fin (p.length + 1)) (j : Fin (q.length + 1))
    (hj : p.vertex i = q.vertex j) (hd : p.PrefixAvoids q i j)
    (t : Nat) (hbound : i.val + j.val ≤ t)
    (hno : ∀ r : AltPath M, r.Augmenting → t < r.length) :
    i.val % 2 = j.val % 2 := by
  by_cases hi : i.val % 2 = 0
  · by_cases hje : j.val % 2 = 0
    · omega
    · have hjo : j.val % 2 = 1 := by omega
      let r := (q.take j.val (by omega)).spliceReverse p 0 i.val (by omega) (by omega)
        hj.symm hjo hi (p.prefix_reverse_disjoint_right q i j hd)
      have hrlen : r.length = j.val + i.val := by rfl
      have hrend : r.last = p.first := by
        simpa only [first] using spliceReverse_last (q.take j.val (by omega)) p 0 i.val
          (by omega) (by omega) hj.symm hjo hi (p.prefix_reverse_disjoint_right q i j hd)
      have hra : r.Augmenting := ⟨by omega, by rw [hrend]; exact p.start_free⟩
      have := hno r hra
      omega
  · have hio : i.val % 2 = 1 := by omega
    by_cases hjo : j.val % 2 = 1
    · omega
    · have hje : j.val % 2 = 0 := by omega
      let r := (p.take i.val (by omega)).spliceReverse q 0 j.val (by omega) (by omega)
        hj hio hje (p.prefix_reverse_disjoint_left q i j hj hd)
      have hrlen : r.length = i.val + j.val := by rfl
      have hrend : r.last = q.first := by
        simpa only [first] using spliceReverse_last (p.take i.val (by omega)) q 0 j.val
          (by omega) (by omega) hj hio hje (p.prefix_reverse_disjoint_left q i j hj hd)
      have hra : r.Augmenting := ⟨by omega, by rw [hrend]; exact q.start_free⟩
      have := hno r hra
      omega

/-- The prefix before the first intersection avoids the other path completely. -/
theorem FirstHit.prefix_avoids {q p : AltPath M} (h : FirstHit q p 0) :
    q.PrefixAvoids p h.qi h.pi := by
  intro a b ha _
  exact h.first a b ha (by omega)

/-- A first hit cannot beat a shortest path's prefix when short augmenting paths
are excluded, even when the two free roots differ. -/
theorem FirstHit.index_le {q p : AltPath M} (h : FirstHit q p 0)
    (hp : p.Shortest) (t : Nat) (hbound : p.length + q.length ≤ t)
    (hno : ∀ r : AltPath M, r.Augmenting → t < r.length) : h.pi.val ≤ h.qi.val := by
  have hpar := q.intersection_parity p h.qi h.pi h.hit h.prefix_avoids t (by omega) hno
  let r := (q.take h.qi.val (by omega)).splice p h.pi.val (by omega)
    h.hit hpar h.forward_disjoint
  have hrlen : r.length = h.qi.val + (p.length - h.pi.val) := rfl
  have hrend : r.last = p.last := splice_last _ _ _ _ _ _ _
  have hrpar : r.length % 2 = p.length % 2 := splice_parity _ _ _ _ _ _ _
  have hle := hp.2 r.length ⟨r, hrend, rfl, hrpar⟩
  omega

/-- Shortest paths meeting at the same endpoint can exchange roots if their total
length is below every augmenting-path length. The constructed path retains the
second path's length/parity and the first path's free root. -/
theorem shortest_root_transfer (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hend : p.last = q.last)
    (hno : ∀ r : AltPath M, r.Augmenting → p.length + q.length < r.length) :
    ∃ r : AltPath M, r.first = p.first ∧ r.last = q.last ∧
      r.length = q.length ∧ r.Shortest := by
  obtain ⟨a⟩ := firstHit_exists q p 0
    ⟨⟨q.length, by omega⟩, ⟨p.length, by omega⟩, by omega, hend.symm⟩
  obtain ⟨b⟩ := firstHit_exists p q 0
    ⟨⟨p.length, by omega⟩, ⟨q.length, by omega⟩, by omega, hend⟩
  have hab : a.qi.val ≤ b.pi.val := by
    by_cases hlt : b.pi.val < a.qi.val
    · exact False.elim (a.first b.pi b.qi hlt (by omega) b.hit.symm)
    · omega
  have hba : b.qi.val ≤ a.pi.val := by
    by_cases hlt : a.pi.val < b.qi.val
    · exact False.elim (b.first a.pi a.qi hlt (by omega) a.hit.symm)
    · omega
  have ha := a.index_le hp (p.length + q.length) (by omega) hno
  have hle : b.qi.val ≤ b.pi.val := by omega
  have hpar := p.intersection_parity q b.qi b.pi b.hit b.prefix_avoids
    (p.length + q.length) (by omega) hno
  let r := (p.take b.qi.val (by omega)).splice q b.pi.val (by omega)
    b.hit hpar b.forward_disjoint
  have hrlen : r.length = b.qi.val + (q.length - b.pi.val) := rfl
  have hrpar : r.length % 2 = q.length % 2 := splice_parity _ _ _ _ _ _ _
  have hrend : r.last = q.last := splice_last _ _ _ _ _ _ _
  have hmin := hq.2 r.length ⟨r, hrend, rfl, hrpar⟩
  have hlength : r.length = q.length := by omega
  refine ⟨r, ?_, hrend, hlength, ?_⟩
  · simp only [r, first, splice, take, Nat.zero_le, dite_true]
  · unfold Shortest
    rw [hlength, hrend]
    exact hq

/-- Opposite-parity shortest paths account exactly for the endpoint tenacity. -/
theorem opposite_shortest_tenacity (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hend : p.last = q.last) (hp0 : p.length % 2 = 0) (hq1 : q.length % 2 = 1) :
    tenacity M p.last = some (p.length + q.length) := by
  have he : evenlevel M p.last = some p.length :=
    (level_eq_some_iff M 0 p.last p.length).2 (by simpa only [Shortest, hp0] using hp)
  have ho : oddlevel M p.last = some q.length :=
    (level_eq_some_iff M 1 p.last q.length).2 (by simpa only [Shortest, hq1, hend] using hq)
  simp only [tenacity, he, ho, levelAdd]

end AltPath

variable {V : Type} {G : Graph V}

/-- A globally shortest parity path from the specified free root. -/
def RootedShortest (M : Matching G) (parity : Nat) (f v : V) : Prop :=
  ∃ p : AltPath M, p.first = f ∧ p.last = v ∧ p.Shortest ∧ p.length % 2 = parity

/-- Lemma 6.9: for an eligible-tenacity vertex, each free root supplies shortest
paths of both parities or of neither parity. -/
theorem rooted_shortest_even_iff_odd (M : Matching G) (t : Nat)
    (ht : EligibleTenacity M t) (v : V) (hvt : tenacity M v = some t) (f : V) :
    RootedShortest M 0 f v ↔ RootedShortest M 1 f v := by
  have hlevels : ∃ e o, evenlevel M v = some e ∧ oddlevel M v = some o ∧ e + o = t := by
    unfold tenacity at hvt
    cases he : evenlevel M v with
    | none => simp [he, levelAdd] at hvt
    | some e =>
      cases ho : oddlevel M v with
      | none => simp [he, ho, levelAdd] at hvt
      | some o =>
        have hsum : e + o = t := by simpa [he, ho, levelAdd] using hvt
        exact ⟨e, o, rfl, rfl, hsum⟩
  obtain ⟨e, o, he, ho, hsum⟩ := hlevels
  have hes := (level_eq_some_iff M 0 v e).1 he
  have hos := (level_eq_some_iff M 1 v o).1 ho
  constructor
  · rintro ⟨p, hpf, hpv, hp, hp0⟩
    obtain ⟨q, hqv, hql, hq1⟩ := hos.1
    have hq : q.Shortest := by simpa only [AltPath.Shortest, hql, hqv, hq1] using hos
    have htlen := p.opposite_shortest_tenacity q hp hq (hpv.trans hqv.symm) hp0 (by omega)
    have hsum' : p.length + q.length = t := by rw [hpv, hvt] at htlen; exact (Option.some.inj htlen).symm
    obtain ⟨r, hrf, hrv, hrl, hrs⟩ := p.shortest_root_transfer q hp hq
      (hpv.trans hqv.symm) (by intro r hr; rw [hsum']; exact ht.2.2 r hr)
    exact ⟨r, hrf.trans hpf, hrv.trans hqv, hrs, by omega⟩
  · rintro ⟨p, hpf, hpv, hp, hp1⟩
    obtain ⟨q, hqv, hql, hq0⟩ := hes.1
    have hq : q.Shortest := by simpa only [AltPath.Shortest, hql, hqv, hq0] using hes
    have htlen := q.opposite_shortest_tenacity p hq hp (hqv.trans hpv.symm) (by omega) hp1
    have hsum' : p.length + q.length = t := by
      rw [hqv, hvt] at htlen
      have := Option.some.inj htlen
      omega
    obtain ⟨r, hrf, hrv, hrl, hrs⟩ := p.shortest_root_transfer q hp hq
      (hpv.trans hqv.symm) (by intro r hr; rw [hsum']; exact ht.2.2 r hr)
    exact ⟨r, hrf.trans hpf, hrv.trans hqv, hrs, by omega⟩
end MaximumMatching
