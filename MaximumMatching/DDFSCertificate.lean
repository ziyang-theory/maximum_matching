import MaximumMatching.DDFSPaths

/-! A two-path/dominator theorem for strictly layered directed graphs, proved by
induction on root layers. It is independent of an operational DDFS implementation. -/
namespace MaximumMatching.DDFS
variable {V : Type} (H : LayeredGraph V)

def Reaches (T : V → Prop) (r : V) : Prop := ∃ p : Path H, p.To T r

def Dominates (T : V → Prop) (r b : V) : Prop :=
  ∀ p : Path H, p.To T r → p.Contains b

def CommonDominator (T : V → Prop) (r g b : V) : Prop :=
  Dominates H T r b ∧ Dominates H T g b

def DisjointTo (T : V → Prop) (r g : V) : Prop :=
  ∃ p q : Path H, p.To T r ∧ q.To T g ∧ p.Disjoint q

theorem dominates_trans (T : V → Prop) (r c b : V)
    (hc : Dominates H T r c) (hb : Dominates H T c b) : Dominates H T r b := by
  intro p hp
  obtain ⟨i, hi⟩ := hc p hp
  have htail : (p.drop i.val (by omega)).To T c := by
    refine ⟨?_, ?_⟩
    · simpa using hi
    · simpa using hp.2
  exact p.contains_drop i.val (by omega) (hb _ htail)

/-- Dominators of one root are ordered by their layers: a lower one also
dominates every terminal continuation from a higher one. -/
theorem dominates_below (T : V → Prop) (g b c : V)
    (hg : Reaches H T g) (hb : Dominates H T g b) (hc : Dominates H T g c)
    (hl : H.level b ≤ H.level c) : Dominates H T c b := by
  obtain ⟨s, hs⟩ := hg
  obtain ⟨i, hi⟩ := hc s hs
  intro q hq
  let a := s.take i.val (by omega)
  have hj : a.last = q.first := by
    change s.vertex ⟨i.val, by omega⟩ = q.first
    rw [hi, hq.1]
  have hall : (a.append q hj).To T g := by
    exact ⟨by simpa [a] using hs.1, by simpa using hq.2⟩
  have hhit := (a.contains_append_iff q hj b).1 (hb _ hall)
  rcases hhit with ha | hqb
  · have hcl : H.level c ≤ H.level b := by
      have h := a.last_level_le ha
      simpa only [hj, hq.1] using h
    have hbc : b = c := by
      have h := a.eq_of_contains_level_eq ha a.contains_last (by rw [hj, hq.1]; omega)
      simpa only [hj, hq.1] using h
    rw [hbc, ← hq.1]
    exact q.contains_first
  · exact hqb

theorem disjointTo_symm (T : V → Prop) (r g : V) :
    DisjointTo H T r g → DisjointTo H T g r := by
  rintro ⟨p, q, hp, hq, hd⟩
  exact ⟨q, p, hq, hp, Path.disjoint_symm hd⟩

private theorem exists_minimum (P : Nat → Prop) (hex : ∃ k, P k) :
    ∃ k, P k ∧ ∀ j, P j → k ≤ j := by
  classical
  obtain ⟨k, hk⟩ := hex
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases h : ∃ j, j < k ∧ P j
    · obtain ⟨j, hj, hp⟩ := h
      exact ih j hj hp
    · exact ⟨k, hk, fun j hp => Nat.le_of_not_lt (fun hj => h ⟨j, hj, hp⟩)⟩

/-- Two reachable roots admit disjoint terminal paths, or all such paths from
both roots contain a common vertex. No Menger theorem is assumed. -/
theorem two_path_dichotomy (T : V → Prop) (r g : V)
    (hr : Reaches H T r) (hg : Reaches H T g) :
    DisjointTo H T r g ∨ ∃ b, CommonDominator H T r g b := by
  classical
  have aux : ∀ n : Nat, ∀ r g : V, H.level r + H.level g = n →
      Reaches H T r → Reaches H T g →
      DisjointTo H T r g ∨ ∃ b, CommonDominator H T r g b := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      have ordered (r g : V) (hsum : H.level r + H.level g = n)
          (hle : H.level g ≤ H.level r) (hr : Reaches H T r) (hg : Reaches H T g) :
          DisjointTo H T r g ∨ ∃ b, CommonDominator H T r g b := by
        by_cases heq : r = g
        · right
          refine ⟨r, ?_, ?_⟩
          · intro p hp; rw [← hp.1]; exact p.contains_first
          · intro p hp; rw [heq, ← hp.1]; exact p.contains_first
        have hnot (q : Path H) (hq : q.To T g) : ¬ q.Contains r := by
          intro hqr
          have hrg := q.contains_eq_first_of_level_ge hqr (by rw [hq.1]; exact hle)
          exact heq (hrg.trans hq.1)
        by_cases hrt : T r
        · left
          obtain ⟨q, hq⟩ := hg
          refine ⟨Path.trivial H r, q, ⟨rfl, hrt⟩, hq, ?_⟩
          intro v hv hqv
          obtain ⟨i, hi⟩ := hv
          have hrv : r = v := hi
          apply hnot q hq
          rw [hrv]
          exact hqv
        by_cases hdis : DisjointTo H T r g
        · exact Or.inl hdis
        have hsucc : ∀ x, H.Edge r x → Reaches H T x →
            ∃ b, CommonDominator H T x g b := by
          intro x hex hx
          have hdecr := H.decreases hex
          rcases ih (H.level x + H.level g) (by omega) x g rfl hx hg with hd | hb
          · obtain ⟨p, q, hp, hq, hpq⟩ := hd
            have he : H.Edge r p.first := by rw [hp.1]; exact hex
            apply False.elim
            apply hdis
            refine ⟨Path.prepend r p he, q, ⟨rfl, by simpa using hp.2⟩, hq, ?_⟩
            intro v hv hqv
            rcases (Path.contains_prepend_iff r p he v).1 hv with hv | hv
            · subst v; exact hnot q hq hqv
            · exact hpq v hv hqv
          · exact hb
        have hexist : ∃ k, ∃ b, H.level b = k ∧ ∃ x,
            H.Edge r x ∧ Reaches H T x ∧ CommonDominator H T x g b := by
          obtain ⟨p, hp⟩ := hr
          have hpos : 0 < p.length := by
            by_cases hz : p.length = 0
            · have he : p.first = p.last := congrArg p.vertex (Fin.ext (by omega))
              exact False.elim (hrt (by rw [← hp.1, he]; exact hp.2))
            · omega
          let x := p.vertex ⟨1, by omega⟩
          have hx : Reaches H T x := ⟨p.drop 1 (by omega), by simp [Path.To, x, hp.2]⟩
          have he : H.Edge r x := by
            have h := p.adjacent ⟨0, hpos⟩
            change H.Edge p.first x at h
            rwa [hp.1] at h
          obtain ⟨b, hb⟩ := hsucc x he hx
          exact ⟨H.level b, b, rfl, x, he, hx, hb⟩
        obtain ⟨k, ⟨b, hbk, x, hex, hx, hxb⟩, hmin⟩ := exists_minimum _ hexist
        right
        refine ⟨b, ?_, hxb.2⟩
        intro p hp
        have hpos : 0 < p.length := by
          by_cases hz : p.length = 0
          · have he : p.first = p.last := congrArg p.vertex (Fin.ext (by omega))
            exact False.elim (hrt (by rw [← hp.1, he]; exact hp.2))
          · omega
        let y := p.vertex ⟨1, by omega⟩
        have hy : Reaches H T y := ⟨p.drop 1 (by omega), by simp [Path.To, y, hp.2]⟩
        have he : H.Edge r y := by
          have h := p.adjacent ⟨0, hpos⟩
          change H.Edge p.first y at h
          rwa [hp.1] at h
        obtain ⟨c, hc⟩ := hsucc y he hy
        have hbc : H.level b ≤ H.level c := by
          rw [hbk]
          exact hmin (H.level c) ⟨c, rfl, y, he, hy, hc⟩
        have hcb := dominates_below H T g b c hg hxb.2 hc.2 hbc
        have hyb := dominates_trans H T y c b hc.1 hcb
        exact p.contains_drop 1 (by omega) (hyb _ (by simp [Path.To, y, hp.2]))
      intro r g hsum hr hg
      by_cases hle : H.level g ≤ H.level r
      · exact ordered r g hsum hle hr hg
      · rcases ordered g r (by omega) (by omega) hg hr with hd | ⟨b, hb⟩
        · exact Or.inl (disjointTo_symm H T g r hd)
        · exact Or.inr ⟨b, hb.2, hb.1⟩
  exact aux (H.level r + H.level g) r g rfl hr hg

/-- The graph-theoretic two outcomes of DDFS, without any operational machine
premise: either disjoint root-to-bottom paths or a highest bottleneck. -/
theorem bottom_dichotomy (r g : V)
    (hr : ∃ p : Path H, p.ToBottom r) (hg : ∃ q : Path H, q.ToBottom g) :
    (∃ p q : Path H, p.ToBottom r ∧ q.ToBottom g ∧ p.Disjoint q) ∨
      ∃ b, HighestBottleneck H r g b := by
  rcases two_path_dichotomy H (fun v => H.level v = 0) r g hr hg with hd | ⟨b, hb⟩
  · exact Or.inl hd
  · right
    apply highestBottleneck_exists H r g hr
    refine ⟨b, ?_⟩
    intro p hp
    rcases hp with hp | hp
    · exact hb.1 p hp
    · exact hb.2 p hp

/-- Two vertex-disjoint directed paths, with specified roots and endpoints. -/
def Linkage (r g a b : V) : Prop :=
  ∃ p q : Path H, p.first = r ∧ p.last = a ∧
    q.first = g ∧ q.last = b ∧ p.Disjoint q

/-- The per-vertex certificate above a highest bottleneck. A vertex `w` reachable
from either root and strictly above `b` can be linked to one root while the other
root is linked disjointly to `b`. The orientation may depend on `w`.

This proves the existence used in Lemma 6.13 Claim 4; it does not assert that an
operational DDFS machine computes a globally consistent coloring or search trees. -/
theorem highestBottleneck_certificate (r g b w : V)
    (hr : ∃ p : Path H, p.ToBottom r) (hg : ∃ q : Path H, q.ToBottom g)
    (hb : HighestBottleneck H r g b) (hw : H.level b < H.level w)
    (a : Path H) (ha : a.first = r ∨ a.first = g) (haw : a.last = w) :
    Linkage H r g w b ∨ Linkage H g r w b := by
  let T : V → Prop := fun v => v = w ∨ v = b
  have reachesT (u : V) (hu : u = r ∨ u = g)
      (hre : ∃ p : Path H, p.ToBottom u) : Reaches H T u := by
    obtain ⟨p, hp⟩ := hre
    have hpRG : p.ToBottom r ∨ p.ToBottom g := by
      rcases hu with rfl | rfl
      · exact Or.inl hp
      · exact Or.inr hp
    obtain ⟨i, hi⟩ := hb.1 p hpRG
    refine ⟨p.take i.val (by omega), ?_, ?_⟩
    · simpa using hp.1
    · exact Or.inr (by simpa using hi)
  have hrT := reachesT r (Or.inl rfl) hr
  have hgT := reachesT g (Or.inr rfl) hg
  rcases two_path_dichotomy H T r g hrT hgT with hd | ⟨c, hc⟩
  · obtain ⟨p, q, hp, hq, hpq⟩ := hd
    have hend := disjoint_paths_distinct_bottoms H p q hpq
    rcases hp.2 with hpw | hpb
    · rcases hq.2 with hqw | hqb
      · exact False.elim (hend (hpw.trans hqw.symm))
      · exact Or.inl ⟨p, q, hp.1, hpw, hq.1, hqb, hpq⟩
    · rcases hq.2 with hqw | hqb
      · exact Or.inr ⟨q, p, hq.1, hqw, hp.1, hpb, Path.disjoint_symm hpq⟩
      · exact False.elim (hend (hpb.trans hqb.symm))
  · have hcb : Bottleneck H r g c := by
      intro p hp
      obtain ⟨i, hi⟩ := hb.1 p hp
      let q := p.take i.val (by omega)
      have hqt : T q.last := Or.inr (by simpa [q] using hi)
      have hhit : q.Contains c := by
        rcases hp with hp | hp
        · exact hc.1 q ⟨by simpa [q] using hp.1, hqt⟩
        · exact hc.2 q ⟨by simpa [q] using hp.1, hqt⟩
      exact p.contains_take i.val (by omega) hhit
    have hcbelow := hb.2 c hcb
    have hca : a.Contains c := by
      rcases ha with har | hag
      · exact hc.1 a ⟨har, Or.inl haw⟩
      · exact hc.2 a ⟨hag, Or.inl haw⟩
    have hwbelow := a.last_level_le hca
    rw [haw] at hwbelow
    omega

end MaximumMatching.DDFS
