import MaximumMatching.BlossomStructure
import MaximumMatching.MinimumBaseStructure
import MaximumMatching.RelativePaths

section GeneralSuffix

/-! Tenacity bounds on the suffix of a long even shortest path, without a global
minimum-tenacity assumption. The proof constructs both parity witnesses using
the proved simple first-hit splice, then bounds their semantic minima. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Two opposite-parity path witnesses bound the finite vertex tenacity by
the sum of their lengths. -/
theorem tenacity_bound_of_opposite_witnesses (v : V) (i k : Nat)
    (hi : HasPathLength M (i % 2) v i)
    (hk : HasPathLength M ((i + 1) % 2) v k) :
    ∃ t, tenacity M v = some t ∧ t ≤ i + k := by
  have finite_bound (parity len : Nat) (h : HasPathLength M parity v len) :
      ∃ a, level M parity v = some a ∧ a ≤ len := by
    cases ha : level M parity v with
    | none => exact False.elim ((level_eq_none_iff M parity v).1 ha ⟨len, h⟩)
    | some a => exact ⟨a, rfl, ((level_eq_some_iff M parity v a).1 ha).2 len h⟩
  obtain ⟨a, ha, hai⟩ := finite_bound (i % 2) i hi
  obtain ⟨b, hb, hbk⟩ := finite_bound ((i + 1) % 2) k hk
  by_cases hie : i % 2 = 0
  · have hio : (i + 1) % 2 = 1 := by omega
    refine ⟨a + b, ?_, by omega⟩
    simpa only [tenacity, evenlevel, oddlevel, hie, hio, levelAdd] using
      (show levelAdd (level M (i % 2) v) (level M ((i + 1) % 2) v) = some (a + b) by rw [ha, hb]; rfl)
  · have hio : i % 2 = 1 := by omega
    have hie' : (i + 1) % 2 = 0 := by omega
    refine ⟨b + a, ?_, by omega⟩
    simpa only [tenacity, evenlevel, oddlevel, hio, hie', levelAdd] using
      (show levelAdd (level M ((i + 1) % 2) v) (level M (i % 2) v) = some (b + a) by rw [hb, ha]; rfl)

namespace AltPath

/-- After the short path's length, vertex tenacity is finite and no greater
than the sum of the two endpoint path lengths. Only the long path needs to
be shortest; the short path supplies an actual opposite-parity witness. -/
theorem tenacity_bound_beyond_shorter (p q : AltPath M) (hp : p.Shortest)
    (hpe : p.length % 2 = 0) (hend : q.last = p.last)
    (hinner : q.length < p.length) (i : Fin (p.length + 1))
    (hi : q.length < i.val) :
    ∃ t, tenacity M (p.vertex i) = some t ∧ t ≤ p.length + q.length := by
  obtain ⟨k, hk, hkt⟩ := p.beyond_shorter_opposite q hp hpe hend hinner i hi
  obtain ⟨t, ht, hti⟩ := tenacity_bound_of_opposite_witnesses (p.vertex i) i.val k
    (p.prefix_witness i) hk
  exact ⟨t, ht, by omega⟩

/-- The tenacity bound extends to the boundary index, which is odd and paired
with its successor. This includes every vertex from the short path's length. -/
theorem tenacity_bound_suffix (p q : AltPath M) (hp : p.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (i : Fin (p.length + 1)) (hi : q.length ≤ i.val) :
    ∃ t, tenacity M (p.vertex i) = some t ∧ t ≤ p.length + q.length := by
  by_cases hlt : q.length < i.val
  · exact p.tenacity_bound_beyond_shorter q hp hpe hend hinner i hlt
  · have he : i.val = q.length := by omega
    have hmatch := p.mate_next i.val (by omega) (by omega)
    obtain ⟨t, ht, htb⟩ := p.tenacity_bound_beyond_shorter q hp hpe hend hinner
      ⟨i.val + 1, by omega⟩ (by change q.length < i.val + 1; omega)
    exact ⟨t, (matched_tenacity M hmatch).1.trans ht, htb⟩

/-- No suffix vertex is above the endpoint path-length sum in tenacity. For
opposite shortest endpoint paths this sum is exactly the endpoint's tenacity. -/
theorem suffix_not_high_tenacity (p q : AltPath M) (hp : p.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (i : Fin (p.length + 1)) (hi : q.length ≤ i.val) :
    ¬ levelLT (some (p.length + q.length)) (tenacity M (p.vertex i)) := by
  obtain ⟨t, ht, htb⟩ := p.tenacity_bound_suffix q hp hpe hqo hend hinner i hi
  rw [ht]
  change ¬ p.length + q.length < t
  omega

end AltPath
end MaximumMatching

end GeneralSuffix

section GeneralBaseStep

/-! A general-tenacity common-base step that needs no global minimum premise.
The lower-tenacity predecessor case is completed in GeneralStructureStep. -/
namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A predecessor above the endpoint tenacity must occur on every even shortest
path to that inner endpoint; otherwise its fresh extension supplies an opposite
path with tenacity at most the endpoint's. -/
theorem high_predecessor_occurs (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last)
    (hhigh : levelLT (some (p.length + q.length))
      (tenacity M (q.vertex ⟨q.length - 1, by omega⟩))) :
    ∃ i : Fin (p.length + 1), p.vertex i = q.vertex ⟨q.length - 1, by omega⟩ ∧
      i.val = q.length - 1 := by
  classical
  let u := q.vertex ⟨q.length - 1, by omega⟩
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hqten : tenacity M q.last = some (p.length + q.length) := by rw [hend]; exact hten
  have hum : minlevel M u = some (q.length - 1) := by
    exact (q.limited_bfs_honesty hq ⟨q.length - 1, by omega⟩ (by
      rw [hqten]; exact levelLT_le hhigh)).2 (by rw [hqten]; exact hhigh)
  have hon : ∃ i : Fin (p.length + 1), p.vertex i = u := by
    by_cases hon : ∃ i : Fin (p.length + 1), p.vertex i = u
    · exact hon
    apply False.elim
    have hfresh : ∀ i, p.vertex i ≠ u := by intro i hi; exact hon ⟨i, hi⟩
    have hadj : G.Adj p.last u := by
      rw [← hend]
      have he : q.length - 1 + 1 = q.length := by omega
      simpa only [he, last, u] using G.symm (q.adjacent ⟨q.length - 1, by omega⟩)
    let r := p.append u hfresh hadj (p.inner_predecessor_append_parity q hpe hqo hend)
    have hw0 : HasPathLength M ((q.length - 1) % 2) u (q.length - 1) :=
      q.prefix_witness ⟨q.length - 1, by omega⟩
    have hw1 : HasPathLength M ((q.length - 1 + 1) % 2) u (p.length + 1) :=
      ⟨r, append_last _ _ _ _ _, rfl, by omega⟩
    obtain ⟨s, hs, hsb⟩ := tenacity_bound_of_opposite_witnesses u (q.length - 1) (p.length + 1) hw0 hw1
    have hh : levelLT (some (p.length + q.length)) (tenacity M u) := hhigh
    have ht : p.length + q.length < s := by simpa only [hs, levelLT] using hh
    omega
  obtain ⟨i, hi⟩ := hon
  have him : minlevel M (p.vertex i) = some i.val :=
    (p.limited_bfs_honesty hp i (by rw [hten, hi]; exact levelLT_le hhigh)).2
      (by rw [hten, hi]; exact hhigh)
  rw [hi] at him
  exact ⟨i, hi, Option.some.inj (him.symm.trans hum)⟩

/-- When the last predecessor of an odd minlevel path has tenacity greater than
the endpoint's, it is the base on both parity paths. All later vertices on the
even path are bounded by `GeneralSuffix`, without any minimum-tenacity premise. -/
theorem high_predecessor_bases (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (hhigh : levelLT (some (p.length + q.length))
      (tenacity M (q.vertex ⟨q.length - 1, by omega⟩))) :
    p.BaseOnPath (p.length + q.length) (q.vertex ⟨q.length - 1, by omega⟩) ∧
      q.BaseOnPath (p.length + q.length) (q.vertex ⟨q.length - 1, by omega⟩) := by
  obtain ⟨i, hi, hil⟩ := p.high_predecessor_occurs q hp hq hpe hqo hend hhigh
  constructor
  · refine ⟨i, hi, hhigh, ?_⟩
    intro j hj
    exact p.suffix_not_high_tenacity q hp hpe hqo hend hinner j (by omega)
  · refine ⟨⟨q.length - 1, by omega⟩, rfl, hhigh, ?_⟩
    intro j hj
    have he : j = ⟨q.length, by omega⟩ := Fin.ext (by
      change j.val = q.length
      change q.length - 1 < j.val at hj
      omega)
    rw [he]
    change ¬levelLT (some (p.length + q.length)) (tenacity M q.last)
    have ht := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
    rw [hend, ht]
    change ¬ p.length + q.length < p.length + q.length
    omega

end AltPath
end MaximumMatching

end GeneralBaseStep

section GeneralBaseEqual

/-! The equal-tenacity predecessor case of the general common-base induction.
Only the predecessor's tenacity is constrained; lower-tenacity vertices elsewhere
in either path are allowed. -/
namespace MaximumMatching
namespace AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

/-- At an inner endpoint, an equal-tenacity predecessor has evenlevel `O-1`
and oddlevel `E+1`, where `E` and `O` are the endpoint's shortest levels. -/
theorem equal_predecessor_levels (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (hu : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) = some (p.length + q.length)) :
    evenlevel M (q.vertex ⟨q.length - 1, by omega⟩) = some (q.length - 1) ∧
      oddlevel M (q.vertex ⟨q.length - 1, by omega⟩) = some (p.length + 1) ∧
      minlevel M (q.vertex ⟨q.length - 1, by omega⟩) = some (q.length - 1) := by
  let u := q.vertex ⟨q.length - 1, by omega⟩
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hqten : tenacity M q.last = some (p.length + q.length) := by rw [hend]; exact hten
  have hqh := (q.honest_iff_level ⟨q.length - 1, by omega⟩).1
    (q.limited_bfs_honesty hq _ (by rw [hqten, hu]; change _ ≤ _; omega)).1
  have hue : evenlevel M u = some (q.length - 1) := by
    simpa only [show (q.length - 1) % 2 = 0 by omega] using hqh
  have huo : oddlevel M u = some (p.length + 1) := by
    change tenacity M u = _ at hu
    unfold tenacity at hu
    rw [hue] at hu
    cases ho : oddlevel M u with
    | none => simp only [ho, levelAdd] at hu; contradiction
    | some k =>
      have hk : q.length - 1 + k = p.length + q.length := by
        simpa only [ho, levelAdd, Option.some.injEq] using hu
      exact congrArg some (by omega)
  refine ⟨hue, huo, ?_⟩
  change minlevel M u = some (q.length - 1)
  simp only [minlevel, hue, huo, levelMin]
  exact congrArg some (Nat.min_eq_left (by omega))

/-- An equal-tenacity predecessor occurring on the even shortest path occurs
at its honest evenlevel index. No minimum-tenacity assumption is needed. -/
theorem equal_predecessor_index (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (hu : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) = some (p.length + q.length))
    (i : Fin (p.length + 1))
    (hi : p.vertex i = q.vertex ⟨q.length - 1, by omega⟩) : i.val = q.length - 1 := by
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  obtain ⟨hue, huo, _⟩ := p.equal_predecessor_levels q hp hq hpe hqo hend hinner hu
  have hph := (p.honest_iff_level i).1
    (p.limited_bfs_honesty hp i (by rw [hten, hi, hu]; change _ ≤ _; omega)).1
  rw [hi] at hph
  by_cases hie : i.val % 2 = 0
  · rw [hie] at hph
    exact Option.some.inj (hph.symm.trans hue)
  · have hio : i.val % 2 = 1 := by omega
    rw [hio] at hph
    have he := Option.some.inj (hph.symm.trans huo)
    omega

/-- If the equal-tenacity predecessor is absent, extending the even shortest
path by its edge to the endpoint gives an actual odd shortest path to it. -/
theorem equal_predecessor_extension_shortest (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (hu : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) = some (p.length + q.length))
    (hfresh : ∀ i, p.vertex i ≠ q.vertex ⟨q.length - 1, by omega⟩)
    (ha : G.Adj p.last (q.vertex ⟨q.length - 1, by omega⟩)) :
    (p.append _ hfresh ha (p.inner_predecessor_append_parity q hpe hqo hend)).Shortest := by
  have huo := (p.equal_predecessor_levels q hp hq hpe hqo hend hinner hu).2.1
  unfold Shortest
  rw [append_length, show (p.length + 1) % 2 = 1 by omega, append_last]
  exact (level_eq_some_iff M 1 _ (p.length + 1)).1 huo

/-- The equal-tenacity predecessor transfers its proved common base to both
shortest paths of the inner endpoint, even in the presence of lower blossoms. -/
theorem equal_predecessor_parity_bases_agree (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (hu : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) = some (p.length + q.length))
    (hub : HasUniqueBase M (q.vertex ⟨q.length - 1, by omega⟩) (p.length + q.length))
    (b : V) :
    p.BaseOnPath (p.length + q.length) b ↔ q.BaseOnPath (p.length + q.length) b := by
  classical
  let u := q.vertex ⟨q.length - 1, by omega⟩
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hqten : tenacity M q.last = some (p.length + q.length) := by rw [hend]; exact hten
  obtain ⟨hue, _, _⟩ := p.equal_predecessor_levels q hp hq hpe hqo hend hinner hu
  have hqprefix : (q.take (q.length - 1) (by omega)).Shortest := by
    unfold Shortest
    rw [take_length, take_last, show (q.length - 1) % 2 = 0 by omega]
    exact (level_eq_some_iff M 0 u (q.length - 1)).1 hue
  obtain ⟨c, hc, _⟩ := hub
  have hqc := hc (q.take (q.length - 1) (by omega)) rfl hqprefix
  have hqc' := (q.baseOnPath_take_pred_iff (by omega) _ hqten c).1 hqc
  have hpc : p.BaseOnPath (p.length + q.length) c := by
    by_cases hon : ∃ i : Fin (p.length + 1), p.vertex i = u
    · obtain ⟨i, hi⟩ := hon
      have hid := p.equal_predecessor_index q hp hq hpe hqo hend hinner hu i hi
      have hpu : p.vertex ⟨q.length - 1, by omega⟩ = u := by
        have hie : i = ⟨q.length - 1, by omega⟩ := Fin.ext hid
        simpa only [hie] using hi
      have hpprefix : (p.take (q.length - 1) (by omega)).Shortest := by
        unfold Shortest
        rw [take_length, take_last, show (q.length - 1) % 2 = 0 by omega, hpu]
        exact (level_eq_some_iff M 0 u (q.length - 1)).1 hue
      have hpc := hc (p.take (q.length - 1) (by omega)) hpu hpprefix
      apply ((p.take (q.length - 1) (by omega)).baseOnPath_initial_iff p
        (by simp; omega) (by intro j; rfl) _ ?_ c).1 hpc
      intro j hj
      exact p.suffix_not_high_tenacity q hp hpe hqo hend hinner j (by
        change q.length - 1 < j.val at hj
        omega)
    · have hfresh : ∀ i, p.vertex i ≠ u := by intro i he; exact hon ⟨i, he⟩
      have hqa : G.Adj p.last u := by
        have ha := G.symm (q.adjacent ⟨q.length - 1, by omega⟩)
        have he : q.length - 1 + 1 = q.length := by omega
        rw [← hend]
        simpa only [he, last, u] using ha
      let r := p.append u hfresh hqa (p.inner_predecessor_append_parity q hpe hqo hend)
      have hr : r.Shortest := p.equal_predecessor_extension_shortest q hp hq hpe hqo hend hinner hu hfresh hqa
      have hrc := hc r (append_last _ _ _ _ _) hr
      exact (p.baseOnPath_append_low_iff u hfresh hqa
        (p.inner_predecessor_append_parity q hpe hqo hend) _ hu c).2 hrc
  constructor
  · intro hb
    exact (p.baseOnPath_unique _ b c hb hpc).symm ▸ hqc'
  · intro hb
    exact (q.baseOnPath_unique _ b c hb hqc').symm ▸ hpc


/-- All predecessor cases at or above the current tenacity are discharged.
The induction hypothesis is used only at the predecessor's strictly smaller
minimum level; the strictly higher case needs no induction hypothesis. -/
theorem parity_bases_agree_of_predecessor_ge (p q : AltPath M)
    (hp : p.Shortest) (hq : q.Shortest) (hpe : p.length % 2 = 0)
    (hqo : q.length % 2 = 1) (hend : q.last = p.last) (hinner : q.length < p.length)
    (hge : levelLE (some (p.length + q.length))
      (tenacity M (q.vertex ⟨q.length - 1, by omega⟩)))
    (ih : ∀ (u : V) (k : Nat), minlevel M u = some k → k < q.length →
      tenacity M u = some (p.length + q.length) → HasUniqueBase M u (p.length + q.length))
    (b : V) :
    p.BaseOnPath (p.length + q.length) b ↔ q.BaseOnPath (p.length + q.length) b := by
  by_cases heq : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) = some (p.length + q.length)
  · have hmin := (p.equal_predecessor_levels q hp hq hpe hqo hend hinner heq).2.2
    exact p.equal_predecessor_parity_bases_agree q hp hq hpe hqo hend hinner heq
      (ih _ (q.length - 1) hmin (by omega) heq) b
  · have hhigh : levelLT (some (p.length + q.length))
        (tenacity M (q.vertex ⟨q.length - 1, by omega⟩)) := by
      cases hu : tenacity M (q.vertex ⟨q.length - 1, by omega⟩) with
      | none => trivial
      | some s =>
        have hle : p.length + q.length ≤ s := by simpa only [hu, levelLE] using hge
        have hne : s ≠ p.length + q.length := by
          intro h; exact heq (hu.trans (congrArg some h))
        change p.length + q.length < s
        omega
    obtain ⟨hpb, hqb⟩ := p.high_predecessor_bases q hp hq hpe hqo hend hinner hhigh
    constructor
    · intro hb
      exact (p.baseOnPath_unique _ _ _ hb hpb).symm ▸ hqb
    · intro hb
      exact (q.baseOnPath_unique _ _ _ hb hqb).symm ▸ hpb

end AltPath
end MaximumMatching

end GeneralBaseEqual

section GeneralBaseChain

/-! Higher-threshold path-relative bases along established common-base chains.
These lemmas concern the actual partial base relation and do not assume general
base existence or the separate lower-blossom rerouting construction. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- Cutting a shortest path at an actual base preserves all path-relative bases
at every threshold at least the endpoint's tenacity. -/
theorem IsBase.threshold_prefix {v b : V} (hb : IsBase M v b)
    (p : AltPath M) (hpv : p.last = v) (hp : p.Shortest)
    (t : Nat) (hvt : levelLE (tenacity M v) (some t)) :
    ∃ i : Fin (p.length + 1), p.vertex i = b ∧ i.val % 2 = 0 ∧ i.val < p.length ∧
      minlevel M b = some i.val ∧ (p.take i.val (by omega)).Shortest ∧
      ∀ c, p.BaseOnPath t c ↔ (p.take i.val (by omega)).BaseOnPath t c := by
  obtain ⟨i, hi, hie, hilt, himin, hishort⟩ := hb.on_shortest p hpv hp
  obtain ⟨s, hvs, hcommon⟩ := (show IsBase M v b from hb)
  have hst : s ≤ t := by simpa only [hvs, levelLE] using hvt
  obtain ⟨j, hj, _, htail⟩ := hcommon p hpv hp
  have hji : j = i := p.injective j i (hj.trans hi.symm)
  subst j
  refine ⟨i, hi, hie, hilt, himin, hishort, ?_⟩
  intro c
  apply ((p.take i.val (by omega)).baseOnPath_initial_iff p
    (by simp; omega) (by intro k; rfl) t ?_ c).symm
  intro k hk hhigh
  apply htail k hk
  cases hw : tenacity M (p.vertex k) with
  | none => trivial
  | some r =>
    have htr : t < r := by simpa only [hw, levelLT] using hhigh
    change s < r
    omega

/-- Every established chain below a threshold preserves all higher-threshold
base values when a shortest path is cut at its root. The proof also constructs
the actual shortest even prefix at the root. -/
theorem base_cut_threshold_prefix (s t : Nat) (hst : s ≤ t) (b v : V)
    (h : BaseTree.Cut (IsBase M) (tenacity M) s b v)
    (p : AltPath M) (hpv : p.last = v) (hp : p.Shortest) :
    ∃ i : Fin (p.length + 1), p.vertex i = b ∧ i.val % 2 = 0 ∧ i.val < p.length ∧
      minlevel M b = some i.val ∧ (p.take i.val (by omega)).Shortest ∧
      ∀ c, p.BaseOnPath t c ↔ (p.take i.val (by omega)).BaseOnPath t c := by
  have widen : ∀ w, levelLE (tenacity M w) (some s) → levelLE (tenacity M w) (some t) := by
    intro w hw
    cases hten : tenacity M w with
    | none => simp only [hten, levelLE] at hw
    | some r =>
      have hrs : r ≤ s := by simpa only [hten, levelLE] using hw
      change r ≤ t
      omega
  induction h generalizing p with
  | edge hbase hv => exact hbase.threshold_prefix p hpv hp t (widen _ hv)
  | @step v w b hbase hv hchain ih =>
    obtain ⟨j, hj, _, hjlt, _, hjshort, hpreserve⟩ :=
      hbase.threshold_prefix p hpv hp t (widen _ hv)
    obtain ⟨i, hi, hie, hilt, himin, hishort, hipreserve⟩ :=
      ih (p.take j.val (by omega)) hj hjshort
    have hib : i.val < p.length + 1 := by
      change i.val < j.val at hilt
      omega
    refine ⟨⟨i.val, hib⟩, hi, hie, ?_, himin, hishort, ?_⟩
    · change i.val < j.val at hilt
      change i.val < p.length
      omega
    · intro c
      exact (hpreserve c).trans (hipreserve c)

/-- The same prefix-preservation result for the paper's recursive blossoms. -/
theorem blossom_threshold_prefix (s t : Nat) (hst : s ≤ t) (b v : V)
    (h : Blossom M s b v) (p : AltPath M) (hpv : p.last = v) (hp : p.Shortest) :
    ∃ i : Fin (p.length + 1), p.vertex i = b ∧ i.val % 2 = 0 ∧ i.val < p.length ∧
      minlevel M b = some i.val ∧ (p.take i.val (by omega)).Shortest ∧
      ∀ c, p.BaseOnPath t c ↔ (p.take i.val (by omega)).BaseOnPath t c :=
  base_cut_threshold_prefix s t hst b v (blossom_to_cut s b v h) p hpv hp


namespace AltPath

/-- In the low-predecessor case, the odd minlevel path has an actual shortest
prefix to the lower blossom's boundary. Cutting to it preserves all base values
at the endpoint's tenacity and strictly decreases the minimum level. This is the
short-path half of the induction; it does not reroute the opposite even path. -/
theorem predecessor_blossom_prefix (p q : AltPath M) (hp : p.Shortest) (hq : q.Shortest)
    (hpe : p.length % 2 = 0) (hqo : q.length % 2 = 1)
    (hend : q.last = p.last) (hinner : q.length < p.length)
    (c : V) (hc : Blossom M (p.length + q.length - 2) c
      (q.vertex ⟨q.length - 1, by omega⟩)) :
    ∃ r : AltPath M, r.last = c ∧ r.Shortest ∧ r.length % 2 = 0 ∧
      minlevel M c = some r.length ∧ r.length < q.length ∧
      ∀ b, q.BaseOnPath (p.length + q.length) b ↔ r.BaseOnPath (p.length + q.length) b := by
  have hten := p.opposite_shortest_tenacity q hp hq hend.symm hpe hqo
  have hqten : tenacity M q.last = some (p.length + q.length) := by rw [hend]; exact hten
  have he : evenlevel M q.last = some p.length := by
    rw [hend]
    exact (level_eq_some_iff M 0 p.last p.length).2
      (by simpa only [Shortest, hpe] using hp)
  have ho : oddlevel M q.last = some q.length :=
    (level_eq_some_iff M 1 q.last q.length).2 (by simpa only [Shortest, hqo] using hq)
  have hqm : minlevel M q.last = some q.length := by
    simp only [minlevel, he, ho, levelMin]
    exact congrArg some (Nat.min_eq_right (by omega))
  have hqprefix := q.minlevel_predecessor_honest hq hqm (p.length + q.length) hqten
    ⟨q.length - 1, by omega⟩ (by
      have hlast : q.length - 1 + 1 = q.length := by omega
      simp only [hlast]
      change levelLE (some (p.length + q.length)) (tenacity M q.last)
      rw [hqten]
      change _ ≤ _
      omega)
  let r₀ := q.take (q.length - 1) (by omega)
  obtain ⟨i, hi, hie, hilt, himin, hishort, hpreserve⟩ := blossom_threshold_prefix
    (p.length + q.length - 2) (p.length + q.length) (by omega) c
    (q.vertex ⟨q.length - 1, by omega⟩) hc r₀ rfl hqprefix
  refine ⟨r₀.take i.val (by omega), hi, hishort, hie, himin, ?_, ?_⟩
  · change i.val < q.length
    change i.val < q.length - 1 at hilt
    omega
  · intro b
    exact (q.baseOnPath_take_pred_iff (by omega) _ hqten b).symm.trans (hpreserve b)

end AltPath

end MaximumMatching

end GeneralBaseChain

section BlossomRelative

/-! Relative shortest paths through iterated actual bases. These facts apply to
source-recursive blossoms without assuming general base existence or confinement.
They extend the direct-base decomposition to an entire established base chain. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- A blossom boundary is the last vertex above its threshold on every shortest
path to a member. This follows from the actual common-base chain. -/
theorem blossom_baseOnPath (t : Nat) (b v : V) (h : Blossom M t b v)
    (hb : levelLT (some t) (tenacity M b))
    (p : AltPath M) (hpv : p.last = v) (hp : p.Shortest) : p.BaseOnPath t b := by
  obtain ⟨i, hi, _, _, _, _, hpreserve⟩ :=
    blossom_threshold_prefix t t (Nat.le_refl _) b v h p hpv hp
  apply (hpreserve b).2
  refine ⟨⟨i.val, by change i.val < i.val + 1; omega⟩, hi, hb, ?_⟩
  intro j hj
  change i.val < j.val at hj
  have := j.isLt
  change j.val < i.val + 1 at this
  omega

/-- The suffix after an established blossom boundary is shortest among relative
paths of its parity. The opposite global path supplies the length budget. -/
theorem blossom_shortest_relative (t : Nat) (b v : V) (h : Blossom M t b v)
    (hb : levelLT (some t) (tenacity M b))
    (p : AltPath M) (hpv : p.last = v) (hp : p.Shortest) :
    ∃ i : Fin (p.length + 1), ∃ hie : i.val % 2 = 0, p.vertex i = b ∧
      (p.take i.val (by omega)).Shortest ∧
      (p.segment i.val (by omega) hie).Shortest := by
  obtain ⟨s, hvs, hst⟩ := blossom_tenacity_bound t b v h
  obtain ⟨i, hi, hie, _, himin, hip⟩ := blossom_on_shortest t b v h p hpv hp
  obtain ⟨q, hqv, hq, hqpar⟩ := finite_tenacity_shortest_parity v s (p.length + 1) hvs
  obtain ⟨j, _, _, hjlt, hjmin, _⟩ := blossom_on_shortest t b v h q hqv hq
  have hji : j.val = i.val := Option.some.inj (hjmin.symm.trans himin)
  have hsum : p.length + q.length = s := by
    have hten : tenacity M v = some (p.length + q.length) := by
      by_cases hpe : p.length % 2 = 0
      · simpa only [hpv] using p.opposite_shortest_tenacity q hp hq
          (hpv.trans hqv.symm) hpe (by omega)
      · have hqe : q.length % 2 = 0 := by omega
        simpa only [hqv, Nat.add_comm] using q.opposite_shortest_tenacity p hq hp
          (hqv.trans hpv.symm) hqe (by omega)
    exact Option.some.inj (hten.symm.trans hvs)
  refine ⟨i, hie, hi, hip, ?_⟩
  apply p.segment_shortest_of_high hp i hie t
  · exact (level_eq_some_iff M 0 (p.vertex i) i.val).2
      (by simpa only [AltPath.Shortest, AltPath.take_length, AltPath.take_last, hie] using hip)
  · simpa only [hi] using hb
  · omega

/-- Every vertex strictly after the boundary has tenacity at most the blossom
threshold, even when that prefix is not itself shortest. Membership in the
blossom is a stronger statement and is not concluded here. -/
theorem blossom_suffix_tenacity_bound (t : Nat) (b v : V) (h : Blossom M t b v)
    (hb : levelLT (some t) (tenacity M b))
    (p : AltPath M) (hpv : p.last = v) (hp : p.Shortest)
    (i j : Fin (p.length + 1)) (hi : p.vertex i = b) (hij : i.val < j.val) :
    ∃ s, tenacity M (p.vertex j) = some s ∧ s ≤ t := by
  obtain ⟨k, hk, _, htail⟩ := blossom_baseOnPath t b v h hb p hpv hp
  have hik := p.injective i k (hi.trans hk.symm)
  have hn := htail j (by simpa only [hik] using hij)
  cases hs : tenacity M (p.vertex j) with
  | none => exact False.elim (hn (by rw [hs]; trivial))
  | some s =>
    have hn' : ¬t < s := by simpa only [hs, levelLT] using hn
    exact ⟨s, rfl, by omega⟩

end MaximumMatching

end BlossomRelative

section GeneralBlossomJoin

/-! Any shortest relative path to an established blossom member joins to any
shortest even path to its boundary. The actual common-base chain supplies the
length identities; disjointness follows from the boundary's high tenacity. -/
namespace MaximumMatching
variable {V : Type} {G : Graph V} {M : Matching G}

/-- The global parity level equals the boundary's evenlevel plus the shortest
relative length, including blossoms whose member has an iterated base. -/
theorem blossom_relative_length_formula (t : Nat) (b v : V)
    (hv : Blossom M t b v) (hb : levelLT (some t) (tenacity M b))
    (p : AltPath M) (hp : p.Shortest) (hpe : p.length % 2 = 0) (hpb : p.last = b)
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v)
    (τ : Nat) (hvt : tenacity M v = some τ) :
    IsShortest M (q.length % 2) v (p.length + q.length) ∧
      2 * p.length + q.length ≤ τ := by
  have hplevel : evenlevel M b = some p.length :=
    (level_eq_some_iff M 0 b p.length).2 (by simpa only [AltPath.Shortest, hpe, hpb] using hp)
  obtain ⟨r, hrv, hr, hrpar⟩ := finite_tenacity_shortest_parity v τ q.length hvt
  obtain ⟨i, hie, hib, hip, his⟩ := blossom_shortest_relative t b v hv hb r hrv hr
  have hilevel : evenlevel M b = some i.val :=
    (level_eq_some_iff M 0 b i.val).2 (by
      simpa only [AltPath.Shortest, AltPath.take_length, AltPath.take_last, hie, hib] using hip)
  have hilen : i.val = p.length := Option.some.inj (hilevel.symm.trans hplevel)
  let s := r.segment i.val (by omega) hie
  have hsf : s.first = b := (r.segment_first i.val (by omega) hie).trans hib
  have hsl : s.last = v := (r.segment_last i.val (by omega) hie).trans hrv
  have hspar : s.length % 2 = q.length % 2 := by
    change (r.length - i.val) % 2 = q.length % 2
    omega
  have hqs : q.length ≤ s.length := hq s (hsf.trans hqb.symm) (hsl.trans hqv.symm) hspar
  have hsq : s.length ≤ q.length := his q (hqb.trans hsf.symm) (hqv.trans hsl.symm) hspar.symm
  have hqlen : q.length = r.length - i.val := Nat.le_antisymm hqs hsq
  have hrlen : r.length = p.length + q.length := by omega
  have hsumpar : (p.length + q.length) % 2 = q.length % 2 := by omega
  have hshort : IsShortest M (q.length % 2) v (p.length + q.length) := by
    simpa only [AltPath.Shortest, hrv, hrlen, hsumpar] using hr
  refine ⟨hshort, ?_⟩
  obtain ⟨u, huv, hu, hupar⟩ := finite_tenacity_shortest_parity v τ (q.length + 1) hvt
  obtain ⟨j, _, _, hjlt, hjmin, _⟩ := blossom_on_shortest t b v hv u huv hu
  have hpmin : minlevel M b = some p.length := (minlevel_eq_even_of_outer b (blossom_outer t b v hv)).trans hplevel
  have hjlen : j.val = p.length := Option.some.inj (hjmin.symm.trans hpmin)
  have hsum : r.length + u.length = τ := by
    have ht' : tenacity M v = some (r.length + u.length) := by
      by_cases hqeven : q.length % 2 = 0
      · have hre : r.length % 2 = 0 := hrpar.trans hqeven
        have huo : u.length % 2 = 1 := by omega
        have hten := r.opposite_shortest_tenacity u hr hu (hrv.trans huv.symm) hre huo
        simpa only [hrv] using hten
      · have hro : r.length % 2 = 1 := by omega
        have hue : u.length % 2 = 0 := by omega
        have hten := u.opposite_shortest_tenacity r hu hr (huv.trans hrv.symm) hue hro
        simpa only [huv, Nat.add_comm] using hten
    exact Option.some.inj (ht'.symm.trans hvt)
  omega

/-- Any shortest relative path avoids every vertex of any shortest even prefix
to the base, apart from the shared base endpoint. -/
theorem blossom_relative_avoids_prefix (t : Nat) (b v : V)
    (hv : Blossom M t b v) (hb : levelLT (some t) (tenacity M b))
    (p : AltPath M) (hp : p.Shortest) (hpe : p.length % 2 = 0) (hpb : p.last = b)
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v) :
    ∀ (i : Fin (p.length + 1)) (j : Fin (q.length + 1)),
      0 < j.val → p.vertex i ≠ q.vertex j := by
  obtain ⟨s, hvt, hst⟩ := blossom_tenacity_bound t b v hv
  obtain ⟨hshort, hbound⟩ := blossom_relative_length_formula t b v hv hb p hp hpe hpb q hq hqb hqv s hvt
  apply p.segment_avoids_prefix q (hpb.trans hqb.symm) (by simpa only [hqv] using hshort)
    t ?_ ?_ (by omega)
  · exact (level_eq_some_iff M 0 p.last p.length).2
      (by simpa only [AltPath.Shortest, hpe] using hp)
  · rw [hpb]
    exact hb

/-- Proposition 6.17 in the joining direction: the actual concatenation of
arbitrary shortest component paths is a shortest global alternating path.
Disjointness comes from `relative_avoids_prefix`, not from the caller. -/
theorem blossom_append_relative_shortest (t : Nat) (b v : V)
    (hv : Blossom M t b v) (hb : levelLT (some t) (tenacity M b))
    (p : AltPath M) (hp : p.Shortest) (hpe : p.length % 2 = 0) (hpb : p.last = b)
    (q : AltSegment M) (hq : q.Shortest) (hqb : q.first = b) (hqv : q.last = v) :
    (p.appendSegment q hpe (hpb.trans hqb.symm)
      (blossom_relative_avoids_prefix t b v hv hb p hp hpe hpb q hq hqb hqv)).Shortest := by
  obtain ⟨s, hvt, hst⟩ := blossom_tenacity_bound t b v hv
  have hshort := (blossom_relative_length_formula t b v hv hb p hp hpe hpb q hq hqb hqv s hvt).1
  have hpar : (p.length + q.length) % 2 = q.length % 2 := by omega
  simpa only [AltPath.Shortest, AltPath.appendSegment_length, AltPath.appendSegment_last,
    hqv, hpar] using hshort


end MaximumMatching

end GeneralBlossomJoin

section GeneralBlossomMembership

/-! Identify the blossom of an endpoint from the actual boundary on one
shortest path, once bases exist up to the cutoff. -/
namespace MaximumMatching.AltPath
variable {V : Type} {G : Graph V} {M : Matching G}

theorem blossom_of_shortest_base (p : AltPath M) (hp : p.Shortest)
    (t : Nat) (ht : t % 2 = 1)
    (hexists : ∀ (v : V) (s : Nat), tenacity M v = some s → s ≤ t → ∃ b, IsBase M v b)
    (b : V) (hb : p.BaseOnPath t b) (hv : levelLE (tenacity M p.last) (some t)) :
    Blossom M t b p.last := by
  have hfinite : ∃ s, tenacity M p.last = some s ∧ s ≤ t := by
    cases hs : tenacity M p.last with
    | none => simp only [hs, levelLE] at hv
    | some s => exact ⟨s, rfl, by simpa only [hs, levelLE] using hv⟩
  obtain ⟨s, hs, hst⟩ := hfinite
  obtain ⟨c, hc, hmem⟩ := blossom_cover_of_base_existence t ht hexists p.last s hs hst
  have hcb := p.baseOnPath_unique t c b (blossom_baseOnPath t c p.last hmem hc p rfl hp) hb
  exact hcb ▸ hmem

end MaximumMatching.AltPath

end GeneralBlossomMembership
