import MaximumMatching.BasePaths
import MaximumMatching.GeneralBaseEqual
import MaximumMatching.PredecessorHonesty

/-! Higher-threshold path-relative bases along established common-base chains.
These lemmas concern the actual partial base relation and do not assume general
base existence or the missing lower-blossom rerouting construction. -/
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
