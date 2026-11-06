import MaximumMatching.DDFSExecutable

/-! Global colored spanning trees reconstructed from the actual bottleneck
output. Parent functions provide globally consistent ancestry. -/
namespace MaximumMatching.DDFS
variable {V : Type} {H : LayeredGraph V}

/-- Following a unique-parent map forward from its root. -/
inductive ParentReach (parent : V → Option V) (root : V) : V → Prop where
  | root : ParentReach parent root root
  | step {u v} : ParentReach parent root u → parent v = some u → ParentReach parent root v

theorem ParentReach.mono {p q : V → Option V} {r v : V}
    (h : ParentReach p r v) (hm : ∀ u w, p w = some u → q w = some u) : ParentReach q r v := by
  induction h with
  | root => exact .root
  | step _ hp ih => exact .step ih (hm _ _ hp)

/-- A directed rooted spanning tree, represented by one parent per non-root.
Reachability of every domain vertex is derived in construction, not assumed of
an unknown search output. -/
structure RootedTree (H : LayeredGraph V) (root : V) (S : V → Prop) where
  parent : V → Option V
  root_none : parent root = none
  edge : ∀ u v, parent v = some u → S u ∧ S v ∧ H.Edge u v
  spanning : ∀ v, S v → ParentReach parent root v

namespace RootedTree

theorem path (T : RootedTree H root S) (v : V) (hv : S v) :
    ∃ p : Path H, p.first = root ∧ p.last = v ∧
      ∀ i : Fin p.length, T.parent (p.vertex ⟨i.val + 1, by omega⟩) =
        some (p.vertex ⟨i.val, by omega⟩) := by
  have hr := T.spanning v hv
  induction hr with
  | root => exact ⟨Path.trivial H root, rfl, rfl, fun i => Fin.elim0 i⟩
  | @step u v _ hp ih =>
    obtain ⟨p, hpr, hpu, hpe⟩ := ih (T.edge u v hp).1
    have he : H.Edge p.last v := hpu ▸ (T.edge u v hp).2.2
    refine ⟨p.snoc v he, by simpa using hpr, by simp, ?_⟩
    intro i
    by_cases hi : i.val < p.length
    · simpa only [Path.snoc, dite_eq_left (show i.val ≤ p.length by omega),
        dite_eq_left (show i.val + 1 ≤ p.length by omega)] using hpe ⟨i.val, hi⟩
    · have hei : i.val = p.length := by have := i.isLt; change i.val < p.length + 1 at this; omega
      simp only [Path.snoc, hei, Nat.le_refl, dite_true,
        show ¬p.length + 1 ≤ p.length by omega, dite_false]
      change T.parent v = some p.last
      rwa [hpu]

end RootedTree

namespace Path
variable [DecidableEq V]

def locate (p : Path H) (v : V) : Option (Fin (p.length + 1)) :=
  (List.finRange (p.length + 1)).find? fun i => decide (p.vertex i = v)

theorem locate_sound (p : Path H) (v : V) (i : Fin (p.length + 1))
    (h : p.locate v = some i) : p.vertex i = v := by
  have hh := List.find?_some (p := fun j => decide (p.vertex j = v)) h
  exact of_decide_eq_true hh

theorem locate_none (p : Path H) (v : V) : p.locate v = none ↔ ¬p.Contains v := by
  rw [locate, List.find?_eq_none]
  simp only [decide_eq_true_eq, List.mem_finRange, forall_const]
  constructor
  · intro h ⟨i, hi⟩; exact h i hi
  · intro h i hi; exact h ⟨i, hi⟩

@[simp] theorem locate_vertex (p : Path H) (i : Fin (p.length + 1)) : p.locate (p.vertex i) = some i := by
  cases h : p.locate (p.vertex i) with
  | none => exact False.elim ((p.locate_none _).1 h ⟨i, rfl⟩)
  | some j =>
    have he := p.injective j i (p.locate_sound _ j h)
    simp only [he]

end Path

namespace TreeReconstruction
variable [DecidableEq V]

/-- False denotes the red root and true denotes the green root. -/
def root (r g : V) (c : Bool) : V := if c then g else r

structure Forest (V : Type) where
  color : V → Option Bool
  parent : V → Option V

/-- Partial forest correctness; coverage of the entire searched region is not
an input and is proved after saturation. -/
structure Valid (S : V → Prop) (r g b : V) (F : Forest V) : Prop where
  domain : ∀ v c, F.color v = some c → S v ∧ v ≠ b
  roots : ∀ c, root r g c ≠ b → F.color (root r g c) = some c
  roots_none : ∀ c, F.parent (root r g c) = none
  parent_color : ∀ u v, F.parent v = some u →
    ∃ c, F.color u = some c ∧ F.color v = some c ∧ H.Edge u v
  reached : ∀ v c, F.color v = some c → ParentReach F.parent (root r g c) v

/-- Seed the forest with the actual two saved root-to-bottleneck paths. -/
def seed (b : V) (p q : Path H) : Forest V where
  color v := if v = b then none else
    match p.locate v with
    | some _ => some false
    | none => match q.locate v with | some _ => some true | none => none
  parent v := if v = b then none else
    match p.locate v with
    | some i => if hi : 0 < i.val then some (p.vertex ⟨i.val - 1, by omega⟩) else none
    | none => match q.locate v with
      | some i => if hi : 0 < i.val then some (q.vertex ⟨i.val - 1, by omega⟩) else none
      | none => none

omit [DecidableEq V] in
private theorem vertex_ne_last (p : Path H) (i : Fin (p.length + 1)) (hi : i.val < p.length) :
    p.vertex i ≠ p.last := by
  intro h
  have he := congrArg Fin.val (p.injective i ⟨p.length, by omega⟩ h)
  change i.val = p.length at he
  omega

private theorem seed_red (b : V) (p q : Path H) (i : Fin (p.length + 1)) (hi : p.vertex i ≠ b) :
    (seed b p q).color (p.vertex i) = some false := by
  simp only [seed, hi, ite_false, Path.locate_vertex]

private theorem seed_green (b : V) (p q : Path H)
    (hm : ∀ v, p.Contains v → q.Contains v → v = b)
    (i : Fin (q.length + 1)) (hi : q.vertex i ≠ b) :
    (seed b p q).color (q.vertex i) = some true := by
  have hp : p.locate (q.vertex i) = none := (p.locate_none _).2
    (fun hh => hi (hm _ hh ⟨i, rfl⟩))
  simp only [seed, hi, ite_false, hp, Path.locate_vertex]

private theorem seed_red_parent (b : V) (p q : Path H)
    (i : Fin (p.length + 1)) (hi : p.vertex i ≠ b) :
    (seed b p q).parent (p.vertex i) =
      if hj : 0 < i.val then some (p.vertex ⟨i.val - 1, by omega⟩) else none := by
  simp only [seed, hi, ite_false, Path.locate_vertex]

private theorem seed_green_parent (b : V) (p q : Path H)
    (hm : ∀ v, p.Contains v → q.Contains v → v = b)
    (i : Fin (q.length + 1)) (hi : q.vertex i ≠ b) :
    (seed b p q).parent (q.vertex i) =
      if hj : 0 < i.val then some (q.vertex ⟨i.val - 1, by omega⟩) else none := by
  have hp : p.locate (q.vertex i) = none := (p.locate_none _).2
    (fun hh => hi (hm _ hh ⟨i, rfl⟩))
  simp only [seed, hi, ite_false, hp, Path.locate_vertex]

omit [DecidableEq V] in
private theorem reached_along (F : Forest V) (p : Path H) (b : V) (hb : p.last = b)
    (hp : ∀ i : Fin (p.length + 1), p.vertex i ≠ b →
      F.parent (p.vertex i) = if hj : 0 < i.val then some (p.vertex ⟨i.val - 1, by omega⟩) else none)
    (i : Fin (p.length + 1)) (hi : p.vertex i ≠ b) : ParentReach F.parent p.first (p.vertex i) := by
  have aux : ∀ k (hk : k < p.length + 1), k < p.length → ParentReach F.parent p.first (p.vertex ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero => intro hk _; exact .root
    | succ k ih =>
      intro hk hkl
      have hprev := ih (by omega) (by omega)
      apply ParentReach.step hprev
      rw [hp ⟨k + 1, hk⟩ (fun h => vertex_ne_last p _ hkl (h.trans hb.symm))]
      simp
  have hil : i.val < p.length := by
    by_cases hl : i.val < p.length
    · exact hl
    · have he : i = ⟨p.length, by omega⟩ := Fin.ext (by have := i.isLt; change i.val = p.length; omega)
      exact False.elim (hi ((congrArg p.vertex he).trans hb))
  exact aux i.val i.isLt hil

theorem seed_valid (S : V → Prop) (r g b : V) (p q : Path H)
    (hpr : p.first = r) (hqr : q.first = g) (hpb : p.last = b) (hqb : q.last = b)
    (hps : ∀ v, p.Contains v → S v) (hqs : ∀ v, q.Contains v → S v)
    (hm : ∀ v, p.Contains v → q.Contains v → v = b) : Valid (H := H) S r g b (seed b p q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v c hc
    simp only [seed] at hc
    split at hc
    · contradiction
    next hv =>
      refine ⟨?_, hv⟩
      cases hp : p.locate v with
      | some i => exact hps v ⟨i, p.locate_sound v i hp⟩
      | none =>
        rw [hp] at hc
        cases hq : q.locate v with
        | none => rw [hq] at hc; contradiction
        | some i => exact hqs v ⟨i, q.locate_sound v i hq⟩
  · intro c hc
    cases c with
    | false =>
      change r ≠ b at hc
      have hv : p.vertex ⟨0, by omega⟩ ≠ b := by change p.first ≠ b; rwa [hpr]
      exact hpr ▸ seed_red b p q ⟨0, by omega⟩ hv
    | true =>
      change g ≠ b at hc
      have hv : q.vertex ⟨0, by omega⟩ ≠ b := by change q.first ≠ b; rwa [hqr]
      exact hqr ▸ seed_green b p q hm ⟨0, by omega⟩ hv
  · intro c
    cases c with
    | false =>
      change (seed b p q).parent r = none
      by_cases hr : r = b
      · simp [seed, hr]
      · have hv : p.vertex ⟨0, by omega⟩ ≠ b := by change p.first ≠ b; rwa [hpr]
        have hh := seed_red_parent b p q ⟨0, by omega⟩ hv
        simp only [Nat.lt_irrefl, dite_false] at hh
        change (seed b p q).parent p.first = none at hh
        rwa [hpr] at hh
    | true =>
      change (seed b p q).parent g = none
      by_cases hg : g = b
      · simp [seed, hg]
      · have hv : q.vertex ⟨0, by omega⟩ ≠ b := by change q.first ≠ b; rwa [hqr]
        have hh := seed_green_parent b p q hm ⟨0, by omega⟩ hv
        simp only [Nat.lt_irrefl, dite_false] at hh
        change (seed b p q).parent q.first = none at hh
        rwa [hqr] at hh
  · intro u v hpar
    simp only [seed] at hpar
    split at hpar
    · contradiction
    next hv =>
      cases hp : p.locate v with
      | some i =>
        simp only [hp] at hpar
        have hiv := p.locate_sound v i hp
        split at hpar
        next hi =>
          have hpu : p.vertex ⟨i.val - 1, by omega⟩ = u := Option.some.inj hpar
          have hip : p.vertex ⟨i.val - 1, by omega⟩ ≠ b := fun h =>
            vertex_ne_last p _ (by have := i.isLt; change i.val - 1 < p.length; omega) (h.trans hpb.symm)
          refine ⟨false, hpu ▸ seed_red b p q _ hip, hiv ▸ seed_red b p q i (hiv ▸ hv), ?_⟩
          have he := p.adjacent ⟨i.val - 1, by omega⟩
          simpa only [show i.val - 1 + 1 = i.val by omega, Fin.eta, hpu, hiv] using he
        next _ => contradiction
      | none =>
        simp only [hp] at hpar
        cases hq : q.locate v with
        | none => simp only [hq] at hpar; contradiction
        | some i =>
          simp only [hq] at hpar
          have hiv := q.locate_sound v i hq
          split at hpar
          next hi =>
            have hqu : q.vertex ⟨i.val - 1, by omega⟩ = u := Option.some.inj hpar
            have hiq : q.vertex ⟨i.val - 1, by omega⟩ ≠ b := fun h =>
              vertex_ne_last q _ (by have := i.isLt; change i.val - 1 < q.length; omega) (h.trans hqb.symm)
            refine ⟨true, hqu ▸ seed_green b p q hm _ hiq,
              hiv ▸ seed_green b p q hm i (hiv ▸ hv), ?_⟩
            have he := q.adjacent ⟨i.val - 1, by omega⟩
            simpa only [show i.val - 1 + 1 = i.val by omega, Fin.eta, hqu, hiv] using he
          next _ => contradiction
  · intro v c hc
    simp only [seed] at hc
    split at hc
    · contradiction
    next hv =>
      cases hp : p.locate v with
      | some i =>
        rw [hp] at hc
        have hcf : c = false := (Option.some.inj hc).symm
        subst c
        have hiv := p.locate_sound v i hp
        have hr := reached_along (seed b p q) p b hpb (seed_red_parent b p q) i (hiv ▸ hv)
        simpa only [root, Bool.false_eq_true, ite_false, hpr, hiv] using hr
      | none =>
        rw [hp] at hc
        cases hq : q.locate v with
        | none => rw [hq] at hc; contradiction
        | some i =>
          rw [hq] at hc
          have hct : c = true := (Option.some.inj hc).symm
          subst c
          have hiv := q.locate_sound v i hq
          have hr := reached_along (seed b p q) q b hqb (seed_green_parent b p q hm) i (hiv ▸ hv)
          simpa only [root, ite_true, hqr, hiv] using hr

def Extends (F F' : Forest V) : Prop :=
  ∀ v c, F.color v = some c → F'.color v = some c

omit [DecidableEq V] in
theorem Extends.refl (F : Forest V) : Extends F F := fun _ _ h => h

omit [DecidableEq V] in
theorem Extends.trans {F F' F'' : Forest V} (h : Extends F F') (h' : Extends F' F'') :
    Extends F F'' := fun v c hc => h' v c (h v c hc)

/-- Attach one previously uncolored vertex to its colored predecessor. -/
def attach (F : Forest V) (u v : V) (c : Bool) : Forest V where
  color w := if w = v then some c else F.color w
  parent w := if w = v then some u else F.parent w

theorem attach_extends (F : Forest V) (u v : V) (c : Bool) (hv : F.color v = none) :
    Extends F (attach F u v c) := by
  intro w d hd
  have hne : w ≠ v := by intro he; rw [he, hv] at hd; contradiction
  simp only [attach, hne, ite_false, hd]

theorem attach_valid {S : V → Prop} {r g b : V} {F : Forest V}
    (hF : Valid (H := H) S r g b F) (u v : V) (c : Bool)
    (hu : F.color u = some c) (hv : F.color v = none)
    (he : H.Edge u v) (hsv : S v) (hvb : v ≠ b) :
    Valid (H := H) S r g b (attach F u v c) := by
  have hmono := attach_extends F u v c hv
  have hup : u ≠ v := by intro hh; rw [hh, hv] at hu; contradiction
  have hpmono : ∀ a w, F.parent w = some a → (attach F u v c).parent w = some a := by
    intro a w hw
    have hne : w ≠ v := by
      intro hh
      obtain ⟨d, _, hd, _⟩ := hF.parent_color a w hw
      rw [hh, hv] at hd
      contradiction
    simp only [attach, hne, ite_false, hw]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w d hd
    change (if w = v then some c else F.color w) = some d at hd
    split at hd
    next hh => exact hh ▸ ⟨hsv, hvb⟩
    next _ => exact hF.domain w d hd
  · intro d hd
    exact hmono _ _ (hF.roots d hd)
  · intro d
    have hne : root r g d ≠ v := by
      intro hh
      have hrb : root r g d ≠ b := hh ▸ hvb
      have hc := hF.roots d hrb
      rw [hh, hv] at hc
      contradiction
    simp only [attach, hne, ite_false]
    exact hF.roots_none d
  · intro a w hw
    change (if w = v then some u else F.parent w) = some a at hw
    split at hw
    next hwv =>
      have hua : u = a := Option.some.inj hw
      refine ⟨c, hua ▸ hmono u c hu, ?_, ?_⟩
      · simp only [attach, hwv, ite_true]
      · exact hua ▸ hwv ▸ he
    next _ =>
      obtain ⟨d, ha, hwc, hew⟩ := hF.parent_color a w hw
      exact ⟨d, hmono a d ha, hmono w d hwc, hew⟩
  · intro w d hd
    change (if w = v then some c else F.color w) = some d at hd
    split at hd
    next hwv =>
      have hcd : c = d := Option.some.inj hd
      subst d
      rw [hwv]
      apply ParentReach.step ((hF.reached u c hu).mono hpmono)
      simp only [attach, ite_true]
    next _ => exact (hF.reached w d hd).mono hpmono

/-- An attachment opportunity inside the searched region. -/
abbrev Frontier (S : V → Prop) (b : V) (F : Forest V) (u v : V) : Prop :=
  H.Edge u v ∧ (F.color u).isSome ∧ F.color v = none ∧ S v ∧ v ≠ b

variable {n : Nat} {H : LayeredGraph (Fin n)}

def uncolored (F : Forest (Fin n)) : Nat :=
  (List.finRange n).countP fun v => (F.color v).isNone

private theorem countP_strict {A : Type} (xs : List A) (p q : A → Bool)
    (hle : ∀ a ∈ xs, p a = true → q a = true)
    (hex : ∃ a, a ∈ xs ∧ p a = false ∧ q a = true) : xs.countP p < xs.countP q := by
  induction xs with
  | nil => simp at hex
  | cons a xs ih =>
    obtain ⟨b, hb, hbp, hbq⟩ := hex
    have htail : ∀ x ∈ xs, p x = true → q x = true := fun x hx => hle x (List.mem_cons_of_mem _ hx)
    rcases List.mem_cons.mp hb with he | hb
    · subst b
      have hh := List.countP_mono_left htail
      simp only [List.countP_cons, hbp, hbq, Bool.false_eq_true, ↓reduceIte]
      omega
    · have hh := ih htail ⟨b, hb, hbp, hbq⟩
      have ha := hle a (List.mem_cons_self)
      rw [List.countP_cons, List.countP_cons]
      cases hpa : p a <;> cases hqa : q a <;> simp_all <;> omega

theorem attach_uncolored_lt (F : Forest (Fin n)) (u v : Fin n) (c : Bool)
    (hv : F.color v = none) : uncolored (attach F u v c) < uncolored F := by
  unfold uncolored
  apply countP_strict
  · intro w _ hw
    change (if w = v then some c else F.color w).isNone = true at hw
    split at hw
    · contradiction
    · exact hw
  · exact ⟨v, List.mem_finRange v, by simp [attach], by simp [hv]⟩

def frontierPair [DecidableRel H.Edge] (S : Fin n → Prop) [DecidablePred S]
    (b : Fin n) (F : Forest (Fin n)) : Option (Fin n × Fin n) :=
  (Machine.vertexPairs n).find? fun e => decide (Frontier (H := H) S b F e.1 e.2)

structure Completion (H : LayeredGraph (Fin n)) (S : Fin n → Prop) (r g b : Fin n)
    (F : Forest (Fin n)) where
  forest : Forest (Fin n)
  valid : Valid (H := H) S r g b forest
  extends_seed : Extends F forest
  closed : ∀ u v, ¬ Frontier (H := H) S b forest u v

/-- Deterministically saturate the finite colored forest. Every successful
iteration colors a new vertex, so there are at most n such iterations. -/
def complete [DecidableRel H.Edge] (S : Fin n → Prop) [DecidablePred S] (r g b : Fin n)
    (F : Forest (Fin n)) (hF : Valid (H := H) S r g b F) : Completion H S r g b F :=
  match hpair : frontierPair (H := H) S b F with
  | none => ⟨F, hF, Extends.refl F, by
      intro u v hf
      have hn := List.find?_eq_none.mp hpair (u, v) (Machine.mem_vertexPairs u v)
      exact hn (by simpa only [decide_eq_true_eq] using hf)⟩
  | some e =>
    have he : Frontier (H := H) S b F e.1 e.2 :=
      of_decide_eq_true (List.find?_some (p := fun e : Fin n × Fin n => decide (Frontier (H := H) S b F e.1 e.2)) hpair)
    match hc : F.color e.1 with
    | none => False.elim (by have hh := he.2.1; rw [hc] at hh; exact Bool.noConfusion hh)
    | some c =>
      let F' := attach F e.1 e.2 c
      let out := complete S r g b F'
        (attach_valid hF e.1 e.2 c hc he.2.2.1 he.1 he.2.2.2.1 he.2.2.2.2)
      ⟨out.forest, out.valid, (attach_extends F e.1 e.2 c he.2.2.1).trans out.extends_seed, out.closed⟩
termination_by uncolored F
decreasing_by exact attach_uncolored_lt F e.1 e.2 c he.2.2.1

/-- Saturation covers every path from a seeded root that remains in the
searched region above the bottleneck. -/
theorem Completion.path_colored {S : Fin n → Prop} {r g b : Fin n} {F : Forest (Fin n)}
    (out : Completion H S r g b F) (p : Path H)
    (hr : p.first = r ∨ p.first = g)
    (hS : ∀ i, S (p.vertex i)) (hb : ∀ i, p.vertex i ≠ b) :
    ∃ c, out.forest.color p.last = some c := by
  have aux : ∀ k (hk : k < p.length + 1), ∃ c, out.forest.color (p.vertex ⟨k, hk⟩) = some c := by
    intro k
    induction k with
    | zero =>
      intro hk
      rcases hr with hr | hr
      · refine ⟨false, ?_⟩
        have hh := out.valid.roots false (by change r ≠ b; rw [← hr]; exact hb ⟨0, hk⟩)
        change out.forest.color r = some false at hh
        change out.forest.color p.first = some _
        rwa [hr]
      · refine ⟨true, ?_⟩
        have hh := out.valid.roots true (by change g ≠ b; rw [← hr]; exact hb ⟨0, hk⟩)
        change out.forest.color g = some true at hh
        change out.forest.color p.first = some _
        rwa [hr]
    | succ k ih =>
      intro hk
      obtain ⟨c, hc⟩ := ih (by omega)
      cases hv : out.forest.color (p.vertex ⟨k + 1, hk⟩) with
      | some d => exact ⟨d, rfl⟩
      | none =>
        apply False.elim
        apply out.closed (p.vertex ⟨k, by omega⟩) (p.vertex ⟨k + 1, hk⟩)
        exact ⟨p.adjacent ⟨k, by omega⟩, by simp [hc], hv, hS _, hb _⟩
  exact aux p.length (by omega)

def colorSet (F : Forest (Fin n)) (b : Fin n) (c : Bool) (v : Fin n) : Prop :=
  v = b ∨ F.color v = some c

/-- Each tree adds its own final parent edge into the shared bottleneck. -/
def treeParent (F : Forest (Fin n)) (b : Fin n) (c : Bool) (p : Path H)
    (v : Fin n) : Option (Fin n) :=
  if v = b then
    if hpos : 0 < p.length then some (p.vertex ⟨p.length - 1, by omega⟩) else none
  else if F.color v = some c then F.parent v else none

private theorem colored_reach {S : Fin n → Prop} {r g b : Fin n} {F : Forest (Fin n)}
    (hF : Valid (H := H) S r g b F) (c : Bool) (p : Path H) (v : Fin n)
    (hv : F.color v = some c) : ParentReach (treeParent F b c p) (root r g c) v := by
  have hreach := hF.reached v c hv
  induction hreach with
  | root => exact .root
  | @step u v _ hp ih =>
    obtain ⟨d, hu, hd, he⟩ := hF.parent_color u v hp
    have hdc : d = c := Option.some.inj (hd.symm.trans hv)
    subst d
    apply ParentReach.step (ih hu)
    simp only [treeParent, (hF.domain v c hv).2, ite_false, hv, ite_true, hp]

/-- Build one of the globally consistent rooted trees from the completed
forest, including its separately saved final edge into b. -/
def rootedTree {S : Fin n → Prop} {r g b : Fin n} {F : Forest (Fin n)}
    (hF : Valid (H := H) S r g b F) (c : Bool) (p : Path H)
    (hpr : p.first = root r g c) (hpb : p.last = b)
    (hpred : ∀ hpos : 0 < p.length, F.color (p.vertex ⟨p.length - 1, by omega⟩) = some c) :
    RootedTree H (root r g c) (colorSet F b c) where
  parent := treeParent F b c p
  root_none := by
    by_cases hrb : root r g c = b
    · have hl : p.length = 0 := by
        have he := p.injective ⟨0, by omega⟩ ⟨p.length, by omega⟩ (hpr.trans (hrb.trans hpb.symm))
        have hh := congrArg Fin.val he
        change 0 = p.length at hh
        omega
      simp only [treeParent, hrb, ite_true, hl, Nat.lt_irrefl, dite_false]
    · simp only [treeParent, hrb, ite_false, hF.roots c hrb, ite_true, hF.roots_none c]
  edge := by
    intro u v hp
    unfold treeParent at hp
    split at hp
    next hvb =>
      split at hp
      next hpos =>
        have he := Option.some.inj hp
        refine ⟨Or.inr (he ▸ hpred hpos), Or.inl hvb, ?_⟩
        have hedge := p.adjacent ⟨p.length - 1, by omega⟩
        have hlast : p.vertex ⟨p.length - 1 + 1, by omega⟩ = b := by
          simpa only [show p.length - 1 + 1 = p.length by omega, Path.last] using hpb
        simpa only [he, hlast, hvb] using hedge
      next _ => contradiction
    next _ =>
      split at hp
      next hc =>
        obtain ⟨d, hu, hv, he⟩ := hF.parent_color u v hp
        have hdc : d = c := Option.some.inj (hv.symm.trans hc)
        subst d
        exact ⟨Or.inr hu, Or.inr hv, he⟩
      next _ => contradiction
  spanning := by
    intro v hv
    rcases hv with hvb | hc
    · subst v
      by_cases hpos : 0 < p.length
      · apply ParentReach.step (colored_reach hF c p _ (hpred hpos))
        simp only [treeParent, ite_true, hpos, dite_true]
      · have hl : p.length = 0 := by omega
        have he : p.first = p.last := congrArg p.vertex (Fin.ext (by omega))
        have hrb : root r g c = b := hpr.symm.trans (he.trans hpb)
        rw [← hrb]
        exact .root
    · exact colored_reach hF c p v hc

end TreeReconstruction

/-- A stored global coloring and two parent-function spanning trees. The
colored sets partition the searched region except for the shared bottleneck. -/
structure ColoredTrees (H : LayeredGraph (Fin n)) (S : Fin n → Prop) (r g b : Fin n) where
  color : Fin n → Option Bool
  bottleneck_mem : S b
  domain : ∀ v, (∃ c, color v = some c) ↔ S v ∧ v ≠ b
  red : RootedTree H r (fun v => v = b ∨ color v = some false)
  green : RootedTree H g (fun v => v = b ∨ color v = some true)

namespace ColoredTrees
variable {n : Nat} {H : LayeredGraph (Fin n)} {S : Fin n → Prop} {r g b : Fin n}

theorem cover (T : ColoredTrees H S r g b) (v : Fin n) :
    S v ↔ (v = b ∨ T.color v = some false) ∨ (v = b ∨ T.color v = some true) := by
  constructor
  · intro hv
    by_cases hvb : v = b
    · exact Or.inl (Or.inl hvb)
    · obtain ⟨c, hc⟩ := (T.domain v).2 ⟨hv, hvb⟩
      cases c
      · exact Or.inl (Or.inr hc)
      · exact Or.inr (Or.inr hc)
  · rintro (hv | hv)
    · rcases hv with hvb | hc
      · exact hvb ▸ T.bottleneck_mem
      · exact ((T.domain v).1 ⟨false, hc⟩).1
    · rcases hv with hvb | hc
      · exact hvb ▸ T.bottleneck_mem
      · exact ((T.domain v).1 ⟨true, hc⟩).1

theorem overlap (T : ColoredTrees H S r g b) (v : Fin n) :
    (v = b ∨ T.color v = some false) ∧ (v = b ∨ T.color v = some true) ↔ v = b := by
  constructor
  · rintro ⟨hv | hr, hw | hg⟩
    · exact hv
    · exact hv
    · exact hw
    · have he := Option.some.inj (hr.symm.trans hg)
      contradiction
  · intro hv; exact ⟨Or.inl hv, Or.inl hv⟩

end ColoredTrees
namespace Machine
variable {n : Nat} {H : LayeredGraph (Fin n)}

/-- Reconstruct globally consistent colored trees from an actual reachable
bottleneck output. All witnesses, coloring and parent functions are computed
from the saved paths and finite search history. -/
def reconstructTrees [DecidableRel H.Edge] (hreach : ReachBottom H) (r g : Fin n)
    (s : ExecutableState H) (hs : Reachable r g s.state) (b : Fin n) (p q : Path H)
    (hm : s.state.mode = .bottleneck b p q) : ColoredTrees H s.state.frame.visited r g b := by
  letI := s.visitedDec
  have hi := reachable_invariant hreach hs
  have ho : HighestBottleneck H r g b ∧ SavedPaths r g b s.state.frame p q := by
    simpa only [ModeInv, hm] using hi.mode
  let F := TreeReconstruction.seed b p q
  have hF := TreeReconstruction.seed_valid s.state.frame.visited r g b p q
    ho.2.red_root ho.2.green_root ho.2.red_end ho.2.green_end
    ho.2.red_seen ho.2.green_seen ho.2.meet
  let out := TreeReconstruction.complete s.state.frame.visited r g b F hF
  have hpredp : ∀ hpos : 0 < p.length,
      out.forest.color (p.vertex ⟨p.length - 1, by omega⟩) = some false := by
    intro hpos
    apply out.extends_seed
    apply TreeReconstruction.seed_red
    intro he
    have hx := p.injective ⟨p.length - 1, by omega⟩ ⟨p.length, by omega⟩ (he.trans ho.2.red_end.symm)
    have hh := congrArg Fin.val hx
    change p.length - 1 = p.length at hh
    omega
  have hpredq : ∀ hpos : 0 < q.length,
      out.forest.color (q.vertex ⟨q.length - 1, by omega⟩) = some true := by
    intro hpos
    apply out.extends_seed
    apply TreeReconstruction.seed_green b p q ho.2.meet
    intro he
    have hx := q.injective ⟨q.length - 1, by omega⟩ ⟨q.length, by omega⟩ (he.trans ho.2.green_end.symm)
    have hh := congrArg Fin.val hx
    change q.length - 1 = q.length at hh
    omega
  refine ⟨out.forest.color, ho.2.red_end ▸ ho.2.red_seen p.last p.contains_last, ?_,
    TreeReconstruction.rootedTree out.valid false p ho.2.red_root ho.2.red_end hpredp,
    TreeReconstruction.rootedTree out.valid true q ho.2.green_root ho.2.green_end hpredq⟩
  intro v
  constructor
  · rintro ⟨c, hc⟩
    exact out.valid.domain v c hc
  · rintro ⟨hv, hvb⟩
    obtain ⟨a, haroot, hab, ⟨i, hiv⟩⟩ :=
      (visited_iff_on_root_to_bottleneck hreach hs hm v).1 hv
    have hil : i.val < a.length := by
      by_cases hlt : i.val < a.length
      · exact hlt
      · have he : i = ⟨a.length, by omega⟩ := Fin.ext (by have := i.isLt; change i.val = a.length; omega)
        exact False.elim (hvb (hiv.symm.trans ((congrArg a.vertex he).trans hab)))
    have hS : ∀ j : Fin (i.val + 1), s.state.frame.visited ((a.take i.val (by omega)).vertex j) := by
      intro j
      apply (visited_iff_on_root_to_bottleneck hreach hs hm _).2
      exact ⟨a, haroot, hab, ⟨⟨j.val, by have := j.isLt; change j.val < i.val + 1 at this; omega⟩, rfl⟩⟩
    have hb : ∀ j : Fin (i.val + 1), (a.take i.val (by omega)).vertex j ≠ b := by
      intro j hj
      have he := a.injective ⟨j.val, by have := j.isLt; change j.val < i.val + 1 at this; omega⟩
        ⟨a.length, by omega⟩ (hj.trans hab.symm)
      have hh := congrArg Fin.val he
      have hjb := j.isLt
      change j.val < i.val + 1 at hjb
      change j.val = a.length at hh
      omega
    have hc := out.path_colored (a.take i.val (by omega)) haroot hS hb
    simpa only [Path.take_last, hiv] using hc

/-- The full graph-theoretic DDFS output, including global colored trees in
the bottleneck case. The searched set is exactly the root-to-bottleneck region. -/
inductive FullOutput (H : LayeredGraph (Fin n)) (r g : Fin n) where
  | disjoint (p q : Path H) (red : p.ToBottom r) (green : q.ToBottom g)
      (separate : p.Disjoint q)
  | bottleneck (b : Fin n) (S : Fin n → Prop) (trees : ColoredTrees H S r g b)
      (highest : HighestBottleneck H r g b)
      (region : ∀ v, S v ↔ OnRootTo (H := H) r g b v)

/-- Execute DDFS and reconstruct the full colored-tree output when needed.
The finite reconstruction is a separate postprocessing pass that returns
certified paths or colored trees. -/
def executeFull [DecidableRel H.Edge] (hreach : ReachBottom H) (r g : Fin n) :
    FullOutput H r g := by
  let out := execute hreach r g
  have hs : Reachable r g out.finalState.state := out.trace.reachable .initial
  have hc := execute_correct hreach r g
  change CorrectOutcome r g out.finalState.state at hc
  cases hm : out.finalState.state.mode with
  | normal => simp only [CorrectOutcome, hm] at hc
  | redRecovery b p q => simp only [CorrectOutcome, hm] at hc
  | greenRecovery b p q => simp only [CorrectOutcome, hm] at hc
  | disjoint =>
    have hd : out.finalState.state.frame.red.ToBottom r ∧ out.finalState.state.frame.green.ToBottom g ∧
        out.finalState.state.frame.red.Disjoint out.finalState.state.frame.green := by
      simpa only [CorrectOutcome, hm] using hc
    exact .disjoint out.finalState.state.frame.red out.finalState.state.frame.green hd.1 hd.2.1 hd.2.2
  | bottleneck b p q =>
    have hh : HighestBottleneck H r g b ∧ p.first = r ∧ p.last = b ∧ q.first = g ∧
        q.last = b ∧ (∀ u, p.Contains u → q.Contains u → u = b) := by
      simpa only [CorrectOutcome, hm] using hc
    exact .bottleneck b out.finalState.state.frame.visited
      (reconstructTrees hreach r g out.finalState hs b p q hm) hh.1
      (fun v => visited_iff_on_root_to_bottleneck hreach hs hm v)

end Machine
end MaximumMatching.DDFS
