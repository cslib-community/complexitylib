/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.GomoryHu.Basic

/-!
# Existence of Gomory–Hu trees

Every symmetric submodular set function `f : Finset V → β` on a nonempty finite ground set has a
Gomory–Hu tree (cut-equivalent tree): a spanning tree on `V` such that for every tree edge `uv`, the
side of `T - uv` containing `u` is a minimum `u`–`v` cut of `f`. Gomory and Hu ([GomoryHu1961]; see
also [Schrijver2003], Section 15.4) prove this for the cut function of an undirected graph with
nonnegative edge weights, which is symmetric and submodular. Their proof uses only these two
properties, and the statement for symmetric submodular functions is its standard abstraction.

## Proof

The proof follows the recursive scheme of Gomory and Hu, phrased without contraction. A *partial
tree* on a set `R` of terminals is a set of labelled edges `(u, v, S)` with `u, v ∈ R`, each `S`
a minimum `u`–`v` cut, the labels laminar with respect to the edges (an edge's label does not
separate the endpoints of any other edge), every two terminals joined by a chain of edges, and
every vertex represented by a terminal on the same side of every label. Pick distinct terminals
`s, t ∈ R` and a minimum `s`–`t` cut `U`. By the uncrossing lemma
`Cslib.Algorithms.Lean.GomoryHu.IsMinCutBetween.inter`, the terminals of `R ∩ U` have minimum cuts
that do not split `Uᶜ`, and those of `R \ U` have minimum cuts that do not split `U`. Recursively
build partial trees on both sides and join them by the edge `r₁ r₂` labelled `U`, where `r₁` is the
terminal of `R ∩ U` representing `t` and `r₂` the terminal of `R \ U` representing `s`. The set `U`
is a minimum `r₁`–`r₂` cut: a cheaper `r₁`–`r₂` separator would cross an edge on a tree chain whose
label separates `s` from `t`, and all such labels weigh at least `f U`.

## Main results

* `Cslib.Algorithms.Lean.GomoryHu.exists_isGomoryHuTree`: every symmetric submodular set function
  on a nonempty finite ground set has a Gomory–Hu tree.

## References

* [GomoryHu1961]
* [Schrijver2003]
-/

public section

namespace Cslib.Algorithms.Lean.GomoryHu

open Cslib.Algorithms.Lean.Submodular
open SimpleGraph (edgeSide mem_edgeSide)

variable {V : Type*} {β : Type*}

/-- A labelled edge of a partial Gomory–Hu tree: endpoints `u, v` and the side `S` of `u`. -/
private structure CEdge (V : Type*) where
  u : V
  v : V
  S : Finset V

/-- `x` and `y` are joined by an edge of `E` whose label separates `x₀` from `y₀`. -/
private def Step (E : Set (CEdge V)) (x₀ y₀ : V) (x y : V) : Prop :=
  ∃ e ∈ E, (x₀ ∈ e.S ↔ y₀ ∉ e.S) ∧ ((e.u = x ∧ e.v = y) ∨ (e.u = y ∧ e.v = x))

/-- Invariant of a partial Gomory–Hu tree `E` on the terminals `R` whose labels lie in `L`. -/
private structure Inv [Preorder β] (f : Finset V → β) (L : Finset V → Prop) (R : Finset V)
    (E : Set (CEdge V)) : Prop where
  mem : ∀ e ∈ E, e.u ∈ R ∧ e.v ∈ R
  good : ∀ e ∈ E, L e.S
  edge : ∀ e ∈ E, IsMinCutBetween f e.u e.v e.S
  nest : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → (e'.u ∈ e.S ↔ e'.v ∈ e.S)
  chain : ∀ x ∈ R, ∀ y ∈ R, Relation.ReflTransGen (Step E x y) x y
  rep : ∀ z, ∃ r ∈ R, ∀ e ∈ E, (z ∈ e.S ↔ r ∈ e.S)

/-- A chain from inside `Y` to outside `Y` crosses `Y` along one of its edges. -/
private theorem exists_cross {E : Set (CEdge V)} {x₀ y₀ a b : V} {Y : Finset V}
    (h : Relation.ReflTransGen (Step E x₀ y₀) a b) (ha : a ∈ Y) (hb : b ∉ Y) :
    ∃ e ∈ E, (x₀ ∈ e.S ↔ y₀ ∉ e.S) ∧ (e.u ∈ Y ↔ e.v ∉ Y) := by
  induction h with
  | refl => exact absurd ha hb
  | @tail c d _ hcd ih =>
    by_cases hc : c ∈ Y
    · obtain ⟨e, he, hsep, hends⟩ := hcd
      refine ⟨e, he, hsep, ?_⟩
      rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨fun _ => hb, fun _ => hc⟩
      · exact ⟨fun h => absurd h hb, fun h => absurd hc h⟩
    · exact ih hc

private theorem step_mono {E E' : Set (CEdge V)} {x₀ y₀ x₁ y₁ : V}
    (hE : ∀ e ∈ E, e ∈ E' ∧ ((x₀ ∈ e.S ↔ y₀ ∉ e.S) → (x₁ ∈ e.S ↔ y₁ ∉ e.S))) {a b : V}
    (h : Relation.ReflTransGen (Step E x₀ y₀) a b) :
    Relation.ReflTransGen (Step E' x₁ y₁) a b :=
  Relation.ReflTransGen.mono (fun _ _ ⟨e, he, hsep, hends⟩ =>
    ⟨e, (hE e he).1, (hE e he).2 hsep, hends⟩) _ _ h

private theorem step_swap {E : Set (CEdge V)} {x₀ y₀ a b : V}
    (h : Relation.ReflTransGen (Step E x₀ y₀) a b) :
    Relation.ReflTransGen (Step E y₀ x₀) b a :=
  Relation.ReflTransGen.mono (fun _ _ ⟨e, he, hsep, hends⟩ =>
    ⟨e, he, by tauto, by tauto⟩) _ _ (Relation.reflTransGen_swap.mpr h)

section Construction

variable [Fintype V] [DecidableEq V]

/-- A family of sets closed under complement and intersection. -/
private def Good (L : Finset V → Prop) : Prop :=
  (∀ X, L X → L Xᶜ) ∧ ∀ X Y, L X → L Y → L (X ∩ Y)

/-- The sets of `L` that do not split `Uᶜ`. -/
private def Restrict (L : Finset V → Prop) (U : Finset V) (X : Finset V) : Prop :=
  L X ∧ (X ⊆ U ∨ Uᶜ ⊆ X)

/-- Every two distinct terminals of `R` have a minimum cut in `L`. -/
private def Exact [Preorder β] (f : Finset V → β) (L : Finset V → Prop) (R : Finset V) : Prop :=
  ∀ a ∈ R, ∀ b ∈ R, a ≠ b → ∃ X, L X ∧ IsMinCutBetween f a b X

private theorem good_restrict {L : Finset V → Prop} (hL : Good L) (U : Finset V) :
    Good (Restrict L U) := by
  refine ⟨fun X ⟨hX, hXU⟩ => ⟨hL.1 X hX, ?_⟩, fun X Y ⟨hX, hXU⟩ ⟨hY, hYU⟩ =>
    ⟨hL.2 X Y hX hY, ?_⟩⟩
  · rcases hXU with h | h
    · exact Or.inr (Finset.compl_subset_compl.mpr h)
    · exact Or.inl (compl_le_iff_compl_le.mp h)
  · rcases hXU with h | h
    · exact Or.inl (Finset.inter_subset_left.trans h)
    · rcases hYU with h' | h'
      · exact Or.inl (Finset.inter_subset_right.trans h')
      · exact Or.inr (Finset.subset_inter h h')

/-- **Gluing.** Partial trees on the two sides of a minimum `s`–`t` cut `U`, joined by an edge
labelled `U`, form a partial tree. -/
private theorem glue [Preorder β] {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X)
    {L : Finset V → Prop} {R U : Finset V} {s t : V} (hs : s ∈ R) (ht : t ∈ R) (hLU : L U)
    (hU : IsMinCutBetween f s t U) {E₁ E₂ : Set (CEdge V)}
    (I₁ : Inv f (Restrict L U) (R ∩ U) E₁) (I₂ : Inv f (Restrict L Uᶜ) (R ∩ Uᶜ) E₂) :
    ∃ E, Inv f L R E := by
  have hsU : s ∈ U := hU.left_mem
  have htU : t ∉ U := hU.right_notMem
  -- Labels of `E₁` do not split `Uᶜ`; labels of `E₂` do not split `U`.
  have side₁ : ∀ e ∈ E₁, ∀ x y, x ∉ U → y ∉ U → (x ∈ e.S ↔ y ∈ e.S) := by
    intro e he x y hx hy
    rcases (I₁.good e he).2 with h | h
    · exact ⟨fun hx' => absurd (h hx') hx, fun hy' => absurd (h hy') hy⟩
    · exact ⟨fun _ => h (Finset.mem_compl.mpr hy), fun _ => h (Finset.mem_compl.mpr hx)⟩
  have side₂ : ∀ e ∈ E₂, ∀ x y, x ∈ U → y ∈ U → (x ∈ e.S ↔ y ∈ e.S) := by
    intro e he x y hx hy
    rcases (I₂.good e he).2 with h | h
    · exact ⟨fun hx' => absurd hx (Finset.mem_compl.mp (h hx')),
        fun hy' => absurd hy (Finset.mem_compl.mp (h hy'))⟩
    · rw [compl_compl] at h
      exact ⟨fun _ => h hy, fun _ => h hx⟩
  obtain ⟨r₁, hr₁, hr₁t⟩ := I₁.rep t
  obtain ⟨r₂, hr₂, hr₂s⟩ := I₂.rep s
  have hr₁U : r₁ ∈ U := (Finset.mem_inter.mp hr₁).2
  have hr₂U : r₂ ∉ U := Finset.mem_compl.mp (Finset.mem_inter.mp hr₂).2
  have out₁ : ∀ e ∈ E₁, ∀ x, x ∉ U → (x ∈ e.S ↔ r₁ ∈ e.S) := fun e he x hx =>
    (side₁ e he x t hx htU).trans (hr₁t e he)
  have in₂ : ∀ e ∈ E₂, ∀ x, x ∈ U → (x ∈ e.S ↔ r₂ ∈ e.S) := fun e he x hx =>
    (side₂ e he x s hx hsU).trans (hr₂s e he)
  have htR₂ : t ∈ R ∩ Uᶜ := Finset.mem_inter.mpr ⟨ht, Finset.mem_compl.mpr htU⟩
  have hsR₁ : s ∈ R ∩ U := Finset.mem_inter.mpr ⟨hs, hsU⟩
  -- The new edge `r₁ r₂` with label `U` is a minimum `r₁`–`r₂` cut.
  have newEdge : IsMinCutBetween f r₁ r₂ U := by
    refine ⟨hr₁U, hr₂U, fun Y h₁ h₂ => ?_⟩
    by_cases hsY : s ∈ Y <;> by_cases htY : t ∈ Y
    · obtain ⟨e, he, hsep, hY⟩ := exists_cross (I₂.chain t htR₂ r₂ hr₂) htY h₂
      have hst : s ∈ e.S ↔ t ∉ e.S := by
        have := in₂ e he s hsU
        tauto
      exact (hU.le_of_separates hsym hst).trans ((I₂.edge e he).le_of_separates hsym hY)
    · exact hU.le hsY htY
    · exact hU.le_of_separates hsym (by tauto)
    · obtain ⟨e, he, hsep, hY⟩ := exists_cross (Y := Yᶜ) (I₁.chain s hsR₁ r₁ hr₁)
        (Finset.mem_compl.mpr hsY) (fun h => Finset.mem_compl.mp h h₁)
      have hst : s ∈ e.S ↔ t ∉ e.S := by
        have := out₁ e he t htU
        tauto
      have hY' : e.u ∈ Y ↔ e.v ∉ Y := by
        simp only [Finset.mem_compl] at hY
        tauto
      exact (hU.le_of_separates hsym hst).trans ((I₁.edge e he).le_of_separates hsym hY')
  let enew : CEdge V := ⟨r₁, r₂, U⟩
  refine ⟨E₁ ∪ E₂ ∪ {enew}, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro e he
    rcases he with (he | he) | he
    · obtain ⟨h1, h2⟩ := I₁.mem e he
      exact ⟨(Finset.mem_inter.mp h1).1, (Finset.mem_inter.mp h2).1⟩
    · obtain ⟨h1, h2⟩ := I₂.mem e he
      exact ⟨(Finset.mem_inter.mp h1).1, (Finset.mem_inter.mp h2).1⟩
    · rw [Set.mem_singleton_iff] at he
      subst he
      exact ⟨(Finset.mem_inter.mp hr₁).1, (Finset.mem_inter.mp hr₂).1⟩
  · intro e he
    rcases he with (he | he) | he
    · exact (I₁.good e he).1
    · exact (I₂.good e he).1
    · rw [Set.mem_singleton_iff] at he
      subst he
      exact hLU
  · intro e he
    rcases he with (he | he) | he
    · exact I₁.edge e he
    · exact I₂.edge e he
    · rw [Set.mem_singleton_iff] at he
      subst he
      exact newEdge
  · have inU₁ : ∀ e ∈ E₁, e.u ∈ U ∧ e.v ∈ U := fun e he =>
      ⟨(Finset.mem_inter.mp (I₁.mem e he).1).2, (Finset.mem_inter.mp (I₁.mem e he).2).2⟩
    have outU₂ : ∀ e ∈ E₂, e.u ∉ U ∧ e.v ∉ U := fun e he =>
      ⟨Finset.mem_compl.mp (Finset.mem_inter.mp (I₂.mem e he).1).2,
        Finset.mem_compl.mp (Finset.mem_inter.mp (I₂.mem e he).2).2⟩
    intro e he e' he' hne
    rcases he with (he | he) | he <;> rcases he' with (he' | he') | he'
    · exact I₁.nest e he e' he' hne
    · exact side₁ e he _ _ (outU₂ e' he').1 (outU₂ e' he').2
    · rw [Set.mem_singleton_iff] at he'
      subst he'
      exact (out₁ e he r₂ hr₂U).symm
    · exact side₂ e he _ _ (inU₁ e' he').1 (inU₁ e' he').2
    · exact I₂.nest e he e' he' hne
    · rw [Set.mem_singleton_iff] at he'
      subst he'
      exact in₂ e he r₁ hr₁U
    · rw [Set.mem_singleton_iff] at he
      subst he
      exact ⟨fun _ => (inU₁ e' he').2, fun _ => (inU₁ e' he').1⟩
    · rw [Set.mem_singleton_iff] at he
      subst he
      exact ⟨fun h => absurd h (outU₂ e' he').1, fun h => absurd h (outU₂ e' he').2⟩
    · rw [Set.mem_singleton_iff] at he he'
      subst he he'
      exact absurd rfl hne
  · have cross : ∀ x ∈ R, ∀ y ∈ R, x ∈ U → y ∉ U →
        Relation.ReflTransGen (Step (E₁ ∪ E₂ ∪ {enew}) x y) x y := by
      intro x hx y hy hxU hyU
      have c₁ : Relation.ReflTransGen (Step (E₁ ∪ E₂ ∪ {enew}) x y) x r₁ :=
        step_mono (fun e he => ⟨Or.inl (Or.inl he), fun hsep => by
          have := out₁ e he y hyU
          tauto⟩) (I₁.chain x (Finset.mem_inter.mpr ⟨hx, hxU⟩) r₁ hr₁)
      have c₂ : Step (E₁ ∪ E₂ ∪ {enew}) x y r₁ r₂ :=
        ⟨enew, Or.inr rfl, ⟨fun _ => hyU, fun _ => hxU⟩, Or.inl ⟨rfl, rfl⟩⟩
      have c₃ : Relation.ReflTransGen (Step (E₁ ∪ E₂ ∪ {enew}) x y) r₂ y :=
        step_mono (fun e he => ⟨Or.inl (Or.inr he), fun hsep => by
          have := in₂ e he x hxU
          tauto⟩) (I₂.chain r₂ hr₂ y (Finset.mem_inter.mpr ⟨hy, Finset.mem_compl.mpr hyU⟩))
      exact c₁.trans (Relation.ReflTransGen.head c₂ c₃)
    intro x hx y hy
    by_cases hxU : x ∈ U <;> by_cases hyU : y ∈ U
    · exact step_mono (fun e he => ⟨Or.inl (Or.inl he), id⟩)
        (I₁.chain x (Finset.mem_inter.mpr ⟨hx, hxU⟩) y (Finset.mem_inter.mpr ⟨hy, hyU⟩))
    · exact cross x hx y hy hxU hyU
    · exact step_swap (cross y hy x hx hyU hxU)
    · exact step_mono (fun e he => ⟨Or.inl (Or.inr he), id⟩)
        (I₂.chain x (Finset.mem_inter.mpr ⟨hx, Finset.mem_compl.mpr hxU⟩) y
          (Finset.mem_inter.mpr ⟨hy, Finset.mem_compl.mpr hyU⟩))
  · intro z
    by_cases hz : z ∈ U
    · obtain ⟨r, hr, hzr⟩ := I₁.rep z
      refine ⟨r, (Finset.mem_inter.mp hr).1, fun e he => ?_⟩
      rcases he with (he | he) | he
      · exact hzr e he
      · exact side₂ e he z r hz (Finset.mem_inter.mp hr).2
      · rw [Set.mem_singleton_iff] at he
        subst he
        exact ⟨fun _ => (Finset.mem_inter.mp hr).2, fun _ => hz⟩
    · obtain ⟨r, hr, hzr⟩ := I₂.rep z
      have hrU : r ∉ U := Finset.mem_compl.mp (Finset.mem_inter.mp hr).2
      refine ⟨r, (Finset.mem_inter.mp hr).1, fun e he => ?_⟩
      rcases he with (he | he) | he
      · exact side₁ e he z r hz hrU
      · exact hzr e he
      · rw [Set.mem_singleton_iff] at he
        subst he
        exact ⟨fun h => absurd h hz, fun h => absurd h hrU⟩

variable [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]

/-- Restricting to one side `U` of a minimum `s`–`t` cut keeps minimum cuts between the
terminals of `R ∩ U`, by uncrossing. -/
private theorem exact_restrict {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X)
    (hsub : IsSubmodular f) {L : Finset V → Prop} (hL : Good L) {R U : Finset V} {s t : V}
    (hex : Exact f L R) (hLU : L U) (hU : IsMinCutBetween f s t U) :
    Exact f (Restrict L U) (R ∩ U) := by
  intro a ha b hb hab
  obtain ⟨haR, haU⟩ := Finset.mem_inter.mp ha
  obtain ⟨hbR, hbU⟩ := Finset.mem_inter.mp hb
  obtain ⟨X, hLX, hX⟩ := hex a haR b hbR hab
  by_cases htX : t ∈ X
  · -- Work with the complement, a minimum `b`–`a` cut missing `t`.
    have hY := (hX.compl hsym).inter hsub hU hbU (fun h => Finset.mem_compl.mp h htX)
    exact ⟨(Xᶜ ∩ U)ᶜ, (good_restrict hL U).1 _ ⟨hL.2 _ _ (hL.1 _ hLX) hLU,
      Or.inl Finset.inter_subset_right⟩, hY.compl hsym⟩
  · exact ⟨X ∩ U, ⟨hL.2 _ _ hLX hLU, Or.inl Finset.inter_subset_right⟩,
      hX.inter hsub hU haU htX⟩

/-- Partial trees exist on every nonempty set of terminals whose minimum cuts lie in a family
closed under complement and intersection. -/
private theorem exists_inv {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X) (hsub : IsSubmodular f) :
    ∀ (R : Finset V) (L : Finset V → Prop), R.Nonempty → Good L → Exact f L R →
      ∃ E, Inv f L R E := by
  intro R
  induction R using Finset.strongInduction with
  | H R ih =>
  intro L hne hL hex
  by_cases hone : ∀ a ∈ R, ∀ b ∈ R, a = b
  · obtain ⟨r, hr⟩ := hne
    refine ⟨∅, ⟨fun e he => he.elim, fun e he => he.elim, fun e he => he.elim,
      fun e he => he.elim, fun x hx y hy => ?_, fun _ => ⟨r, hr, fun e he => he.elim⟩⟩⟩
    obtain rfl := hone x hx y hy
    exact Relation.ReflTransGen.refl
  · push Not at hone
    obtain ⟨s, hs, t, ht, hst⟩ := hone
    obtain ⟨U, hLU, hU⟩ := hex s hs t ht hst
    have hss₁ : R ∩ U ⊂ R := (Finset.ssubset_iff_of_subset Finset.inter_subset_left).mpr
      ⟨t, ht, fun h => hU.right_notMem (Finset.mem_inter.mp h).2⟩
    have hss₂ : R ∩ Uᶜ ⊂ R := (Finset.ssubset_iff_of_subset Finset.inter_subset_left).mpr
      ⟨s, hs, fun h => Finset.mem_compl.mp (Finset.mem_inter.mp h).2 hU.left_mem⟩
    obtain ⟨E₁, I₁⟩ := ih _ hss₁ (Restrict L U)
      ⟨s, Finset.mem_inter.mpr ⟨hs, hU.left_mem⟩⟩ (good_restrict hL U)
      (exact_restrict hsym hsub hL hex hLU hU)
    obtain ⟨E₂, I₂⟩ := ih _ hss₂ (Restrict L Uᶜ)
      ⟨t, Finset.mem_inter.mpr ⟨ht, Finset.mem_compl.mpr hU.right_notMem⟩⟩ (good_restrict hL Uᶜ)
      (exact_restrict hsym hsub hL hex (hL.1 U hLU) (hU.compl hsym))
    exact glue hsym hs ht hLU hU I₁ I₂

/-- **Gomory–Hu theorem** for symmetric submodular set functions: every symmetric submodular
`f : Finset V → β` on a nonempty finite ground set `V` has a Gomory–Hu tree, a spanning tree `T` on
`V` in which for every edge `uv`, the side of `T - uv` containing `u` is a minimum `u`–`v` cut of
`f`. This is the cut-equivalent form. [GomoryHu1961] (see also [Schrijver2003], Section 15.4)
proves it for cut functions of undirected graphs; the statement for symmetric submodular functions
is the standard abstraction of that proof, which uses only symmetry and submodularity. The graph
case is `Cslib.Algorithms.Lean.GomoryHu.exists_isGomoryHuTree_cutWeight`. -/
theorem exists_isGomoryHuTree [Nonempty V] {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X)
    (hsub : IsSubmodular f) : ∃ T : SimpleGraph V, IsGomoryHuTree f T := by
  obtain ⟨r⟩ := ‹Nonempty V›
  obtain ⟨E, I⟩ := exists_inv hsym hsub Finset.univ (fun _ => True) ⟨r, Finset.mem_univ r⟩
    ⟨fun _ _ => trivial, fun _ _ _ _ => trivial⟩
    (fun a _ b _ hab => (exists_isMinCutBetween f hab).imp fun X hX => ⟨trivial, hX⟩)
  have hne : ∀ e ∈ E, e.u ≠ e.v := fun e he => (I.edge e he).ne
  let T : SimpleGraph V := SimpleGraph.fromRel fun x y => ∃ e ∈ E, e.u = x ∧ e.v = y
  have hadj : ∀ x y, T.Adj x y ↔ ∃ e ∈ E, (e.u = x ∧ e.v = y) ∨ (e.u = y ∧ e.v = x) := by
    intro x y
    simp only [T, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨_, ⟨e, he, h⟩ | ⟨e, he, h⟩⟩
      · exact ⟨e, he, Or.inl h⟩
      · exact ⟨e, he, Or.inr h⟩
    · rintro ⟨e, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨hne e he, Or.inl ⟨e, he, rfl, rfl⟩⟩
      · exact ⟨(hne e he).symm, Or.inr ⟨e, he, rfl, rfl⟩⟩
  -- Distinct edges have distinct endpoint pairs.
  have hsym2 : ∀ e ∈ E, ∀ e' ∈ E, e' ≠ e → s(e'.u, e'.v) ≠ s(e.u, e.v) := by
    intro e he e' he' hne' heq
    have hn := I.nest e he e' he' hne'.symm
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at hn
      exact (I.edge e he).right_notMem (hn.mp (I.edge e he).left_mem)
    · rw [h1, h2] at hn
      exact (I.edge e he).right_notMem (hn.mpr (I.edge e he).left_mem)
  -- Deleting the edge of `e` leaves exactly the two sides of `e.S`.
  have hreach : ∀ e ∈ E, ∀ x y,
      (T.deleteEdges {s(e.u, e.v)}).Reachable x y ↔ (x ∈ e.S ↔ y ∈ e.S) := by
    intro e he x y
    constructor
    · intro h
      rw [SimpleGraph.reachable_iff_reflTransGen] at h
      induction h with
      | refl => exact Iff.rfl
      | @tail b c _ hbc ih =>
        rw [SimpleGraph.deleteEdges_adj, hadj] at hbc
        obtain ⟨⟨e', he', hends⟩, hnot⟩ := hbc
        have hne' : e' ≠ e := by
          rintro rfl
          rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hnot rfl
          · exact hnot Sym2.eq_swap
        have hn := I.nest e he e' he' hne'.symm
        rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ih.trans hn
        · exact ih.trans hn.symm
    · intro hxy
      rw [SimpleGraph.reachable_iff_reflTransGen]
      refine Relation.ReflTransGen.mono (fun a b ⟨e', he', hsep, hends⟩ => ?_) _ _
        (I.chain x (Finset.mem_univ x) y (Finset.mem_univ y))
      have hne' : e' ≠ e := by
        rintro rfl
        tauto
      rw [SimpleGraph.deleteEdges_adj, hadj]
      refine ⟨⟨e', he', hends⟩, fun h => hsym2 e he e' he' hne' ?_⟩
      rw [Set.mem_singleton_iff] at h
      rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h
      · exact Sym2.eq_swap.trans h
  have htree : T.IsTree := by
    refine ⟨⟨fun x y => ?_⟩, ?_⟩
    · rw [SimpleGraph.reachable_iff_reflTransGen]
      exact Relation.ReflTransGen.mono (fun a b ⟨e, he, _, hends⟩ => (hadj a b).mpr ⟨e, he, hends⟩)
        _ _ (I.chain x (Finset.mem_univ x) y (Finset.mem_univ y))
    · rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
      intro p q hpq
      obtain ⟨e, he, hends⟩ := (hadj p q).mp hpq
      rw [SimpleGraph.isBridge_iff]
      rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hreach e he]
        exact fun h => (I.edge e he).right_notMem (h.mp (I.edge e he).left_mem)
      · rw [Sym2.eq_swap, hreach e he]
        exact fun h => (I.edge e he).right_notMem (h.mpr (I.edge e he).left_mem)
  refine ⟨T, htree, fun u v huv => ?_⟩
  obtain ⟨e, he, hends⟩ := (hadj u v).mp huv
  rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have : edgeSide T e.u e.v = e.S := by
      ext x
      rw [mem_edgeSide, hreach e he]
      exact ⟨fun h => h.mp (I.edge e he).left_mem, fun h => ⟨fun _ => h, fun _ =>
        (I.edge e he).left_mem⟩⟩
    rw [this]
    exact I.edge e he
  · have : edgeSide T e.v e.u = e.Sᶜ := by
      ext x
      rw [mem_edgeSide, Sym2.eq_swap, hreach e he, Finset.mem_compl]
      have h1 := (I.edge e he).right_notMem
      constructor
      · intro h hx
        exact h1 (h.mpr hx)
      · intro h
        exact ⟨fun hv => absurd hv h1, fun hx => absurd hx h⟩
    rw [this]
    exact (I.edge e he).compl hsym

end Construction

end Cslib.Algorithms.Lean.GomoryHu
