/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.GomoryHu.Basic

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
    ⟨e, he, ⟨fun hx hy => hsep.mp hy hx,
      fun hy => Classical.byContradiction fun hx => hy (hsep.mpr hx)⟩, hends.symm⟩) _ _
    (Relation.reflTransGen_swap.mpr h)

/-- A property of all edges of `E₁`, `E₂` and the edge `e` holds on `E₁ ∪ E₂ ∪ {e}`. -/
private theorem forall_mem_union_insert {E₁ E₂ : Set (CEdge V)} {e : CEdge V}
    {P : CEdge V → Prop} (h₁ : ∀ e ∈ E₁, P e) (h₂ : ∀ e ∈ E₂, P e) (he : P e) :
    ∀ e' ∈ E₁ ∪ E₂ ∪ {e}, P e' := by
  rintro e' ((h | h) | h)
  · exact h₁ e' h
  · exact h₂ e' h
  · rw [Set.mem_singleton_iff] at h
    subst h
    exact he

/-! ### From a partial tree on all vertices to a Gomory–Hu tree -/

section Tree

variable [Preorder β] {f : Finset V → β} {L : Finset V → Prop} {R : Finset V}

/-- The graph on `V` whose edges are the endpoint pairs of the labelled edges `E`. -/
private def treeOf (E : Set (CEdge V)) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y => ∃ e ∈ E, e.u = x ∧ e.v = y

private theorem Inv.treeOf_adj {E : Set (CEdge V)} (I : Inv f L R E) {x y : V} :
    (treeOf E).Adj x y ↔ ∃ e ∈ E, (e.u = x ∧ e.v = y) ∨ (e.u = y ∧ e.v = x) := by
  simp only [treeOf, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, ⟨e, he, h⟩ | ⟨e, he, h⟩⟩
    · exact ⟨e, he, Or.inl h⟩
    · exact ⟨e, he, Or.inr h⟩
  · rintro ⟨e, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨(I.edge e he).ne, Or.inl ⟨e, he, rfl, rfl⟩⟩
    · exact ⟨(I.edge e he).ne.symm, Or.inr ⟨e, he, rfl, rfl⟩⟩

/-- A tree edge other than that of `e` does not cross the label of `e`. -/
private theorem Inv.mem_iff_of_adj {E : Set (CEdge V)} (I : Inv f L R E) {e : CEdge V}
    (he : e ∈ E) {x y : V}
    (hxy : (treeOf E).Adj x y) (hne : s(x, y) ≠ s(e.u, e.v)) : x ∈ e.S ↔ y ∈ e.S := by
  obtain ⟨e', he', hends⟩ := I.treeOf_adj.mp hxy
  have hee' : e ≠ e' := by
    rintro rfl
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne rfl
    · exact hne Sym2.eq_swap
  rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact I.nest e he e' he' hee'
  · exact (I.nest e he e' he' hee').symm

/-- Deleting the edge of `e` from the tree leaves no path across the label of `e`. -/
private theorem Inv.mem_iff_of_reachable {E : Set (CEdge V)} (I : Inv f L R E) {e : CEdge V}
    (he : e ∈ E) {x y : V}
    (h : ((treeOf E).deleteEdges {s(e.u, e.v)}).Reachable x y) : x ∈ e.S ↔ y ∈ e.S := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Iff.rfl
  | tail _ hbc ih =>
    rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at hbc
    exact ih.trans (I.mem_iff_of_adj he hbc.1 hbc.2)

/-- A partial tree on all vertices is a spanning tree. -/
private theorem Inv.isTree [Fintype V] [Nonempty V] {E : Set (CEdge V)}
    (I : Inv f L Finset.univ E) :
    (treeOf E).IsTree := by
  refine ⟨⟨fun x y => ?_⟩, ?_⟩
  · rw [SimpleGraph.reachable_iff_reflTransGen]
    exact Relation.ReflTransGen.mono
      (fun a b ⟨e, he, _, hends⟩ => I.treeOf_adj.mpr ⟨e, he, hends⟩) _ _
      (I.chain x (Finset.mem_univ x) y (Finset.mem_univ y))
  · rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
    intro p q hpq
    obtain ⟨e, he, hends⟩ := I.treeOf_adj.mp hpq
    rw [SimpleGraph.isBridge_iff]
    have hS := I.edge e he
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fun h => hS.right_notMem ((I.mem_iff_of_reachable he h).mp hS.left_mem)
    · rw [Sym2.eq_swap]
      exact fun h => hS.right_notMem ((I.mem_iff_of_reachable he h).mpr hS.left_mem)

end Tree

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

/-- A set that does not split `Uᶜ` contains both or neither of two vertices outside `U`. -/
private theorem Restrict.mem_iff {L : Finset V → Prop} {U X : Finset V} (h : Restrict L U X)
    {x y : V} (hx : x ∉ U) (hy : y ∉ U) : x ∈ X ↔ y ∈ X := by
  rcases h.2 with h | h
  · exact ⟨fun hx' => absurd (h hx') hx, fun hy' => absurd (h hy') hy⟩
  · exact ⟨fun _ => h (Finset.mem_compl.mpr hy), fun _ => h (Finset.mem_compl.mpr hx)⟩

/-- **Gluing.** Partial trees on the two sides of a minimum `s`–`t` cut `U`, joined by an edge
labelled `U`, form a partial tree. -/
private theorem glue [Preorder β] {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X)
    {L : Finset V → Prop} {R U : Finset V} {s t : V} (hs : s ∈ R) (ht : t ∈ R) (hLU : L U)
    (hU : IsMinCutBetween f s t U) {E₁ E₂ : Set (CEdge V)}
    (I₁ : Inv f (Restrict L U) (R ∩ U) E₁) (I₂ : Inv f (Restrict L Uᶜ) (R ∩ Uᶜ) E₂) :
    ∃ E, Inv f L R E := by
  have hsU : s ∈ U := hU.left_mem
  have htU : t ∉ U := hU.right_notMem
  -- Endpoints of `E₁` lie in `U` and those of `E₂` outside it.
  have inU₁ : ∀ e ∈ E₁, e.u ∈ U ∧ e.v ∈ U := fun e he =>
    ⟨Finset.mem_of_mem_inter_right (I₁.mem e he).1,
      Finset.mem_of_mem_inter_right (I₁.mem e he).2⟩
  have outU₂ : ∀ e ∈ E₂, e.u ∉ U ∧ e.v ∉ U := fun e he =>
    ⟨Finset.mem_compl.mp (Finset.mem_of_mem_inter_right (I₂.mem e he).1),
      Finset.mem_compl.mp (Finset.mem_of_mem_inter_right (I₂.mem e he).2)⟩
  -- Labels of `E₁` do not split `Uᶜ`; labels of `E₂` do not split `U`.
  have side₁ : ∀ e ∈ E₁, ∀ x y, x ∉ U → y ∉ U → (x ∈ e.S ↔ y ∈ e.S) := fun e he _ _ =>
    (I₁.good e he).mem_iff
  have side₂ : ∀ e ∈ E₂, ∀ x y, x ∈ U → y ∈ U → (x ∈ e.S ↔ y ∈ e.S) := fun e he _ _ hx hy =>
    (I₂.good e he).mem_iff (Finset.notMem_compl.mpr hx) (Finset.notMem_compl.mpr hy)
  obtain ⟨r₁, hr₁, hr₁t⟩ := I₁.rep t
  obtain ⟨r₂, hr₂, hr₂s⟩ := I₂.rep s
  have hr₁U : r₁ ∈ U := Finset.mem_of_mem_inter_right hr₁
  have hr₂U : r₂ ∉ U := Finset.mem_compl.mp (Finset.mem_of_mem_inter_right hr₂)
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
      have hst : s ∈ e.S ↔ t ∉ e.S := by grind
      exact (hU.le_of_separates hsym hst).trans ((I₂.edge e he).le_of_separates hsym hY)
    · exact hU.le hsY htY
    · exact hU.le_of_separates hsym (iff_of_false hsY (not_not.mpr htY))
    · obtain ⟨e, he, hsep, hY⟩ := exists_cross (Y := Yᶜ) (I₁.chain s hsR₁ r₁ hr₁)
        (Finset.mem_compl.mpr hsY) (fun h => Finset.mem_compl.mp h h₁)
      have hst : s ∈ e.S ↔ t ∉ e.S := by grind
      have hY' : e.u ∈ Y ↔ e.v ∉ Y := by grind [Finset.mem_compl]
      exact (hU.le_of_separates hsym hst).trans ((I₁.edge e he).le_of_separates hsym hY')
  let enew : CEdge V := ⟨r₁, r₂, U⟩
  refine ⟨E₁ ∪ E₂ ∪ {enew}, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact forall_mem_union_insert
      (fun e he => ⟨Finset.mem_of_mem_inter_left (I₁.mem e he).1,
        Finset.mem_of_mem_inter_left (I₁.mem e he).2⟩)
      (fun e he => ⟨Finset.mem_of_mem_inter_left (I₂.mem e he).1,
        Finset.mem_of_mem_inter_left (I₂.mem e he).2⟩)
      ⟨Finset.mem_of_mem_inter_left hr₁, Finset.mem_of_mem_inter_left hr₂⟩
  · exact forall_mem_union_insert (fun e he => (I₁.good e he).1) (fun e he => (I₂.good e he).1)
      hLU
  · exact forall_mem_union_insert I₁.edge I₂.edge newEdge
  · -- Nesting: within each side by induction, across the sides by `side₁`/`side₂`, and for the
    -- new edge because each side lies on one side of `U`.
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
  · -- Chains: within each side, and across `U` through the new edge `r₁ r₂`.
    have cross : ∀ x ∈ R, ∀ y ∈ R, x ∈ U → y ∉ U →
        Relation.ReflTransGen (Step (E₁ ∪ E₂ ∪ {enew}) x y) x y := by
      intro x hx y hy hxU hyU
      have c₁ : Relation.ReflTransGen (Step (E₁ ∪ E₂ ∪ {enew}) x y) x r₁ :=
        step_mono (fun e he => ⟨Or.inl (Or.inl he), fun hsep =>
          hsep.trans (not_congr (out₁ e he y hyU)).symm⟩)
          (I₁.chain x (Finset.mem_inter.mpr ⟨hx, hxU⟩) r₁ hr₁)
      have c₂ : Step (E₁ ∪ E₂ ∪ {enew}) x y r₁ r₂ :=
        ⟨enew, Or.inr rfl, ⟨fun _ => hyU, fun _ => hxU⟩, Or.inl ⟨rfl, rfl⟩⟩
      have c₃ : Relation.ReflTransGen (Step (E₁ ∪ E₂ ∪ {enew}) x y) r₂ y :=
        step_mono (fun e he => ⟨Or.inl (Or.inr he), fun hsep =>
          (in₂ e he x hxU).trans hsep⟩)
          (I₂.chain r₂ hr₂ y (Finset.mem_inter.mpr ⟨hy, Finset.mem_compl.mpr hyU⟩))
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
  · -- Representatives: from the side of `U` containing the vertex.
    intro z
    by_cases hz : z ∈ U
    · obtain ⟨r, hr, hzr⟩ := I₁.rep z
      have hrU : r ∈ U := Finset.mem_of_mem_inter_right hr
      exact ⟨r, Finset.mem_of_mem_inter_left hr, forall_mem_union_insert hzr
        (fun e he => side₂ e he z r hz hrU) ⟨fun _ => hrU, fun _ => hz⟩⟩
    · obtain ⟨r, hr, hzr⟩ := I₂.rep z
      have hrU : r ∉ U := Finset.mem_compl.mp (Finset.mem_of_mem_inter_right hr)
      exact ⟨r, Finset.mem_of_mem_inter_left hr, forall_mem_union_insert
        (fun e he => side₁ e he z r hz hrU) hzr
        ⟨fun h => absurd h hz, fun h => absurd h hrU⟩⟩

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
  have htree := I.isTree
  refine ⟨treeOf E, htree, fun u v huv => ?_⟩
  obtain ⟨e, he, hends⟩ := I.treeOf_adj.mp huv
  have hS := I.edge e he
  have hadj : (treeOf E).Adj e.u e.v := I.treeOf_adj.mpr ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  -- No other tree edge crosses `e.S`, so it is the side of the edge of `e` containing `e.u`.
  have hside : edgeSide (treeOf E) e.u e.v = e.S :=
    SimpleGraph.edgeSide_eq_of_forall_adj htree hadj hS.left_mem hS.right_notMem (by
      intro x y hxy hne
      exact I.mem_iff_of_adj he hxy hne)
  rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hside]
    exact hS
  · rw [SimpleGraph.edgeSide_swap htree hadj, hside]
    exact hS.compl hsym

end Construction

end Cslib.Algorithms.Lean.GomoryHu
