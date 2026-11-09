/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.ConstraintGraph
public import CslibFrontier.Foundations.Combinatorics.Expander.Loops

/-!
# Constraint graphs on a regular multigraph

The steps of Dinur's proof after preprocessing [Dinur, Section 3][Dinur2005] run on constraint
graphs whose underlying multigraph is regular, since this is what makes random walks and the
spectral expansion `λ` available. A `RegularConstraintGraph V D α` is a `D`-regular multigraph on
`V`, presented by its rotation map (`Cslib.RotationMap`), together with a constraint on each of its
**darts** `(v, i)`, the `i`-th edge at `v` seen from `v`: a relation between the label of `v` and
that of its `i`-th neighbor. Its constraint graph (`toConstraintGraph`) has the darts as edges, so
its proportions of violated constraints are taken over the uniform distribution on darts, which is
the stationary distribution of the edges crossed by the random walk.

An undirected edge has two darts, and their constraints are not required to agree. Nothing is lost:
an undirected constraint is given by the same relation on both darts, read in the two directions,
and the estimates of the proof are stated over darts anyway.

Two regular constraint graphs on the same vertices superpose to their union (`union`), whose
constraint graph is the union of theirs up to the renaming `V × (D ⊕ D') ≃ (V × D) ⊕ (V × D')` of
the darts (`toConstraintGraph_union`). In particular, constraints that always hold may be added on
the edges of a second regular multigraph on the same vertices (`addTrivial`), as the union with an
`unconstrained` regular constraint graph. The violated darts are then the same, and the proportion
of violated darts drops by the factor `|D| / (|D| + |D'|)` (`unsatVal_addTrivial`). Dinur adds the
edges of an expander in this way, to make the underlying multigraph an expander, and self-loops
(`addLoops`), which his powering step along walks of a fixed length needs.

## Main definitions

* `Cslib.PCP.RegularConstraintGraph`: a rotation map with a constraint on each dart.
* `Cslib.PCP.RegularConstraintGraph.toConstraintGraph`: its constraint graph, whose edges are the
  darts.
* `Cslib.PCP.RegularConstraintGraph.union`: two regular constraint graphs on the same vertices,
  superposed.
* `Cslib.PCP.RegularConstraintGraph.unconstrained`: a rotation map with constraints that always
  hold.
* `Cslib.PCP.RegularConstraintGraph.addTrivial`: the edges of another regular multigraph added,
  with constraints that always hold.
* `Cslib.PCP.RegularConstraintGraph.addLoops`: self-loops added, with constraints that always hold.

## Main results

* `Cslib.PCP.RegularConstraintGraph.toConstraintGraph_union`,
  `Cslib.PCP.RegularConstraintGraph.satisfiable_union_iff`: the constraint graph of a union.
* `Cslib.PCP.RegularConstraintGraph.unsatVal_addTrivial`,
  `Cslib.PCP.RegularConstraintGraph.satisfiable_addTrivial_iff`: adding edges with constraints that
  always hold scales the value by `|D| / (|D| + |D'|)` and preserves satisfiability.
* `Cslib.PCP.RegularConstraintGraph.unsatVal_addLoops`,
  `Cslib.PCP.RegularConstraintGraph.satisfiable_addLoops_iff`: the same for self-loops.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [I. Dinur, *The PCP theorem by gap amplification*, ECCC TR05-046, revision 1][Dinur2005]
-/

@[expose] public section

namespace Cslib.PCP

open Finset

/-- A **regular constraint graph**: a `D`-regular multigraph on `V`, presented by its rotation map,
with a constraint over the alphabet `α` on each of its darts. The constraint `rel (v, i)` relates
the label of `v` to that of its `i`-th neighbor. -/
structure RegularConstraintGraph (V D α : Type*) where
  /-- The underlying regular multigraph. -/
  graph : RotationMap V D
  /-- The constraint on a dart `(v, i)`: a relation between the label of `v` and that of its
  `i`-th neighbor. -/
  rel : V × D → α → α → Prop

namespace RegularConstraintGraph

variable {V D D' α : Type*} (R : RegularConstraintGraph V D α)

/-- The constraint graph of a regular constraint graph: its edges are the darts, the dart `(v, i)`
going from `v` to its `i`-th neighbor. -/
def toConstraintGraph : ConstraintGraph V (V × D) α where
  src := Prod.fst
  dst p := R.graph.neighbor p.1 p.2
  rel := R.rel

variable {R} in
/-- A labelling satisfies a dart when the labels of its ends satisfy its constraint. -/
@[simp]
theorem satisfies_toConstraintGraph_iff {σ : V → α} {p : V × D} :
    R.toConstraintGraph.Satisfies σ p ↔ R.rel p (σ p.1) (σ (R.graph.neighbor p.1 p.2)) :=
  Iff.rfl

/-- The number of violated darts is the proportion of violated darts times the number `|V| |D|`
of darts. -/
theorem card_mul_card_mul_unsatFrac [Fintype V] [Fintype D] (σ : V → α) :
    Fintype.card V * Fintype.card D * R.toConstraintGraph.unsatFrac σ =
      #(R.toConstraintGraph.unsatEdges σ) := by
  rw [← Nat.cast_mul, ← Fintype.card_prod, ConstraintGraph.card_mul_unsatFrac]

section Union

variable (R' : RegularConstraintGraph V D' α)

/-- The **union** of two regular constraint graphs on the same vertices: its multigraph is the
union of theirs, the darts `inl i` at `v` being those of `R` and the darts `inr j` those of `R'`,
and every dart keeps its constraint. -/
def union : RegularConstraintGraph V (D ⊕ D') α where
  graph := R.graph.union R'.graph
  rel p := p.2.elim (fun i ↦ R.rel (p.1, i)) fun j ↦ R'.rel (p.1, j)

/-- The underlying multigraph of a union is the union of the underlying multigraphs. -/
@[simp]
theorem graph_union : (R.union R').graph = R.graph.union R'.graph :=
  rfl

/-- The darts of `R` keep their constraints in `R.union R'`. -/
@[simp]
theorem rel_union_inl (v : V) (i : D) : (R.union R').rel (v, .inl i) = R.rel (v, i) :=
  rfl

/-- The darts of `R'` keep their constraints in `R.union R'`. -/
@[simp]
theorem rel_union_inr (v : V) (j : D') : (R.union R').rel (v, .inr j) = R'.rel (v, j) :=
  rfl

/-- The constraint graph of a union is the union of the constraint graphs, with its darts
`V × (D ⊕ D')` renamed to `(V × D) ⊕ (V × D')`. -/
theorem toConstraintGraph_union : (R.union R').toConstraintGraph =
    (R.toConstraintGraph.union R'.toConstraintGraph).comap (Equiv.prodSumDistrib V D D') := by
  ext ⟨v, i | j⟩ <;> rfl

/-- A union is satisfied by the labellings that satisfy both regular constraint graphs. -/
theorem satisfiable_union_iff :
    (R.union R').toConstraintGraph.Satisfiable ↔ ∃ σ : V → α,
      (∀ p, R.toConstraintGraph.Satisfies σ p) ∧ ∀ p, R'.toConstraintGraph.Satisfies σ p := by
  rw [toConstraintGraph_union, ConstraintGraph.satisfiable_comap_iff _ (Equiv.surjective _),
    ConstraintGraph.satisfiable_union_iff]

end Union

section AddTrivial

/-- The regular constraint graph on the multigraph `H` whose constraints always hold. -/
def unconstrained (H : RotationMap V D) : RegularConstraintGraph V D α where
  graph := H
  rel _ _ _ := True

/-- An unconstrained regular constraint graph is satisfied by every labelling. -/
theorem satisfies_unconstrained (H : RotationMap V D) (σ : V → α) (p : V × D) :
    (unconstrained H).toConstraintGraph.Satisfies σ p :=
  True.intro

/-- The regular constraint graph `R` with the edges of `H` added, carrying constraints that always
hold: its union with the unconstrained regular constraint graph on `H`. -/
def addTrivial (H : RotationMap V D') : RegularConstraintGraph V (D ⊕ D') α :=
  R.union (unconstrained H)

variable (H : RotationMap V D')

/-- The underlying multigraph of `R.addTrivial H` is the union of those of `R` and `H`. -/
@[simp]
theorem graph_addTrivial : (R.addTrivial H).graph = R.graph.union H :=
  rfl

/-- The darts of `R` keep their constraints in `R.addTrivial H`. -/
@[simp]
theorem rel_addTrivial_inl (v : V) (i : D) : (R.addTrivial H).rel (v, .inl i) = R.rel (v, i) :=
  rfl

/-- The constraints on the added darts always hold. -/
@[simp]
theorem rel_addTrivial_inr (v : V) (j : D') (a b : α) : (R.addTrivial H).rel (v, .inr j) a b :=
  True.intro

variable {R H} in
/-- The darts of `R` keep their constraints in `R.addTrivial H`. -/
theorem satisfies_addTrivial_inl {σ : V → α} {v : V} {i : D} :
    (R.addTrivial H).toConstraintGraph.Satisfies σ (v, .inl i) ↔
      R.toConstraintGraph.Satisfies σ (v, i) :=
  Iff.rfl

variable {R} in
/-- The added darts are satisfied by every labelling. -/
theorem satisfies_addTrivial_inr (σ : V → α) (v : V) (j : D') :
    (R.addTrivial H).toConstraintGraph.Satisfies σ (v, .inr j) :=
  True.intro

/-- Adding edges with constraints that always hold preserves satisfiability. -/
theorem satisfiable_addTrivial_iff :
    (R.addTrivial H).toConstraintGraph.Satisfiable ↔ R.toConstraintGraph.Satisfiable := by
  rw [addTrivial, satisfiable_union_iff]
  exact ⟨fun ⟨σ, hσ, _⟩ ↦ ⟨σ, hσ⟩, fun ⟨σ, hσ⟩ ↦ ⟨σ, hσ, satisfies_unconstrained H σ⟩⟩

variable [Fintype V] [Fintype D] [Fintype D']

/-- **Adding edges with constraints that always hold** scales the value by
`|D| / (|D| + |D'|)`: the constraint graph of `R.addTrivial H` is the union of that of `R` with
`|V| |D'|` edges that are always satisfied. -/
theorem unsatVal_addTrivial :
    (R.addTrivial H).toConstraintGraph.unsatVal =
      Fintype.card D / (Fintype.card D + Fintype.card D') * R.toConstraintGraph.unsatVal := by
  rw [addTrivial, toConstraintGraph_union, ConstraintGraph.unsatVal_comap_equiv,
    ConstraintGraph.unsatVal_union_of_forall_rel _ _ fun _ _ _ ↦ True.intro, Fintype.card_prod,
    Fintype.card_prod]
  rcases isEmpty_or_nonempty V with hV | hV
  · rw [R.toConstraintGraph.unsatVal_of_isEmpty, mul_zero, mul_zero]
  · have hV' : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    push_cast
    rw [← mul_add, mul_div_mul_left _ _ hV']

end AddTrivial

section AddLoops

variable (E : Type*)

/-- The regular constraint graph `R` with a self-loop added at every vertex for each `j : E`,
carrying constraints that always hold: its underlying multigraph is `R.graph.addLoops E`. -/
def addLoops : RegularConstraintGraph V (D ⊕ E) α :=
  R.addTrivial (RotationMap.loops V E)

/-- The underlying multigraph of `R.addLoops E` is that of `R` with self-loops added. -/
@[simp]
theorem graph_addLoops : (R.addLoops E).graph = R.graph.addLoops E :=
  rfl

/-- Adding self-loops with constraints that always hold preserves satisfiability. -/
theorem satisfiable_addLoops_iff :
    (R.addLoops E).toConstraintGraph.Satisfiable ↔ R.toConstraintGraph.Satisfiable :=
  R.satisfiable_addTrivial_iff _

/-- **Adding self-loops** with constraints that always hold scales the value by
`|D| / (|D| + |E|)`. -/
theorem unsatVal_addLoops [Fintype V] [Fintype D] [Fintype E] :
    (R.addLoops E).toConstraintGraph.unsatVal =
      Fintype.card D / (Fintype.card D + Fintype.card E) * R.toConstraintGraph.unsatVal :=
  R.unsatVal_addTrivial _

end AddLoops

end RegularConstraintGraph

end Cslib.PCP
