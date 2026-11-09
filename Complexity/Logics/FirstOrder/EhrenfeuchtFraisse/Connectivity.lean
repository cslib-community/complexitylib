/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.EhrenfeuchtFraisse.DefinedGraph
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Sort

/-!
# Connectivity is not first-order definable

A finite simple graph `G` on `V` is a structure in Mathlib's language of graphs
`FirstOrder.Language.graph` through `SimpleGraph.structure`. **No first-order sentence in this
language holds in exactly the connected finite graphs** (`not_exists_sentence_connected`), and this
remains true when only graphs with at least `t` vertices are considered
(`not_exists_sentence_connected_of_le_card`).

The proof reduces EVEN on finite linear orders to connectivity. The *step-two graph* of a linear
order joins each element to the element two steps above it, and closes the ends: the last element
is joined to the second one and the penultimate element to the first one (`stepTwoGraph`). On an
order with an odd number of elements this graph is a single cycle through all elements; on an order
with an even number of elements it is the disjoint union of the even and the odd positions
(`stepTwoGraph_connected_iff_odd`). Its arcs are first-order definable from `≤`
(`stepTwoArcFormula`), so it is the graph defined by a formula in the sense of
`Complexity.Logics.FirstOrder.EhrenfeuchtFraisse.DefinedGraph` (`stepTwoGraph_eq_definedGraph`), and
the parity transfer `DefinedGraph.not_exists_sentence_of_odd` turns a sentence defining
connectivity into a sentence of the language of orders expressing that a finite linear order has an
odd number of elements, which the Ehrenfeucht–Fraïssé theorem for finite linear orders rules out.

The sentences range over the pure graph vocabulary, with no built-in order or arithmetic. In
ordered descriptive complexity (Immerman's conventions, with numeric predicates `≤` and `BIT`),
connectivity is still not first-order definable, but that follows from circuit lower bounds for
parity, not from this argument. Connectivity of undirected graphs is decidable in logarithmic space
(`USTCON_mem_L`), so this gives a concrete logspace graph property that first-order logic without
order cannot express.

## Main definitions

* `Cslib.Logic.FO.Connectivity.stepTwoGraph`: the step-two graph of a linear order.
* `Cslib.Logic.FO.Connectivity.stepTwoArcFormula`: the formula of the language of orders defining
  its arcs.

## Main results

* `Cslib.Logic.FO.Connectivity.stepTwoGraph_connected_iff_odd`: the step-two graph of a finite
  linear order is connected iff the order has an odd number of elements.
* `Cslib.Logic.FO.Connectivity.stepTwoGraph_eq_definedGraph`: the step-two graph is the graph
  defined by `stepTwoArcFormula`.
* `Cslib.Logic.FO.Connectivity.not_exists_sentence_connected`: connectivity of finite graphs is
  not first-order definable.
* `Cslib.Logic.FO.Connectivity.not_exists_sentence_connected_of_le_card`: the same for graphs with
  at least `t` vertices.

## References

* [H.-D. Ebbinghaus and J. Flum, *Finite Model Theory*][EbbinghausFlum1999], Chapter 2
  (Ehrenfeucht–Fraïssé games and nondefinability of connectivity).
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Corollary 3.19 (connectivity is not
  definable, by a reduction from EVEN on linear orders).
-/

public section

open FirstOrder Language Structure

namespace Cslib.Logic.FO.Connectivity

open DefinedGraph

universe u

/-! ### The arc formula -/

variable {α : Type*}

/-- The formula of the language of orders defining `StepTwoArc`. -/
noncomputable def stepTwoArcFormula (x y : α) : Language.order.Formula α :=
  twoAboveFormula x y ⊔ (isTopFormula x ⊓ isSecondFormula y) ⊔
    (isPenultimateFormula x ⊓ isBotFormula y)

/-! ### The step-two graph -/

variable {M : Type*} [LinearOrder M]

variable (M) in
/-- The arcs of the step-two graph of a linear order: from `x` to the element two steps above it,
from the greatest element to the second least element, and from the second greatest element to the
least element. -/
def StepTwoArc (x y : M) : Prop :=
  (∃ z, x ⋖ z ∧ z ⋖ y) ∨ ((∀ t, t ≤ x) ∧ ∃ z, (∀ t, z ≤ t) ∧ z ⋖ y) ∨
    ((∃ z, (∀ t, t ≤ z) ∧ x ⋖ z) ∧ ∀ t, y ≤ t)

/-- Unfolding `StepTwoArc`. -/
theorem stepTwoArc_iff {x y : M} :
    StepTwoArc M x y ↔ (∃ z, x ⋖ z ∧ z ⋖ y) ∨ ((∀ t, t ≤ x) ∧ ∃ z, (∀ t, z ≤ t) ∧ z ⋖ y) ∨
      ((∃ z, (∀ t, t ≤ z) ∧ x ⋖ z) ∧ ∀ t, y ≤ t) :=
  Iff.rfl

variable (M) in
/-- The **step-two graph** of a linear order: distinct elements are adjacent when there is a
`StepTwoArc` between them in either direction. On a finite linear order with `m` elements
`0 < 1 < ⋯ < m - 1`, this joins `i` and `i + 2`, `m - 1` and `1`, and `m - 2` and `0`. -/
def stepTwoGraph : SimpleGraph M where
  Adj x y := x ≠ y ∧ (StepTwoArc M x y ∨ StepTwoArc M y x)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Unfolding adjacency in `stepTwoGraph`. -/
theorem stepTwoGraph_adj {x y : M} :
    (stepTwoGraph M).Adj x y ↔ x ≠ y ∧ (StepTwoArc M x y ∨ StepTwoArc M y x) :=
  Iff.rfl

/-! ### Realizing the arc formula -/

section Realize

variable [Language.order.Structure M] [Language.order.OrderedStructure M]

/-- `stepTwoArcFormula` defines `StepTwoArc`. -/
@[simp]
theorem realize_stepTwoArcFormula (v : α → M) (x y : α) :
    (stepTwoArcFormula x y).Realize v ↔ StepTwoArc M (v x) (v y) := by
  simp only [stepTwoArcFormula, Formula.realize_sup, Formula.realize_inf,
    realize_twoAboveFormula, realize_isTopFormula, realize_isSecondFormula,
    realize_isPenultimateFormula, realize_isBotFormula, stepTwoArc_iff, or_assoc]

end Realize

/-! ### The step-two graph on `Fin m` -/

/-- The arcs of the step-two graph on `Fin m`, in terms of values. -/
theorem stepTwoArc_fin_iff {m : ℕ} (x y : Fin m) :
    StepTwoArc (Fin m) x y ↔ (x : ℕ) + 2 = y ∨ ((x : ℕ) + 1 = m ∧ (y : ℕ) = 1) ∨
      ((x : ℕ) + 2 = m ∧ (y : ℕ) = 0) := by
  have hx := x.2
  have hy := y.2
  simp only [stepTwoArc_iff, Fin.covBy_iff, Nat.covBy_iff_add_one_eq, Fin.le_def]
  refine or_congr ⟨?_, ?_⟩ (or_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩)
  · rintro ⟨z, h₁, h₂⟩
    omega
  · intro h
    exact ⟨⟨x + 1, by omega⟩, rfl, by simp only; omega⟩
  · rintro ⟨h₁, z, h₂, h₃⟩
    have := h₁ ⟨m - 1, by omega⟩
    have := h₂ ⟨0, by omega⟩
    simp only at *
    omega
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun t => by have := t.2; omega, ⟨0, by omega⟩, fun t => Nat.zero_le _,
      by simp only; omega⟩
  · rintro ⟨⟨z, h₁, h₂⟩, h₃⟩
    have := h₁ ⟨m - 1, by omega⟩
    have := h₃ ⟨0, by omega⟩
    have := z.2
    simp only at *
    omega
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨⟨m - 1, by omega⟩, fun t => by have := t.2; simp only; omega, by simp only; omega⟩,
      fun t => by omega⟩

/-- Adjacency in the step-two graph on `Fin m`, in terms of values. -/
theorem stepTwoGraph_adj_fin_iff {m : ℕ} (x y : Fin m) :
    (stepTwoGraph (Fin m)).Adj x y ↔ (x : ℕ) ≠ y ∧
      ((x : ℕ) + 2 = y ∨ ((x : ℕ) + 1 = m ∧ (y : ℕ) = 1) ∨ ((x : ℕ) + 2 = m ∧ (y : ℕ) = 0) ∨
        ((y : ℕ) + 2 = x ∨ ((y : ℕ) + 1 = m ∧ (x : ℕ) = 1) ∨
          ((y : ℕ) + 2 = m ∧ (x : ℕ) = 0))) := by
  simp only [stepTwoGraph_adj, stepTwoArc_fin_iff, ne_eq, Fin.val_inj, or_assoc]

private theorem reachable_even {m : ℕ} (hm : 0 < m) :
    ∀ j (h : 2 * j < m), (stepTwoGraph (Fin m)).Reachable ⟨0, hm⟩ ⟨2 * j, h⟩
  | 0, _ => .rfl
  | j + 1, h => (reachable_even hm j (by omega)).trans (SimpleGraph.Adj.reachable
      ((stepTwoGraph_adj_fin_iff _ _).2 ⟨by simp only; omega, .inl (by simp only; omega)⟩))

private theorem reachable_odd {m : ℕ} (hm : 1 < m) :
    ∀ j (h : 2 * j + 1 < m), (stepTwoGraph (Fin m)).Reachable ⟨1, hm⟩ ⟨2 * j + 1, h⟩
  | 0, _ => .rfl
  | j + 1, h => (reachable_odd hm j (by omega)).trans (SimpleGraph.Adj.reachable
      ((stepTwoGraph_adj_fin_iff _ _).2 ⟨by simp only; omega, .inl (by simp only; omega)⟩))

private theorem stepTwoGraph_fin_connected_of_odd {m : ℕ} (hm : Odd m) :
    (stepTwoGraph (Fin m)).Connected := by
  obtain ⟨t, rfl⟩ := hm
  have h0 : 0 < 2 * t + 1 := by omega
  have : Nonempty (Fin (2 * t + 1)) := ⟨⟨0, h0⟩⟩
  refine SimpleGraph.Connected.mk fun x y => ?_
  suffices h : ∀ x : Fin (2 * t + 1), (stepTwoGraph _).Reachable ⟨0, h0⟩ x from
    (h x).symm.trans (h y)
  intro x
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' x.1
  · have := reachable_even h0 j (by omega)
    convert this using 1
    exact Fin.ext hj
  · have ht : 0 < t := by have := x.2; omega
    have h1 : 1 < 2 * t + 1 := by omega
    have h10 : (stepTwoGraph (Fin (2 * t + 1))).Reachable ⟨0, h0⟩ ⟨1, h1⟩ :=
      (reachable_even h0 t (by omega)).trans (SimpleGraph.Adj.reachable
        ((stepTwoGraph_adj_fin_iff _ _).2 ⟨by simp only; omega, .inr (.inl ⟨rfl, rfl⟩)⟩))
    refine h10.trans ?_
    have := reachable_odd h1 j (by omega)
    convert this using 1
    exact Fin.ext hj

private theorem not_stepTwoGraph_fin_connected_of_even {m : ℕ} (hm : Even m) :
    ¬ (stepTwoGraph (Fin m)).Connected := by
  intro hc
  obtain ⟨t, rfl⟩ := hm
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact hc.nonempty.elim fun x => x.elim0
  have hpar : ∀ x y : Fin (t + t), (stepTwoGraph _).Adj x y → (x : ℕ) % 2 = (y : ℕ) % 2 := by
    intro x y h
    rw [stepTwoGraph_adj_fin_iff] at h
    omega
  have h01 := hc.preconnected ⟨0, by omega⟩ ⟨1, by omega⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at h01
  have key : ∀ y, Relation.ReflTransGen (stepTwoGraph (Fin (t + t))).Adj ⟨0, by omega⟩ y →
      (y : ℕ) % 2 = 0 := by
    intro y hy
    induction hy with
    | refl => rfl
    | tail _ hab ih => rw [← hpar _ _ hab, ih]
  exact absurd (key _ h01) (by simp)

/-- The step-two graph on `Fin m` is connected exactly when `m` is odd. -/
theorem stepTwoGraph_fin_connected_iff {m : ℕ} : (stepTwoGraph (Fin m)).Connected ↔ Odd m := by
  rcases Nat.even_or_odd m with h | h
  · exact ⟨fun hc => absurd hc (not_stepTwoGraph_fin_connected_of_even h),
      fun ho => absurd h (Nat.not_even_iff_odd.2 ho)⟩
  · exact ⟨fun _ => h, fun _ => stepTwoGraph_fin_connected_of_odd h⟩

/-! ### Transport along order isomorphisms -/

/-- Order isomorphisms preserve `StepTwoArc`. -/
theorem stepTwoArc_orderIso {N : Type*} [LinearOrder N] (e : M ≃o N) (x y : M) :
    StepTwoArc N (e x) (e y) ↔ StepTwoArc M x y := by
  simp only [stepTwoArc_iff, e.surjective.exists, e.surjective.forall, apply_covBy_apply_iff e,
    e.le_iff_le]

/-- An order isomorphism is an isomorphism of step-two graphs. -/
def stepTwoGraphIso {N : Type*} [LinearOrder N] (e : M ≃o N) :
    stepTwoGraph M ≃g stepTwoGraph N where
  toEquiv := e.toEquiv
  map_rel_iff' {x y} := by
    simp only [stepTwoGraph_adj, RelIso.coe_fn_toEquiv, stepTwoArc_orderIso, ne_eq,
      EmbeddingLike.apply_eq_iff_eq]

/-- The step-two graph of a finite linear order is connected exactly when the order has an odd
number of elements. -/
theorem stepTwoGraph_connected_iff_odd [Finite M] :
    (stepTwoGraph M).Connected ↔ Odd (Nat.card M) := by
  have := Fintype.ofFinite M
  rw [← (stepTwoGraphIso
      (Fintype.orderIsoFinOfCardEq M Nat.card_eq_fintype_card.symm)).connected_iff,
    stepTwoGraph_fin_connected_iff]

/-! ### The step-two graph as a defined graph -/

variable (M) in
/-- The step-two graph of a linear order is the graph defined by `stepTwoArcFormula`. -/
theorem stepTwoGraph_eq_definedGraph [Language.order.Structure M]
    [Language.order.OrderedStructure M] :
    stepTwoGraph M = definedGraph M (stepTwoArcFormula 0 1) := by
  ext x y
  simp only [stepTwoGraph_adj, definedGraph_adj, realize_stepTwoArcFormula, Matrix.cons_val_zero,
    Matrix.cons_val_one]

/-! ### Nondefinability of connectivity -/

/-- **Connectivity is not first-order definable** on finite graphs, even on graphs with at least
`t` vertices: no sentence of the language of graphs holds in exactly the connected ones among the
finite simple graphs with at least `t` vertices [Libkin, Corollary 3.19][Libkin2004]. -/
theorem not_exists_sentence_connected_of_le_card (t : ℕ) :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      t ≤ Nat.card V → ((letI := G.structure; V ⊨ φ) ↔ G.Connected) :=
  not_exists_sentence_of_odd (fun _ G => G.Connected) (stepTwoArcFormula 0 1) 0
    (fun M _ _ _ _ _ => by rw [← stepTwoGraph_eq_definedGraph, stepTwoGraph_connected_iff_odd])
    t

/-- **Connectivity is not first-order definable** on finite graphs: no sentence of the language of
graphs holds in exactly the connected finite simple graphs [Libkin, Corollary 3.19][Libkin2004]. -/
theorem not_exists_sentence_connected :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      (letI := G.structure; V ⊨ φ) ↔ G.Connected := fun ⟨φ, hφ⟩ =>
  not_exists_sentence_connected_of_le_card 0 ⟨φ, fun V _ G _ => hφ V G⟩

end Cslib.Logic.FO.Connectivity
