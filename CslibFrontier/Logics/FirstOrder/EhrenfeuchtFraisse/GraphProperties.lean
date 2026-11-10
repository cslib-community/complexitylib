/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.DefinedGraph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Bipartiteness and acyclicity are not first-order definable

A finite simple graph `G` on `V` is a structure in Mathlib's language of graphs
`FirstOrder.Language.graph` through `SimpleGraph.structure`. No first-order sentence of this
language holds in exactly the bipartite (2-colorable) finite graphs
(`not_exists_sentence_isBipartite`), nor in exactly the acyclic ones
(`not_exists_sentence_isAcyclic`), even when only graphs with at least `t` vertices are considered.

Both proofs adapt the reduction from EVEN on finite linear orders that [Libkin, Corollary
3.19][Libkin2004] uses for connectivity; in Libkin's book the two statements are exercises
(Exercise 3.4 for acyclicity, Exercise 3.5(3) for 2-colorability) posed for Ehrenfeucht–Fraïssé
games. The order-definable graphs below are this module's adaptation of that reduction. Each is the
graph defined by a formula of the language of orders (`DefinedGraph.definedGraph`), and its property
holds exactly on the orders of even size, so the parity transfer
`DefinedGraph.not_exists_sentence_of_even` of
`CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.DefinedGraph` applies.

The two order-definable graphs, on a linear order `0 < 1 < ⋯ < m - 1`:
* `cycleArcFormula`: each element is joined to its successor and `m - 1` to `0`. On `Fin m` this is
  Mathlib's `SimpleGraph.cycleGraph m` (`definedGraph_cycleArcFormula_fin`), which for `m ≥ 2` is
  bipartite iff `m` is even (`definedGraph_cycleArcFormula_isBipartite_fin`).
* `stepTwoTopBotArcFormula`: each element is joined to the element two steps above it and `m - 1`
  to `0`. For even `m` this is a single path `m - 2, …, 2, 0, m - 1, m - 3, …, 1`; for odd `m ≥ 5`
  the even positions `0, 2, …, m - 1` form a cycle. For `m ≥ 4` it is acyclic iff `m` is even
  (`definedGraph_stepTwoTopBotArcFormula_isAcyclic_fin`). The bound `4` is needed: for `m = 3` the
  graph has the single edge `0 — 2` and is acyclic.

The graph properties are those of Mathlib, `SimpleGraph.IsBipartite` (`Colorable 2`) and
`SimpleGraph.IsAcyclic`, and the sentences range over the pure graph vocabulary, with no built-in
order or arithmetic.

## Main definitions

* `Cslib.Logic.FO.GraphProperties.cycleArcFormula`: the cycle on a linear order.
* `Cslib.Logic.FO.GraphProperties.stepTwoTopBotArcFormula`: the step-two graph of a linear order
  closed by the edge from the greatest to the least element.

## Main results

* `Cslib.Logic.FO.GraphProperties.not_exists_sentence_isBipartite`: bipartiteness is not
  first-order definable on finite graphs.
* `Cslib.Logic.FO.GraphProperties.not_exists_sentence_isAcyclic`: acyclicity is not first-order
  definable on finite graphs.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Corollary 3.19 (connectivity, by
  reduction from EVEN on linear orders; the method adapted here), Exercise 3.4 (acyclicity) and
  Exercise 3.5(3) (2-colorability).
-/

public section

open FirstOrder Language Structure

namespace Cslib.Logic.FO.GraphProperties

open DefinedGraph

universe u

/-! ### Bipartiteness -/

/-- The arcs of the cycle graph of a linear order: from each element to its successor, and from
the greatest element to the least one. -/
noncomputable def cycleArcFormula : Language.order.Formula (Fin 2) :=
  covByFormula 0 1 ⊔ (isTopFormula 0 ⊓ isBotFormula 1)

section Fin

variable {m : ℕ} [Language.order.Structure (Fin m)] [Language.order.OrderedStructure (Fin m)]

/-- Adjacency in the cycle graph on `Fin m`, in terms of values. -/
theorem definedGraph_cycleArcFormula_adj_fin (x y : Fin m) :
    (definedGraph (Fin m) cycleArcFormula).Adj x y ↔ (x : ℕ) ≠ y ∧
      ((x : ℕ) + 1 = y ∨ ((x : ℕ) + 1 = m ∧ (y : ℕ) = 0) ∨
        (y : ℕ) + 1 = x ∨ ((y : ℕ) + 1 = m ∧ (x : ℕ) = 0)) := by
  simp only [definedGraph_adj, cycleArcFormula, Formula.realize_sup, Formula.realize_inf,
    realize_covByFormula_fin, realize_isTopFormula_fin, realize_isBotFormula_fin,
    Matrix.cons_val_zero, Matrix.cons_val_one, ne_eq, Fin.val_inj, or_assoc]

/-- On `Fin m`, `cycleArcFormula` defines Mathlib's cycle graph `SimpleGraph.cycleGraph m`. -/
theorem definedGraph_cycleArcFormula_fin :
    definedGraph (Fin m) cycleArcFormula = SimpleGraph.cycleGraph m := by
  ext x y
  rw [definedGraph_cycleArcFormula_adj_fin, SimpleGraph.cycleGraph_adj']
  have hx := x.2
  have hy := y.2
  rcases lt_trichotomy x y with h | rfl | h
  · rw [Fin.coe_sub_iff_lt.2 h, Fin.coe_sub_iff_le.2 h.le]
    rw [Fin.lt_def] at h
    omega
  · rw [Fin.coe_sub_iff_le.2 le_rfl]
    omega
  · rw [Fin.coe_sub_iff_le.2 h.le, Fin.coe_sub_iff_lt.2 h]
    rw [Fin.lt_def] at h
    omega

/-- The cycle graph on `Fin m`, for `m ≥ 2`, is bipartite iff `m` is even. -/
theorem definedGraph_cycleArcFormula_isBipartite_fin (hm : 2 ≤ m) :
    (definedGraph (Fin m) cycleArcFormula).IsBipartite ↔ Even m := by
  rw [definedGraph_cycleArcFormula_fin]
  refine ⟨fun h => ?_, SimpleGraph.IsBipartite.cycleGraph_of_even⟩
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have h2 := h.chromaticNumber_le
  rw [SimpleGraph.chromaticNumber_cycleGraph_of_odd m hm hodd] at h2
  exact absurd h2 (by decide)

end Fin

/-- **Bipartiteness (2-colorability) is not first-order definable** on finite graphs, even on graphs
with at least `t` vertices [Libkin, Exercise 3.5(3)][Libkin2004]. -/
theorem not_exists_sentence_isBipartite_of_le_card (t : ℕ) :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      t ≤ Nat.card V → ((letI := G.structure; V ⊨ φ) ↔ G.IsBipartite) :=
  not_exists_sentence_of_even (fun _ G => G.IsBipartite) cycleArcFormula 2
    (fun M _ _ _ _ hM => by
      let := orderStructure (Fin (Nat.card M))
      have : Language.order.OrderedStructure (Fin (Nat.card M)) := ⟨fun _ => Iff.rfl⟩
      let e := definedGraphIsoFin cycleArcFormula M
      change (definedGraph M cycleArcFormula).IsBipartite ↔ _
      rw [← definedGraph_cycleArcFormula_isBipartite_fin hM]
      exact ⟨fun h => h.of_hom e.symm.toEmbedding.toHom, fun h => h.of_hom e.toEmbedding.toHom⟩)
    t

/-- **Bipartiteness (2-colorability) is not first-order definable** on finite graphs. -/
theorem not_exists_sentence_isBipartite :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      (letI := G.structure; V ⊨ φ) ↔ G.IsBipartite := fun ⟨φ, hφ⟩ =>
  not_exists_sentence_isBipartite_of_le_card 0 ⟨φ, fun V _ G _ => hφ V G⟩

/-! ### Acyclicity -/

/-- The arcs of the step-two graph of a linear order closed by one edge: from each element to the
element two steps above it, and from the greatest element to the least one. -/
noncomputable def stepTwoTopBotArcFormula : Language.order.Formula (Fin 2) :=
  twoAboveFormula 0 1 ⊔ (isTopFormula 0 ⊓ isBotFormula 1)

section Fin

variable {m : ℕ} [Language.order.Structure (Fin m)] [Language.order.OrderedStructure (Fin m)]

/-- Adjacency in the closed step-two graph on `Fin m`, in terms of values. -/
theorem definedGraph_stepTwoTopBotArcFormula_adj_fin (x y : Fin m) :
    (definedGraph (Fin m) stepTwoTopBotArcFormula).Adj x y ↔ (x : ℕ) ≠ y ∧
      ((x : ℕ) + 2 = y ∨ ((x : ℕ) + 1 = m ∧ (y : ℕ) = 0) ∨
        (y : ℕ) + 2 = x ∨ ((y : ℕ) + 1 = m ∧ (x : ℕ) = 0)) := by
  simp only [definedGraph_adj, stepTwoTopBotArcFormula, Formula.realize_sup, Formula.realize_inf,
    realize_twoAboveFormula_fin, realize_isTopFormula_fin, realize_isBotFormula_fin,
    Matrix.cons_val_zero, Matrix.cons_val_one, ne_eq, Fin.val_inj, or_assoc]

private theorem isAcyclic_stepTwoTopBot_fin_of_even (hm : Even m) :
    (definedGraph (Fin m) stepTwoTopBotArcFormula).IsAcyclic := by
  obtain ⟨k, rfl⟩ := hm
  let f : Fin (k + k) → Fin (k + k) := fun x =>
    ⟨if x.1 % 2 = 0 then k - 1 - x.1 / 2 else 2 * k - 1 - x.1 / 2, by
      have := x.2; split <;> omega⟩
  have hf : Function.Injective f := by
    intro x y h
    have h' := congrArg Fin.val h
    simp only [f] at h'
    ext
    have := x.2
    have := y.2
    split at h' <;> split at h' <;> omega
  let F : definedGraph (Fin (k + k)) stepTwoTopBotArcFormula →g SimpleGraph.pathGraph (k + k) :=
    ⟨f, fun {x y} h => by
      rw [definedGraph_stepTwoTopBotArcFormula_adj_fin] at h
      rw [SimpleGraph.pathGraph_adj]
      simp only [f]
      have := x.2
      have := y.2
      split <;> split <;> omega⟩
  exact (SimpleGraph.isAcyclic_pathGraph _).comap F hf

private theorem not_isAcyclic_stepTwoTopBot_fin_of_odd (hm : Odd m) (h5 : 5 ≤ m) :
    ¬ (definedGraph (Fin m) stepTwoTopBotArcFormula).IsAcyclic := by
  obtain ⟨k, rfl⟩ := hm
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro h
  have h02 : (definedGraph (Fin (2 * k + 1)) stepTwoTopBotArcFormula).Adj ⟨0, by omega⟩
      ⟨2, by omega⟩ :=
    (definedGraph_stepTwoTopBotArcFormula_adj_fin _ _).2 ⟨by simp only; omega, .inl rfl⟩
  apply SimpleGraph.isBridge_iff.1 (h h02)
  have reach : ∀ j (hj : 1 ≤ j) (hjk : j ≤ k),
      ((definedGraph (Fin (2 * k + 1)) stepTwoTopBotArcFormula).deleteEdges
        {s(⟨0, by omega⟩, ⟨2, by omega⟩)}).Reachable ⟨2, by omega⟩ ⟨2 * j, by omega⟩ := by
    intro j hj hjk
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact .rfl
      · refine (ih hj0 (by omega)).trans (SimpleGraph.Adj.reachable ?_)
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨(definedGraph_stepTwoTopBotArcFormula_adj_fin _ _).2
          ⟨by simp only; omega, .inl (by simp only; omega)⟩, ?_⟩
        simp only [Set.mem_singleton_iff, Sym2.eq_iff, Fin.ext_iff]
        omega
  have r1 : ((definedGraph (Fin (2 * k + 1)) stepTwoTopBotArcFormula).deleteEdges
      {s(⟨0, by omega⟩, ⟨2, by omega⟩)}).Reachable ⟨0, by omega⟩ ⟨2 * k, by omega⟩ := by
    refine SimpleGraph.Adj.reachable ?_
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨(definedGraph_stepTwoTopBotArcFormula_adj_fin _ _).2
      ⟨by simp only; omega, .inr (.inr (.inr ⟨rfl, rfl⟩))⟩, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff, Fin.ext_iff]
    omega
  exact r1.trans (reach k (by omega) le_rfl).symm

/-- The step-two graph on `Fin m` closed by the edge `m - 1 — 0` is acyclic iff `m` is even, for
`m ≥ 4`. -/
theorem definedGraph_stepTwoTopBotArcFormula_isAcyclic_fin (hm : 4 ≤ m) :
    (definedGraph (Fin m) stepTwoTopBotArcFormula).IsAcyclic ↔ Even m := by
  refine ⟨fun h => ?_, isAcyclic_stepTwoTopBot_fin_of_even⟩
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  exact not_isAcyclic_stepTwoTopBot_fin_of_odd hodd (by obtain ⟨k, rfl⟩ := hodd; omega) h

end Fin

/-- **Acyclicity is not first-order definable** on finite graphs, even on graphs with at least `t`
vertices [Libkin, Exercise 3.4][Libkin2004]. -/
theorem not_exists_sentence_isAcyclic_of_le_card (t : ℕ) :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      t ≤ Nat.card V → ((letI := G.structure; V ⊨ φ) ↔ G.IsAcyclic) :=
  not_exists_sentence_of_even (fun _ G => G.IsAcyclic) stepTwoTopBotArcFormula 4
    (fun M _ _ _ _ hM => by
      let := orderStructure (Fin (Nat.card M))
      have : Language.order.OrderedStructure (Fin (Nat.card M)) := ⟨fun _ => Iff.rfl⟩
      change (definedGraph M stepTwoTopBotArcFormula).IsAcyclic ↔ _
      rw [(definedGraphIsoFin stepTwoTopBotArcFormula M).isAcyclic_iff,
        definedGraph_stepTwoTopBotArcFormula_isAcyclic_fin hM])
    t

/-- **Acyclicity is not first-order definable** on finite graphs. -/
theorem not_exists_sentence_isAcyclic :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      (letI := G.structure; V ⊨ φ) ↔ G.IsAcyclic := fun ⟨φ, hφ⟩ =>
  not_exists_sentence_isAcyclic_of_le_card 0 ⟨φ, fun V _ G _ => hφ V G⟩

end Cslib.Logic.FO.GraphProperties
