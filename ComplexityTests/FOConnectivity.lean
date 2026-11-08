/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.EhrenfeuchtFraisse.Connectivity

/-! # Connectivity is not first-order definable: checked instances

The step-two graph on `Fin 5` is connected and on `Fin 4` it is not. Two concrete adjacencies, a
step-two graph on a linear order other than `Fin m`, and the pullback of a concrete graph sentence
along the interpretation defined by `stepTwoArcFormula` are checked. A client derives that
disconnectedness is not first-order definable either. -/

@[expose] public section

namespace Cslib.Tests.FOConnectivity

open FirstOrder Language Structure
open Cslib.Logic.FO Cslib.Logic.FO.DefinedGraph Cslib.Logic.FO.Connectivity

/-- On `Fin 5` the step-two graph is the cycle `0 - 2 - 4 - 1 - 3 - 0`, which is connected. -/
example : (stepTwoGraph (Fin 5)).Connected :=
  stepTwoGraph_fin_connected_iff.2 (by decide)

/-- On `Fin 4` the step-two graph has the two edges `0 - 2` and `1 - 3`, so it is not connected. -/
example : ¬ (stepTwoGraph (Fin 4)).Connected :=
  fun h => absurd (stepTwoGraph_fin_connected_iff.1 h) (by decide)

/-- The wrap-around edge from the greatest element to the second least element. -/
example : (stepTwoGraph (Fin 5)).Adj 4 1 :=
  (stepTwoGraph_adj_fin_iff _ _).2 (by decide)

/-- Consecutive elements are not adjacent. -/
example : ¬ (stepTwoGraph (Fin 5)).Adj 0 1 :=
  fun h => absurd ((stepTwoGraph_adj_fin_iff _ _).1 h) (by decide)

/-- The step-two graph of `Bool`, a linear order with two elements, is not connected. -/
example : ¬ (stepTwoGraph Bool).Connected := by
  rw [stepTwoGraph_connected_iff_odd, Nat.card_eq_fintype_card, Fintype.card_bool]
  decide

/-- A client: disconnectedness of finite graphs is not first-order definable either. -/
theorem not_exists_sentence_not_connected :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type) [Finite V] (G : SimpleGraph V),
      (letI := G.structure; V ⊨ φ) ↔ ¬ G.Connected := fun ⟨φ, hφ⟩ =>
  not_exists_sentence_connected.{0} ⟨∼φ, fun V _ G => by
    let := G.structure
    exact (Sentence.realize_not _).trans ((not_congr (hφ V G)).trans not_not)⟩

instance (m : ℕ) : Language.order.Structure (Fin m) := orderStructure _

instance (m : ℕ) : Language.order.OrderedStructure (Fin m) := ⟨fun _ => Iff.rfl⟩

/-- "Every vertex has a neighbour", a sentence of the language of graphs. -/
noncomputable def noIsolated : Language.graph.Sentence :=
  ∀' ∃' (adj.boundedFormula₂ &0 &1)

/-- The pullback of `noIsolated` along the interpretation defined by `stepTwoArcFormula` holds in
the order `Fin 5`: every element `x` is adjacent to `x + 2` in the step-two graph. -/
example : Fin 5 ⊨ (graphInterp (stepTwoArcFormula 0 1)).onSentence noIsolated := by
  rw [realize_onSentence_graphInterp, ← stepTwoGraph_eq_definedGraph]
  simp only [noIsolated, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_rel₂]
  intro x
  refine ⟨x + 2, ?_⟩
  change (stepTwoGraph (Fin 5)).Adj x (x + 2)
  rw [stepTwoGraph_adj_fin_iff]
  revert x
  decide

end Cslib.Tests.FOConnectivity
