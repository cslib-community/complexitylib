/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.EhrenfeuchtFraisse.GraphProperties

/-! # Bipartiteness and acyclicity are not first-order definable: checked instances

The cycle graph on `Fin 4` is bipartite and on `Fin 5` it is not. The closed step-two graph is
acyclic on `Fin 6` but not on `Fin 5`, and it is acyclic on `Fin 3` although `3` is odd, which is
why the parity statement needs at least `4` elements. A client derives that non-bipartiteness (the
existence of an odd cycle) is not first-order definable either. -/

@[expose] public section

namespace Cslib.Tests.FOGraphProperties

open FirstOrder Language Structure
open Cslib.Logic.FO Cslib.Logic.FO.GraphProperties

instance (m : ℕ) : Language.order.Structure (Fin m) := orderStructure _

instance (m : ℕ) : Language.order.OrderedStructure (Fin m) := ⟨fun _ => Iff.rfl⟩

/-- The cycle `0 - 1 - 2 - 3 - 0` is bipartite. -/
example : (definedGraph (Fin 4) cycleArcFormula).IsBipartite :=
  (definedGraph_cycleArcFormula_isBipartite_fin (by decide)).2 (by decide)

/-- The cycle `0 - 1 - 2 - 3 - 4 - 0` is not bipartite. -/
example : ¬ (definedGraph (Fin 5) cycleArcFormula).IsBipartite :=
  fun h => absurd ((definedGraph_cycleArcFormula_isBipartite_fin (by decide)).1 h) (by decide)

/-- The wrap-around edge of the cycle on `Fin 5`. -/
example : (definedGraph (Fin 5) cycleArcFormula).Adj 4 0 :=
  (definedGraph_cycleArcFormula_adj_fin _ _).2 (by decide)

/-- On `Fin 6` the closed step-two graph is the path `4 - 2 - 0 - 5 - 3 - 1`. -/
example : (definedGraph (Fin 6) stepTwoTopBotArcFormula).IsAcyclic :=
  (definedGraph_stepTwoTopBotArcFormula_isAcyclic_fin (by decide)).2 (by decide)

/-- On `Fin 5` the closed step-two graph contains the cycle `0 - 2 - 4 - 0`. -/
example : ¬ (definedGraph (Fin 5) stepTwoTopBotArcFormula).IsAcyclic :=
  fun h => absurd ((definedGraph_stepTwoTopBotArcFormula_isAcyclic_fin (by decide)).1 h)
    (by decide)

/-- On `Fin 3` the closed step-two graph has the single edge `0 - 2`, so it is acyclic although `3`
is odd: the parity characterization needs at least `4` elements. -/
example : (definedGraph (Fin 3) stepTwoTopBotArcFormula).IsAcyclic := by
  have hinj : Function.Injective (![0, 2, 1] : Fin 3 → Fin 3) := by decide
  refine (SimpleGraph.isAcyclic_pathGraph 3).comap
    (G := definedGraph (Fin 3) stepTwoTopBotArcFormula) ⟨![0, 2, 1], fun {x y} h => ?_⟩ hinj
  rw [definedGraph_stepTwoTopBotArcFormula_adj_fin] at h
  rw [SimpleGraph.pathGraph_adj]
  revert x y
  decide

/-- A client: non-bipartiteness of finite graphs is not first-order definable either. -/
theorem not_exists_sentence_not_isBipartite :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type) [Finite V] (G : SimpleGraph V),
      (letI := G.structure; V ⊨ φ) ↔ ¬ G.IsBipartite := fun ⟨φ, hφ⟩ =>
  not_exists_sentence_isBipartite.{0} ⟨∼φ, fun V _ G => by
    let := G.structure
    exact (Sentence.realize_not _).trans ((not_congr (hφ V G)).trans not_not)⟩

end Cslib.Tests.FOGraphProperties
