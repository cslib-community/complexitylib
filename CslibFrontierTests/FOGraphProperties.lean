/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.GraphProperties

/-! # Bipartiteness and acyclicity are not first-order definable: checked instances

The cycle graph on `Fin 4` is bipartite and on `Fin 5` it is not; on `Fin m` it is Mathlib's
`cycleGraph m`. The closed step-two graph is acyclic on `Fin 6` but not on `Fin 5`, and it is
acyclic on `Fin 3` although `3` is odd, which is why the parity statement needs at least `4`
elements. A client derives that non-bipartiteness (the existence of an odd cycle) is not
first-order definable either. -/

@[expose] public section

namespace Cslib.Tests.FOGraphProperties

open FirstOrder Language Structure
open Cslib.Logic.FO Cslib.Logic.FO.DefinedGraph Cslib.Logic.FO.GraphProperties

instance (m : ℕ) : Language.order.Structure (Fin m) := orderStructure _

instance (m : ℕ) : Language.order.OrderedStructure (Fin m) := ⟨fun _ => Iff.rfl⟩

/-- The cycle `0 - 1 - 2 - 3 - 0` is bipartite. -/
example : (definedGraph (Fin 4) cycleArcFormula).IsBipartite :=
  (definedGraph_cycleArcFormula_isBipartite_fin (by decide)).2 (by decide)

/-- The cycle `0 - 1 - 2 - 3 - 4 - 0` is not bipartite. -/
example : ¬ (definedGraph (Fin 5) cycleArcFormula).IsBipartite :=
  fun h => absurd ((definedGraph_cycleArcFormula_isBipartite_fin (by decide)).1 h) (by decide)

/-- On `Fin 5`, `cycleArcFormula` defines Mathlib's cycle graph. -/
example : definedGraph (Fin 5) cycleArcFormula = SimpleGraph.cycleGraph 5 :=
  definedGraph_cycleArcFormula_fin

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

/-- A client of the odd-size parity transfer: the graph defined by the arcs of the cycle on a linear
order with at least two elements has an odd cycle exactly when the order has odd size, so
non-bipartiteness is not first-order definable on graphs with at least `t` vertices. -/
theorem not_exists_sentence_not_isBipartite_of_le_card (t : ℕ) :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type) [Finite V] (G : SimpleGraph V),
      t ≤ Nat.card V → ((letI := G.structure; V ⊨ φ) ↔ ¬ G.IsBipartite) :=
  not_exists_sentence_of_odd (fun _ G => ¬ G.IsBipartite) cycleArcFormula 2
    (fun M _ _ _ _ hM => by
      let := orderStructure (Fin (Nat.card M))
      have : Language.order.OrderedStructure (Fin (Nat.card M)) := ⟨fun _ => Iff.rfl⟩
      let e := definedGraphIsoFin cycleArcFormula M
      rw [← Nat.not_even_iff_odd, ← definedGraph_cycleArcFormula_isBipartite_fin hM]
      exact not_congr ⟨fun h => h.of_hom e.symm.toEmbedding.toHom,
        fun h => h.of_hom e.toEmbedding.toHom⟩)
    t

/-- A client: non-bipartiteness of finite graphs is not first-order definable either. -/
theorem not_exists_sentence_not_isBipartite :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type) [Finite V] (G : SimpleGraph V),
      (letI := G.structure; V ⊨ φ) ↔ ¬ G.IsBipartite := fun ⟨φ, hφ⟩ =>
  not_exists_sentence_isBipartite.{0} ⟨∼φ, fun V _ G => by
    let := G.structure
    exact (Sentence.realize_not _).trans ((not_congr (hφ V G)).trans not_not)⟩

end Cslib.Tests.FOGraphProperties
