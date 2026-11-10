/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.Expander.NeighborDeletion
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.NormNum

/-!
# A regular deletion from the complete graph on four vertices

Deleting the two edges between vertices of equal parity leaves a four-cycle. The complete
graph has degree three and loss `1 / 3` through sets of size two; the transfer theorem gives
loss `1 / 2` for the degree-two cycle on the same range. The pair `{0, 2}` attains this bound,
so the client exercises genuine edge deletion and a nontrivial two-vertex expansion bound.
-/

namespace ComplexityTests.ExpanderNeighborDeletion

open Finset

private def fourCycle : SimpleGraph (Fin 4) where
  Adj v w := (v : ℕ) % 2 ≠ (w : ℕ) % 2
  symm.symm _ _ h := h.symm
  loopless.irrefl _ h := h rfl

private instance : DecidableRel fourCycle.Adj := fun v w ↦
  inferInstanceAs (Decidable ((v : ℕ) % 2 ≠ (w : ℕ) % 2))

private theorem complete_four_regular :
    (⊤ : SimpleGraph (Fin 4)).IsRegularOfDegree 3 := by
  change ∀ v : Fin 4, (⊤ : SimpleGraph (Fin 4)).degree v = 3
  decide +kernel

private theorem fourCycle_regular : fourCycle.IsRegularOfDegree 2 := by
  change ∀ v : Fin 4, fourCycle.degree v = 2
  decide +kernel

private theorem complete_four_neighbor_bound :
    ∀ S : Finset (Fin 4), S.card ≤ 2 →
      2 * S.card ≤ (S.biUnion (fun v ↦ (⊤ : SimpleGraph (Fin 4)).neighborFinset v)).card := by
  decide +kernel

private theorem complete_four_expansion (S : Finset (Fin 4)) (hS : S.card ≤ 2) :
    (1 - (1 / 3 : ℝ)) * 3 * S.card ≤
      ((S.biUnion (fun v ↦ (⊤ : SimpleGraph (Fin 4)).neighborFinset v)).card : ℝ) := by
  have h : (2 : ℝ) * S.card ≤
      ((S.biUnion (fun v ↦ (⊤ : SimpleGraph (Fin 4)).neighborFinset v)).card : ℝ) := by
    exact_mod_cast complete_four_neighbor_bound S hS
  norm_num at h ⊢
  exact h

/-- The transfer theorem applies to concrete graphs and keeps the two-vertex cutoff. -/
example (S : Finset (Fin 4)) (hS : S.card ≤ 2) :
    (1 - (1 / 2 : ℝ)) * 2 * S.card ≤
      ((S.biUnion (fun v ↦ fourCycle.neighborFinset v)).card : ℝ) := by
  have h := SimpleGraph.lossless_bound_of_le_of_isRegularOfDegree
    (G := (⊤ : SimpleGraph (Fin 4))) (H := fourCycle) (K := 2) (ε := (1 / 3 : ℝ))
    le_top complete_four_regular fourCycle_regular (by decide) complete_four_expansion S hS
  norm_num at h ⊢
  exact h

-- The subgraph is strict: the deleted edge joins the same-parity vertices 0 and 2.
example : (⊤ : SimpleGraph (Fin 4)).Adj 0 2 ∧ ¬fourCycle.Adj 0 2 := by decide +kernel

-- This pair reaches the two-vertex cutoff and has exactly the guaranteed two neighbors.
example : (({0, 2} : Finset (Fin 4)).biUnion (fun v ↦ fourCycle.neighborFinset v)).card = 2 := by
  decide +kernel

end ComplexityTests.ExpanderNeighborDeletion
