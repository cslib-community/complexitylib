/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Lean.LubyMIS
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Tests for Luby's randomized maximal independent set algorithm

Concrete runs of `Complexity.Algorithms.Lean.LubyMIS`:

* phases of the path `0 - 1 - 2` under the identity ranking: vertex `0` joins and `1` drops, then
  `2` joins and nothing is live, so the chosen set `{0, 2}` is maximal while the intermediate
  `{0}` is not;
* on the triangle, every ranking finishes in one phase with exactly one chosen vertex;
* on the path `0 - 1 - 2 - 3`, the identity ranking keeps one of the three edges live, so a phase
  need not remove every edge;
* the support of the algorithm is nonempty and its outputs are maximal (nonvacuity of the Las
  Vegas statement), and an instance of the high-probability bound.
-/

namespace ComplexityTests.Algorithms.Lean.LubyMIS

open Cslib Cslib.Algorithms.Lean.LubyMIS SimpleGraph
open scoped ENNReal

/-- The identity ranking of `Fin n`. -/
def idRanking (n : ℕ) : Ranking (Fin n) := finCongr (Fintype.card_fin n).symm

/-! ### The path `0 - 1 - 2` -/

/-- Under the identity ranking, vertex `0` joins first. -/
example : (step (pathGraph 3) init (idRanking 3)).chosen = {0} := by decide

/-- Its neighbour `1` drops out and `2` stays live. -/
example : (step (pathGraph 3) init (idRanking 3)).live = {2} := by decide

/-- In the second phase `2` joins. -/
example :
    (step (pathGraph 3) (step (pathGraph 3) init (idRanking 3)) (idRanking 3)).chosen = {0, 2} := by
  decide

/-- After the second phase nothing is live. -/
example :
    (step (pathGraph 3) (step (pathGraph 3) init (idRanking 3)) (idRanking 3)).live = ∅ := by
  decide

/-- The final chosen set `{0, 2}` is a maximal independent set. -/
example : Maximal (pathGraph 3).IsIndepSet (({0, 2} : Finset (Fin 3)) : Set (Fin 3)) := by
  have h := ((invariant_init (pathGraph 3)).step _ (idRanking 3)).step _ (idRanking 3)
  have hlive :
      (step (pathGraph 3) (step (pathGraph 3) init (idRanking 3)) (idRanking 3)).live = ∅ := by
    decide
  have hchosen :
      (step (pathGraph 3) (step (pathGraph 3) init (idRanking 3)) (idRanking 3)).chosen =
        {0, 2} := by
    decide
  rw [← hchosen]
  exact h.maximal_iff.2 hlive

/-- The intermediate chosen set `{0}` is independent but not maximal: `2` is still live. -/
example : ¬ Maximal (pathGraph 3).IsIndepSet (({0} : Finset (Fin 3)) : Set (Fin 3)) := by
  have h := (invariant_init (pathGraph 3)).step _ (idRanking 3)
  have hchosen : (step (pathGraph 3) init (idRanking 3)).chosen = {0} := by decide
  have hlive : (step (pathGraph 3) init (idRanking 3)).live = {2} := by decide
  rw [← hchosen, h.maximal_iff, hlive]
  decide

/-! ### The triangle and the path `0 - 1 - 2 - 3` -/

/-- On the triangle every ranking finishes in one phase, choosing exactly one vertex. -/
example : ∀ σ : Ranking (Fin 3), (step (⊤ : SimpleGraph (Fin 3)) init σ).live = ∅ ∧
    (step (⊤ : SimpleGraph (Fin 3)) init σ).chosen.card = 1 := by
  decide

/-- The triangle has three edges. -/
example : (⊤ : SimpleGraph (Fin 3)).edgeFinset.card = 3 := by decide

/-- On the path `0 - 1 - 2 - 3`, which has three edges, the identity ranking keeps the edge
`{2, 3}` live: a phase need not finish. -/
example : liveEdges (pathGraph 4) init = 3 ∧
    liveEdges (pathGraph 4) (step (pathGraph 4) init (idRanking 4)) = 1 := by
  decide

/-! ### The algorithm -/

/-- The Las Vegas statement is not vacuous: some output exists, and it is maximal. -/
example : ∃ S ∈ (ProbComp.eval (lubyMIS (pathGraph 3) (Fintype.card (Fin 3)))).support,
    Maximal (pathGraph 3).IsIndepSet (S : Set (Fin 3)) := by
  obtain ⟨S, hS⟩ := ProbComp.support_nonempty (lubyMIS (pathGraph 3) (Fintype.card (Fin 3)))
  rw [← ProbComp.support_eval] at hS
  exact ⟨S, hS, maximal_of_mem_support_lubyMIS _ hS⟩

/-- On the triangle (`|E| = 3 ≤ 2 ^ 2`), four phases succeed with probability at least `1/2`. -/
example : 1 - (2 ^ 1 : ℝ≥0∞)⁻¹ ≤
    (ProbComp.eval (lubyMIS (⊤ : SimpleGraph (Fin 3)) (2 + 1 + 1))).toOuterMeasure
      {S | Maximal (⊤ : SimpleGraph (Fin 3)).IsIndepSet (S : Set (Fin 3))} :=
  one_sub_le_toOuterMeasure_maximal_lubyMIS (⊤ : SimpleGraph (Fin 3)) (m := 2) (by decide) 1

end ComplexityTests.Algorithms.Lean.LubyMIS
