/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Complexity.Classes.Oracle.ThresholdSearch

/-!
# Checked examples for the `maxClauseScore` / `MaxSAT.optimum` bridge

`MaxSAT.maxClauseScore_eq_optimum` identifies the `P^NP` binary-search optimum with the
fine-grained declared-variable optimum on a well-formed instance. The second example shows that
the declared-range hypothesis is needed: with no declared variables, the clause `x₀` scores `0`
under `MaxSAT.score` but `1` under `maxClauseScore`.
-/

public section

namespace CslibFrontierTests.MaxSATThresholdBridge

open Cslib Cslib.Complexity Cslib.Logic.PL

/-- The contradictory pair of unit clauses `x₀` and `¬x₀`. -/
def contra : CNF ℕ := [[(0, true)], [(0, false)]]

/-- Every variable of `contra` is declared when `n = 1`. -/
example : MaxSAT.maxClauseScore contra = MaxSAT.optimum (1, contra) :=
  MaxSAT.maxClauseScore_eq_optimum (by decide)

/-- Both optima of `contra` are `1`. -/
example : MaxSAT.maxClauseScore contra = 1 ∧ MaxSAT.optimum (1, contra) = 1 := by
  rw [← MaxSAT.maxClauseScore_eq_optimum (by decide), and_self]
  obtain ⟨-, ⟨σ, hσ⟩, hub⟩ := MaxSAT.maxClauseScore_spec contra
  have h1 : 1 ≤ contra.countP (Clause.eval fun _ => true) := by decide
  have h2 : contra.countP (Clause.eval σ) ≤ 1 := by
    cases h : σ 0 <;> simp [contra, Clause.eval, Literal.eval, h]
  have := hub fun _ => true
  omega

/-- Without declared variables, the undeclared variable reads `false`, so the optimum drops. -/
example : MaxSAT.optimum (0, [[(0, true)]]) < MaxSAT.maxClauseScore [[(0, true)]] := by
  have h0 : MaxSAT.optimum (0, [[(0, true)]]) = 0 := by decide
  have h1 := (MaxSAT.maxClauseScore_spec [[(0, true)]]).2.2 fun _ => true
  simp [Clause.eval, Literal.eval] at h1
  omega

end CslibFrontierTests.MaxSATThresholdBridge
