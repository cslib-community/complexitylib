/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Complexity.Classes.Oracle.SelfReduction

/-!
# Regression tests for the self-reduction of `SAT` relative to an oracle

The step iterates to the self-reduction on a concrete formula, and the search for `SAT` with an
oracle for `SAT` finds a satisfying assignment of a satisfiable formula.
-/

@[expose] public section

namespace ComplexityTests.OracleSelfReduction

open Cslib Cslib.Complexity Cslib.Complexity.SAT Cslib.Logic.PL

/-- A formula with a repeated variable: `x₀ ∧ (¬x₁ ∨ x₀)`. -/
def φ : CNF ℕ := [[(0, true)], [(1, false), (0, true)]]

/-- Its literal occurrences, in order. -/
example : φ.vars = [0, 1, 0] := rfl

/-- With the decision procedure that always answers yes, every occurrence is fixed to true, and
iterating the step gives the same literals. -/
example : (searchStep (fun _ => true) φ)^[φ.vars.length] [] = [(0, true), (1, true), (0, true)] :=
  rfl

example : selfReduce (fun _ => true) φ = (searchStep (fun _ => true) φ)^[3] [] :=
  selfReduce_eq_iterate _ φ

/-- The step asks about `φ` with the fixed literals as units and the next occurrence set true. -/
example : searchQuery φ [(0, true)] = φ ++ [[(0, true)]] ++ [[(1, true)]] := rfl

open Classical in
/-- `φ` is satisfiable, so the oracle search returns a certificate that `SAT.verifier` accepts. -/
example : verifier (φ, search (fun ψ => decide (encCNF ψ ∈ encCNF '' SAT)) φ) = true := by
  refine (verifier_search_image φ).mpr ⟨fun _ => true, ?_⟩
  decide

/-- The search is polynomial time relative to any oracle language. -/
example (A : Set (List Bool)) :
    ∃ g : CNF ℕ → List Bool, ComputableInPolyTimeWithOracle A g encCNF Turing.MultiTapeTM.encBits :=
  ⟨_, computableInPolyTimeWithOracle_search A⟩

end ComplexityTests.OracleSelfReduction
