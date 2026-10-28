/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.GeometryProfilesData
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.Geometry
import Mathlib.Tactic.FinCases

/-!
# Certificates for the actual positive exact-one replacement profiles

Each finite profile is checked against its full positive exact-one formula, rather than an
unrelated graph. Every source placeholder has just one internal incidence, so it can be removed
when that incidence is joined to the source drawing. Full continuous certificates for the actual
extended incidence routes are in `GeometryProfilesPrefix`.

## Main results

The continuous source-boundary certificates are in `GeometryProfilesPrefix`.
* `profileGeometry_signature`: incidence routes match the actual composed positive compiler.
* `profileGeometry_terminals`: exposed variables are exactly the source placeholders.

## References

The logical gadgets are from [HuntMaratheRadhakrishnanStearns1998, Theorem 3.8].
The composed geometric certificates are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Cslib.Logic.PL Orthogonal

/-- The exact clause-variable incidence sequence of the positive compiled formula. -/
def profileSignature (p : ClauseProfile) : List (ℕ × ℕ) :=
  (profileFormula p).zipIdx.flatMap fun (c, i) =>
    c.map fun l => (i, (profileVariables p).idxOf l.1)

/-- Geometry and logical variable lists have exactly corresponding positions. -/
theorem profileGeometry_variable_length (p : ClauseProfile) :
    (profileGeometry p).variablePositions.length = (profileVariables p).length := by
  fin_cases p <;> decide +kernel

/-- There is one clause position for each actual emitted positive clause. -/
theorem profileGeometry_clause_length (p : ClauseProfile) :
    (profileGeometry p).clausePositions.length = (profileFormula p).length := by
  fin_cases p <;> decide +kernel

/-- Every incidence appears once, in actual output-clause and literal-position order. -/
theorem profileGeometry_signature (p : ClauseProfile) :
    ((profileGeometry p).incidenceRoutes.map fun e => (e.1, e.2.1)) = profileSignature p := by
  fin_cases p <;> decide +kernel

/-- Exposed variables are precisely the source slots, in source literal order. -/
theorem profileGeometry_terminals (p : ClauseProfile) :
    ((profileGeometry p).terminalVariables.map fun v =>
      (profileVariables p).getD v (.inl (.inl 0))) =
        (List.range (profileSource p).length).map (fun v => Sum.inl (Sum.inl v)) := by
  fin_cases p <;> decide +kernel

/-- Each source placeholder has a single internal incidence, ready for exterior splicing. -/
theorem profileGeometry_terminal_degree (p : ClauseProfile) :
    ∀ v ∈ (profileGeometry p).terminalVariables,
      ((profileGeometry p).incidenceRoutes.map fun e => e.2.1).count v = 1 := by
  fin_cases p <;> decide +kernel

/-- The actual composed gadgets have at most twenty-two clauses and sixty-six incidences. -/
theorem profileGeometry_costs (p : ClauseProfile) :
    (profileGeometry p).clausePositions.length ≤ 22 ∧
      (profileGeometry p).incidenceRoutes.length ≤ 66 ∧
      (profileGeometry p).size = 180000 := by
  fin_cases p <;> decide +kernel

end Cslib.Complexity.SAT.ExactOne
