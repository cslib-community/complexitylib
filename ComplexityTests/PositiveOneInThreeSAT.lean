/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.OneInThreeSAT.Reduction

/-!
# Positive exact-one SAT regression examples

Tests distinguish exact-one from ordinary disjunction, check repeated occurrences and
nonvacuous positive degree-three examples, and apply the full parsimonious compiler to
short clauses, an empty clause, and an empty formula.
-/

public section

namespace Cslib.Tests.PositiveOneInThreeSAT

open Cslib.Logic.PL Cslib.Complexity

private def oneTriple : CNF ℕ := [[(0, true), (1, true), (2, true)]]

/-- The four triples on four variables have no exact-one assignment, although every variable
has degree three and every clause is positive and distinct. -/
private def fourTriples : CNF ℕ :=
  [[(0, true), (1, true), (2, true)], [(0, true), (1, true), (3, true)],
    [(0, true), (2, true), (3, true)], [(1, true), (2, true), (3, true)]]

private def binarySource : CNF ℕ := [[(0, true), (1, true)]]

/-- The empty positive instance has exactly one assignment on its empty support. -/
theorem empty_formula_count : CNF.oneModelCount ([] : CNF ℕ) = 1 := by decide

example :
    oneTriple.oneModelCount = 3 ∧
    oneTriple.modelCount = 7 ∧
    oneTriple ∈ PositiveOneInExactThreeSATThree ∧
    fourTriples.oneModelCount = 0 ∧
    ¬fourTriples.OneSatisfiable ∧
    (CNF.oneModelCount [[(0, true), (0, true), (0, true)]] : ℕ) = 0 ∧
    CNF.oneModelCount ([[]] : CNF ℕ) = 0 ∧
    CNF.oneModelCount [[(0, true), (0, false)]] = 2 ∧
    OneSAT.positiveCheck [[(0, false)]] = false ∧
    OneSAT.exactClauseCheck [(0, true), (0, true), (1, true)] = false := by
  refine ⟨by decide, by decide, ?_, by decide,
    by rw [← CNF.oneModelCount_pos_iff]; decide,
    by decide, by decide, by decide, rfl, rfl⟩
  refine ⟨⟨by decide, rfl, fun v => v == 0, by decide⟩, ?_⟩
  intro v
  by_cases h₀ : v = 0
  · subst v; decide
  by_cases h₁ : v = 1
  · subst v; decide
  by_cases h₂ : v = 2
  · subst v; decide
  simp [oneTriple, CNF.vars, Ne.symm h₀, Ne.symm h₁, Ne.symm h₂]

/-- The compiler preserves model counts and obeys clause/variable bounds across `binarySource`,
`[]`, `[[]]`, `[[(2 ^ 100, true)]]`, `[[(0, true), (0, false)]]`, and a malformed width-four
clause. -/
example :
    (toPositiveOneInExactThreeSATThree binarySource).oneModelCount = 3 ∧
    (toPositiveOneInExactThreeSATThree ([] : CNF ℕ)).oneModelCount = 1 ∧
    (toPositiveOneInExactThreeSATThree ([[]] : CNF ℕ)).oneModelCount = 0 ∧
    (toPositiveOneInExactThreeSATThree binarySource).length ≤ 507 ∧
    (toPositiveOneInExactThreeSATThree binarySource).vars.length ≤ 1521 ∧
    (toPositiveOneInExactThreeSATThree [[(2 ^ 100, true)]]).length ≤ 338 ∧
    (toPositiveOneInExactThreeSATThree [[(0, true), (0, false)]]).oneModelCount = 2 ∧
    SharpPositiveOneInExactThreeSATThree
      (toPositiveOneInExactThreeSATThree
        [[(0, true), (0, false), (0, true), (0, false)]]) = 0 := by
  refine ⟨by rw [oneModelCount_toPositiveOneInExactThreeSATThree _ (by decide)]; decide,
    by rw [oneModelCount_toPositiveOneInExactThreeSATThree _ (by simp)]; decide,
    by rw [oneModelCount_toPositiveOneInExactThreeSATThree _ (by decide)]; decide,
    by
      have h := (size_toPositiveOneInExactThreeSATThree binarySource (by decide)).1
      simpa [binarySource, CNF.vars] using h,
    by
      have h := (size_toPositiveOneInExactThreeSATThree binarySource (by decide)).2
      simpa [binarySource, CNF.vars] using h,
    by
      have h := (size_toPositiveOneInExactThreeSATThree [[(2 ^ 100, true)]] (by decide)).1
      simpa [CNF.vars] using h,
    by rw [oneModelCount_toPositiveOneInExactThreeSATThree _ (by decide)]; decide,
    by rw [sharpPositiveOneInExactThreeSATThree_toPositiveOneInExactThreeSATThree]; decide⟩

/-- The formerly ambiguous input has the canonical auxiliary values. -/
example (u v w t x : Bool) :
    CNF.ExactOneGadget.DisjunctionHolds false true true true false false true true ∧
    (CNF.ExactOneGadget.DisjunctionHolds false true true u v w t x ↔
      u = true ∧ v = false ∧ w = false ∧ t = true ∧ x = true) :=
  ⟨by decide, by
    simpa [CNF.ExactOneGadget.firstAux, CNF.ExactOneGadget.secondAux,
      CNF.ExactOneGadget.thirdAux, CNF.ExactOneGadget.fourthAux,
      CNF.ExactOneGadget.fifthAux] using
        CNF.ExactOneGadget.disjunctionHolds_iff false true true u v w t x⟩

end Cslib.Tests.PositiveOneInThreeSAT

end
