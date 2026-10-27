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

example : oneTriple.oneModelCount = 3 := by decide
example : oneTriple.modelCount = 7 := by decide
example : oneTriple ∈ PositiveOneInExactThreeSATThree := by
  refine ⟨⟨by decide, rfl, fun v => v == 0, by decide⟩, ?_⟩
  intro v
  by_cases h₀ : v = 0
  · subst v; decide
  by_cases h₁ : v = 1
  · subst v; decide
  by_cases h₂ : v = 2
  · subst v; decide
  simp [oneTriple, CNF.vars, Ne.symm h₀, Ne.symm h₁, Ne.symm h₂]

/-- The four triples on four variables have no exact-one assignment, although every variable
has degree three and every clause is positive and distinct. -/
private def fourTriples : CNF ℕ :=
  [[(0, true), (1, true), (2, true)], [(0, true), (1, true), (3, true)],
    [(0, true), (2, true), (3, true)], [(1, true), (2, true), (3, true)]]

example : fourTriples.oneModelCount = 0 := by decide
example : ¬fourTriples.OneSatisfiable := by
  rw [← CNF.oneModelCount_pos_iff]
  decide

/-- Repeated variables count as repeated literal positions. -/
example : (CNF.oneModelCount [[(0, true), (0, true), (0, true)]] : ℕ) = 0 := by decide

/-- The empty positive instance has exactly one assignment on its empty support. -/
theorem empty_formula_count : CNF.oneModelCount ([] : CNF ℕ) = 1 := by decide
example : CNF.oneModelCount ([[]] : CNF ℕ) = 0 := by decide

example : CNF.oneModelCount [[(0, true), (0, false)]] = 2 := by decide

example : OneSAT.positiveCheck [[(0, false)]] = false := rfl

example : OneSAT.exactClauseCheck [(0, true), (0, true), (1, true)] = false := rfl

private def binarySource : CNF ℕ := [[(0, true), (1, true)]]

/-- The compiler preserves three models of a binary disjunction without enumerating its
many fresh variables. -/
example : (toPositiveOneInExactThreeSATThree binarySource).oneModelCount = 3 := by
  rw [oneModelCount_toPositiveOneInExactThreeSATThree _ (by decide)]
  decide

example : (toPositiveOneInExactThreeSATThree ([] : CNF ℕ)).oneModelCount = 1 := by
  rw [oneModelCount_toPositiveOneInExactThreeSATThree _ (by simp)]
  decide

example : (toPositiveOneInExactThreeSATThree ([[]] : CNF ℕ)).oneModelCount = 0 := by
  rw [oneModelCount_toPositiveOneInExactThreeSATThree _ (by decide)]
  decide

example : (toPositiveOneInExactThreeSATThree binarySource).length ≤ 507 := by
  have h := (size_toPositiveOneInExactThreeSATThree binarySource (by decide)).1
  simpa [binarySource, CNF.vars] using h

example : (toPositiveOneInExactThreeSATThree binarySource).vars.length ≤ 1521 := by
  have h := (size_toPositiveOneInExactThreeSATThree binarySource (by decide)).2
  simpa [binarySource, CNF.vars] using h

/-- Size bounds do not depend on the numeric magnitude of binary source labels. -/
example : (toPositiveOneInExactThreeSATThree [[(2 ^ 100, true)]]).length ≤ 338 := by
  have h := (size_toPositiveOneInExactThreeSATThree [[(2 ^ 100, true)]] (by decide)).1
  simpa [CNF.vars] using h

example : (toPositiveOneInExactThreeSATThree [[(0, true), (0, false)]]).oneModelCount = 2 := by
  rw [oneModelCount_toPositiveOneInExactThreeSATThree _ (by decide)]
  decide

/-- Malformed width-four syntax is rejected with count zero by the total reduction. -/
example : SharpPositiveOneInExactThreeSATThree
    (toPositiveOneInExactThreeSATThree
      [[(0, true), (0, false), (0, true), (0, false)]]) = 0 := by
  rw [sharpPositiveOneInExactThreeSATThree_toPositiveOneInExactThreeSATThree]
  decide

example : CNF.ExactOneGadget.DisjunctionHolds false true true true false false true true := by
  decide

/-- The formerly ambiguous input has exactly the canonical values. -/
example (u v w t x : Bool) :
    CNF.ExactOneGadget.DisjunctionHolds false true true u v w t x ↔
      u = true ∧ v = false ∧ w = false ∧ t = true ∧ x = true := by
  simpa [CNF.ExactOneGadget.firstAux, CNF.ExactOneGadget.secondAux,
    CNF.ExactOneGadget.thirdAux, CNF.ExactOneGadget.fourthAux,
    CNF.ExactOneGadget.fifthAux] using
      CNF.ExactOneGadget.disjunctionHolds_iff false true true u v w t x

end Cslib.Tests.PositiveOneInThreeSAT

end
