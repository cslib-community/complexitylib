/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.ExactOne
public import CslibFrontier.Logics.Propositional.CNF.ExactThree

/-!
# Exact-three ordinary clauses for exact-one semantics

A triple's exact-one predicate is expressed by five ordinary clauses on its original variables:
one excludes zero true literals and four exclude the assignments with at least two true literals.
This original truth-table encoding preserves distinctness and introduces no new variables.

## Main definitions

* `Clause.oneThreeEncoding`: five clauses on a given triple of literals.

## Main results

* `Clause.eval_oneThreeEncoding`: correctness under the same assignment.
* `Clause.isExactThreeDistinct_oneThreeEncoding`: preservation of distinct variables.
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {V : Type*}

/-- A truth-table encoding of exactly one true literal among three literal positions. -/
def Clause.oneThreeEncoding (a b c : Literal V) : CNF V :=
  [[a, b, c],
   [Std.Sat.Literal.negate a, Std.Sat.Literal.negate b, c],
   [Std.Sat.Literal.negate a, b, Std.Sat.Literal.negate c],
   [a, Std.Sat.Literal.negate b, Std.Sat.Literal.negate c],
   [Std.Sat.Literal.negate a, Std.Sat.Literal.negate b, Std.Sat.Literal.negate c]]

/-- The five ordinary clauses express positional exact-one semantics. -/
theorem Clause.eval_oneThreeEncoding (σ : V → Bool) (a b c : Literal V) :
    (oneThreeEncoding a b c).eval σ = Clause.evalOne σ [a, b, c] := by
  cases ha : Literal.eval σ a <;> cases hb : Literal.eval σ b <;>
    cases hc : Literal.eval σ c <;>
    simp [oneThreeEncoding, CNF.eval, Clause.eval, Clause.evalOne, ha, hb, hc]

/-- Distinct source variables give three distinct variables in every emitted clause. -/
theorem Clause.isExactThreeDistinct_oneThreeEncoding (a b c : Literal V)
    (h : Clause.IsExactThreeDistinct [a, b, c]) :
    (oneThreeEncoding a b c).IsExactThreeDistinct := by
  intro d hd
  simp only [oneThreeEncoding, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl
  all_goals simpa [Clause.IsExactThreeDistinct, Std.Sat.Literal.negate] using h

end Cslib.Logic.PL
