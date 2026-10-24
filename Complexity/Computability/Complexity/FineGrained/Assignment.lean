/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained
import Complexity.Computability.Complexity.Problems.SAT.PolyTime

/-!
# Numbered assignments

Exhaustive search over the assignments of the `n` distinct variables of a formula enumerates the
numbers `i < 2 ^ n`. `Cslib.Logic.PL.bitsAssignment vs i` gives the variable at position `j` of
the list `vs` the binary digit `j` of `i`. Every assignment of the variables of a duplicate-free
list `vs` is numbered by some `i < 2 ^ |vs|` (`Cslib.Logic.PL.exists_lt_two_pow_bitsAssignment_eq`),
so a formula whose variables are listed by `vs` is satisfiable exactly when one of the numbered
assignments satisfies it (`Cslib.Logic.PL.CNF.satisfiable_iff_exists_bitsAssignment`). The
distinct variables of a formula are listed by `Cslib.Logic.PL.CNF.distinctVars`, of length
`Cslib.Logic.PL.CNF.numVars` (`Cslib.Logic.PL.CNF.length_distinctVars`). Evaluating a
formula under a numbered assignment is polynomial-time
(`Cslib.Complexity.computableInPolyTime_eval_bitsAssignment`).

## Main results

* `Cslib.Complexity.computableInPolyTime_eval_bitsAssignment`: evaluation under a numbered
  assignment is polynomial-time.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 2.3][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Evaluating a formula under the assignment numbered by `i` on a list of variables is
polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_eval_bitsAssignment :
    ComputableInPolyTime
      (fun p : (CNF ℕ × List ℕ) × ℕ => p.1.1.eval (bitsAssignment p.1.2 p.2))
      (encPair (encPair encCNF (encList encNat)) encNat) encBool :=
  (CNF.computableInPolyTime_eval_bitsAssignment encNat)

end Cslib.Complexity
