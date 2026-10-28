/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.NP.Nondeterministic
import Complexity.Computability.Complexity.Problems.SAT.PolyTime

/-!
# SAT polynomial-time and encoding regression tests

The verifier must handle empty formulas and clauses, repeated variables, sparse binary labels
and certificates of any length. The calculus tests check composition through `fun_prop`.
-/

namespace ComplexityTests.SATPolyTime

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-- `SAT`, whose certificates are genuine assignments, has a polynomial-time nondeterministic
decider. -/
example : Turing.MultiTapeNTM.DecidableInPolyTime SAT encCNF :=
  decidableInPolyTime_of_mem_NP SAT.mem_NP

/-- The complement of `UNSAT` is in `NP`, so it also has a polynomial-time nondeterministic
decider. -/
example : Turing.MultiTapeNTM.DecidableInPolyTime UNSATᶜ encCNF :=
  decidableInPolyTime_of_mem_NP UNSAT_mem_coNP

example : ComputableInPolyTime (fun φ : CNF ℕ => SAT.verifier (φ, [true, false]))
    encCNF encBool := by
  fun_prop

example : ComputableInPolyTime (fun p => (SAT.verifier p, !SAT.verifier p))
    (encPair encCNF encBits) (encPair encBool encBool) := by
  fun_prop

example : SAT.verifier ([], []) = true := rfl
example : SAT.verifier ([[]], []) = false := rfl

-- Conflicting occurrences of the same variable cannot read different certificate bits.
example : SAT.verifier ([[(7, true)], [(7, false)]], [true, false]) = false := rfl

-- The label is stored in binary; its value is not an index into the certificate.
example : SAT.verifier ([[(2 ^ 100, true)]], [true]) = true := by decide
example : SAT.verifier ([[(2 ^ 100, true)]], []) = false := by decide
example : SAT.verifier ([[(2 ^ 100, true)]], [true, false, false]) = true := by decide

-- A short certificate defaults missing positions to false, including on negative literals.
example : SAT.verifier ([[(5, true)], [(9, false)]], [true]) = true := rfl

end ComplexityTests.SATPolyTime
