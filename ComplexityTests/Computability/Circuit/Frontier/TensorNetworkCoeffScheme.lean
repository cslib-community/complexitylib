/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.CoeffScheme

/-!
# Tests for coefficient extraction as a stack recursion

Two rows `1` and `2` over `A_3 = (ℤ / 8)[U] / (U ^ 2 + U + 1)`, with the modes of dense indices
`0` and `2`. The row `r` has the local term `r` and the coefficient `k + 1 + U` at the mode `k`.
The coefficient of the mode `0` in the product of the two row factors is
`1 (1 + U) + (1 + U) 2 = 3 + 3 U`, and the machine returns it.
-/

@[expose] public section

namespace ComplexityTests.TensorNetworkCoeffScheme

open Cslib Cslib.Circuits.Frontier Cslib.Circuits.Frontier.CoeffScheme

/-- The data of the test. -/
def terms : Terms Unit ℕ where
  prec _ := (3, [1, 1])
  modes _ := [0, 2]
  term _ r o := match o with
    | none => [r, 0]
    | some k => [k + 1, 1]

-- The value, at exponent `1` on the mode `0`.
example : terms.value () [1, 2] [1, 0, 0] = [3, 3] := by decide

-- The stack machine, with fuel `2 (2 + 2) ^ 2 = 32`, returns it.
example : terms.scheme.run terms.fuel id ((), ([1, 2], [1, 0, 0])) = some [3, 3] := by decide

-- With both exponents zero, the coefficient of the constant term is `1 * 2 = 2`.
example : terms.value () [1, 2] [0, 0, 0] = [2, 0] := by decide

-- A mode needed twice from one row factor has coefficient zero.
example : terms.value () [1] [2, 0, 0] = [0, 0] := by decide

-- On every node, the run is the value, and the value in `A_p` is `listCoeff`.
example (x : Node Unit ℕ) :
    terms.scheme.run terms.fuel id x = some (terms.value x.1 x.2.1 x.2.2) :=
  terms.run_scheme x

example (rows : List ℕ) (γ : List ℕ) :
    GaloisRingArith.val 3 [1, 1] (terms.value () rows γ) =
      TensorNetwork.listCoeff ({0, 2} : Finset ℕ)
        (rows.map fun r o => GaloisRingArith.val 3 [1, 1] (terms.term () r o))
        (fun k => γ.getD k 0) :=
  terms.val_value () (by decide) rows γ

-- At most `(m + 2) ^ L` nodes.
example : count 2 2 = 13 ∧ count 2 2 ≤ (2 + 2) ^ 2 := by decide

end ComplexityTests.TensorNetworkCoeffScheme
