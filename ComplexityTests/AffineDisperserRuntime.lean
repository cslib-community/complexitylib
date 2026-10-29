/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.AffineDisperser.PolyTime

/-!
# The explicit affine disperser as a polynomial-time program: clients

The binary polynomial routines are checked on small cases by evaluation in the kernel: a remainder
modulo `X ^ 2 + X + 1`, trial division, and the search for the irreducible polynomial of degree
`5` of least code, `X ^ 5 + X ^ 2 + 1`. At `N = 512` the field degree is the single prime `5`, so
the explicit field is `𝔽₃₂` with `r = 102` blocks and `t = 10`. Two pseudorandom inputs of that
length, from a linear congruential generator, take different values; an independent
implementation (tensor-product arithmetic with reduction in each variable and the trace as a sum of
Frobenius conjugates) gives the same values. The roots `binaryRoot` satisfy the hypothesis of the
root-independence theorem, so it applies.
-/

namespace ComplexityTests.AffineDisperserRuntime

open Cslib Cslib.AffineDisperser Cslib.AffineDisperser.Explicit Turing.MultiTapeTM

/-! ### Binary polynomials -/

-- `X ^ 4 = X` modulo `X ^ 2 + X + 1`, `X ^ 2 + 1` is reducible while `X ^ 2 + X + 1` is
-- irreducible, and the least irreducible polynomial of degree `5` has code `37`.
example :
    modBits [true, true, true] [false, false, false, false, true] = [false, true] ∧
      isIrreducibleCode 5 = false ∧
      isIrreducibleCode 7 = true ∧
      leastIrreducibleCode 64 5 = 37 ∧
      leastIrreducible 5 = polyOfCode 37 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  rw [← polyOfCode_leastIrreducibleCode (B := 64) (by norm_num) (by norm_num),
    show leastIrreducibleCode 64 5 = 37 by decide]

/-! ### The explicit disperser on `512` bits -/

example :
    degreePrimes 512 = [5] ∧
      fieldDegree 512 = 5 ∧
      numBlocks 512 = 102 ∧
      symDegree 512 = 10 := by
  decide

/-- Pseudorandom bits from the linear congruential generator `s ↦ 1103515245 s + 12345` modulo
`2 ^ 31`, reading bit `16` of each state. -/
def lcgBits (N seed : ℕ) : List Bool :=
  ((List.range N).foldl (fun (state : ℕ × List Bool) _ =>
    let s := (state.1 * 1103515245 + 12345) % 2 ^ 31
    (s, state.2 ++ [s / 2 ^ 16 % 2 == 1])) (seed, [])).2

/-- info: (512, false, true) -/
#guard_msgs in
#eval ((lcgBits 512 4).length, explicitDisperserProgram (lcgBits 512 4),
  explicitDisperserProgram (lcgBits 512 5))

/-- The program computes the explicit disperser, and the roots `binaryRoot` satisfy the
root-independence theorem at `N = 512`. -/
example (seed : ℕ) :
    explicitDisperserProgram (lcgBits 512 seed) =
      explicitDisperser (lcgBits 512 seed).length
        (BitString.ofList (lcgBits 512 seed).length (lcgBits 512 seed)) ∧
    traceSymBits (1 : ExplicitField 512) (numBlocks 512) (symDegree 512)
        (rootBasis 512 (fun j => binaryRoot (degreePrime 512 j) (fieldDegree 512))
          (aeval_binaryRoot_degreePrime 512)) (explicitPos 512) =
      explicitDisperser 512 :=
  ⟨explicitDisperserProgram_eq _, traceSymBits_rootBasis_eq_explicitDisperser 512 _ _⟩

end ComplexityTests.AffineDisperserRuntime
