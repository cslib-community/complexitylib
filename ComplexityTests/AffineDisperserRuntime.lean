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
root-independence theorem, so it applies. Axiom checks record the headline dependencies.
-/

namespace ComplexityTests.AffineDisperserRuntime

open Cslib Cslib.AffineDisperser Cslib.AffineDisperser.Explicit Turing.MultiTapeTM

/-! ### Binary polynomials -/

-- `X ^ 4 = X` modulo `X ^ 2 + X + 1`, since `X ^ 3 = 1` there.
example : modBits [true, true, true] [false, false, false, false, true] = [false, true] := by
  decide

-- `X ^ 2 + 1 = (X + 1) ^ 2` is reducible, and `X ^ 2 + X + 1` is irreducible.
example : isIrreducibleCode 5 = false := by decide
example : isIrreducibleCode 7 = true := by decide

-- The least irreducible polynomial of degree `5` is `X ^ 5 + X ^ 2 + 1`, with code `37`.
example : leastIrreducibleCode 64 5 = 37 := by decide

example : leastIrreducible 5 = polyOfCode 37 := by
  rw [← polyOfCode_leastIrreducibleCode (B := 64) (by norm_num) (by norm_num),
    show leastIrreducibleCode 64 5 = 37 by decide]

/-! ### The explicit disperser on `512` bits -/

example : degreePrimes 512 = [5] := by decide
example : fieldDegree 512 = 5 := by decide
example : numBlocks 512 = 102 := by decide
example : symDegree 512 = 10 := by decide

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

/-- The program computes the explicit disperser, so the two runs above are values of
`explicitDisperser 512`. -/
example (seed : ℕ) :
    explicitDisperserProgram (lcgBits 512 seed) =
      explicitDisperser (lcgBits 512 seed).length
        (BitString.ofList (lcgBits 512 seed).length (lcgBits 512 seed)) :=
  explicitDisperserProgram_eq _

/-- The hypothesis of the root-independence theorem is satisfiable: the roots `binaryRoot`. -/
example (N : ℕ) :
    traceSymBits (1 : ExplicitField N) (numBlocks N) (symDegree N)
        (rootBasis N (fun j => binaryRoot (degreePrime N j) (fieldDegree N))
          (aeval_binaryRoot_degreePrime N)) (explicitPos N) =
      explicitDisperser N :=
  traceSymBits_rootBasis_eq_explicitDisperser N _ _

/-! ### Axioms -/

/--
info: 'Cslib.AffineDisperser.computableInPolyTime_explicitDisperser' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms computableInPolyTime_explicitDisperser

/--
info: 'Cslib.AffineDisperser.setOf_explicitDisperser_mem_P' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms setOf_explicitDisperser_mem_P

/--
info: 'Cslib.AffineDisperser.explicitDisperserProgram_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms explicitDisperserProgram_eq

/--
info: 'Cslib.AffineDisperser.traceSymBits_rootBasis_eq_explicitDisperser' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms traceSymBits_rootBasis_eq_explicitDisperser

/--
info: 'Cslib.AffineDisperser.traceSymCoords_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms traceSymCoords_eq

/--
info: 'Cslib.AffineDisperser.isMulTable_monomialTable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isMulTable_monomialTable

/--
info: 'Cslib.prodPowBasis_mul_prodPowBasis' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prodPowBasis_mul_prodPowBasis

/--
info: 'Cslib.AffineDisperser.isIrreducibleCode_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isIrreducibleCode_iff

/--
info: 'Cslib.AffineDisperser.polyOfCode_leastIrreducibleCode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms polyOfCode_leastIrreducibleCode

/--
info: 'Cslib.AffineDisperser.computableInPolyTime_traceSymCoords' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms computableInPolyTime_traceSymCoords

end ComplexityTests.AffineDisperserRuntime
