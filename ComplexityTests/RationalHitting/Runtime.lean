/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

import Complexity.Computability.Circuit.Rational.Runtime

/-!
# Regression tests for the polynomial-time rational hitting-list generator

Concrete checks for `gridPointWords`, `outputWord`, `inputWord`, `parseInput`, and
`hittingGenerator`, agreement with `ExecutableGenerator.output` and
`encodeOutput (hittingList n s)`, polynomial-time certificates, and the end-to-end hitting
specification.
-/

namespace ComplexityTests.RationalHitting.Runtime

open Cslib.Circuits Cslib.Circuits.Rational
open Turing MultiTapeTM MultiTapeTM.ComputableTidilyInPolyTime

/-! ### Unary input format and parser -/

example : inputWord 2 3 = [true, true, false, true, true, true] := by decide +kernel
example : (inputWord 2 3).length = 6 := by decide +kernel
example : parseInput (inputWord 2 3) = some (2, 3) := by decide +kernel
example : parseInput (inputWord 1 1) = some (1, 1) := by decide +kernel

-- Malformed inputs (missing separator, `n = 0`, `s = 0`, or extra `false` bits) parse to `none`.
example : parseInput [] = none := by decide +kernel
example : parseInput [true, true] = none := by decide +kernel
example : parseInput (inputWord 0 2) = none := by decide +kernel
example : parseInput (inputWord 2 0) = none := by decide +kernel
example : parseInput [true, false, true, false, true] = none := by decide +kernel

example : hittingGenerator [] = [] := by decide +kernel
example : hittingGenerator (inputWord 0 2) = [] := by decide +kernel
example : hittingGenerator (inputWord 2 0) = [] := by decide +kernel
example : hittingGenerator [true, false, true, false, true] = [] := by decide +kernel

/-! ### Grid enumeration and output encoding on small parameters -/

example : gridPointWords 0 1 2 1 1 = [] := by decide +kernel
example : outputWord 0 1 2 1 1 = encodeNat 2 ++ encodeNat 0 := by decide +kernel

example :
    outputWord 0 1 (CyclotomicRing.dimension 0) (CyclotomicRing.degree 0) 1 =
      encodeOutput (ExecutableGenerator.output 0 1 0 1) :=
  outputWord_eq 0 1 0 1

/-- info: true -/
#guard_msgs in
#eval outputWord 1 2 4 2 1 == encodeOutput (ExecutableGenerator.output 1 2 1 1)

example (n s : ℕ) : hittingListWord n s = encodeOutput (hittingList n s) :=
  hittingListWord_eq n s

example {n s : ℕ} (hn : 1 ≤ n) (hs : 1 ≤ s) :
    hittingGenerator (inputWord n s) = encodeOutput (hittingList n s) :=
  hittingGenerator_inputWord hn hs

/-! ### Polynomial-time certificates and end-to-end specification -/

example :
    ComputableInPolyTime (fun w : List Bool => parseInput (true :: w))
      encBits (encOption (encPair encUnary encUnary)) := by
  fun_prop

example :
    ComputableInPolyTime (fun p : ℕ × ℕ => encodeOutput (hittingList (p.1 + 1) (p.2 + 1)))
      (encPair encUnary encUnary) encBits :=
  computableInPolyTime_hittingList (by fun_prop) (by fun_prop)

example :
    ComputableInPolyTime (fun p : List Bool × List Bool => hittingGenerator (p.1 ++ p.2))
      (encPair encBits encBits) encBits :=
  hittingGenerator_polytime.comp (g := fun p : List Bool × List Bool => p.1 ++ p.2) (by fun_prop)

example :
    hittingGenerator (inputWord 1 2) = encodeOutput (hittingList 1 2) ∧
      (hittingList 1 2).dimension ≤ 256 * 4 ^ 10 ∧
      (encodeOutput (hittingList 1 2)).length ≤ PolynomialBounds.outputConstant * 4 ^ 104 ∧
      Hits 2 (hittingList 1 2) :=
  hittingGenerator_spec.2 1 2 le_rfl (by decide)

end ComplexityTests.RationalHitting.Runtime
