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

/-! ### Unary input format, grid enumeration, certificates, and end-to-end specification -/

/-- info: true -/
#guard_msgs in
#eval outputWord 1 2 4 2 1 == encodeOutput (ExecutableGenerator.output 1 2 1 1)

example {n s : ℕ} (hn : 1 ≤ n) (hs : 1 ≤ s) :
    (inputWord 2 3 = [true, true, false, true, true, true] ∧
      (inputWord 2 3).length = 6 ∧
      parseInput (inputWord 2 3) = some (2, 3) ∧
      parseInput (inputWord 1 1) = some (1, 1) ∧
      parseInput [] = none ∧
      parseInput [true, true] = none ∧
      parseInput (inputWord 0 2) = none ∧
      parseInput (inputWord 2 0) = none ∧
      parseInput [true, false, true, false, true] = none ∧
      hittingGenerator [] = [] ∧
      hittingGenerator (inputWord 0 2) = [] ∧
      hittingGenerator (inputWord 2 0) = [] ∧
      hittingGenerator [true, false, true, false, true] = []) ∧
    (gridPointWords 0 1 2 1 1 = [] ∧
      outputWord 0 1 2 1 1 = encodeNat 2 ++ encodeNat 0 ∧
      outputWord 0 1 (CyclotomicRing.dimension 0) (CyclotomicRing.degree 0) 1 =
        encodeOutput (ExecutableGenerator.output 0 1 0 1) ∧
      hittingListWord n s = encodeOutput (hittingList n s) ∧
      hittingGenerator (inputWord n s) = encodeOutput (hittingList n s)) ∧
    ComputableInPolyTime parseInput encBits (encOption (encPair encUnary encUnary)) ∧
    ComputableInPolyTime (fun p : ℕ × ℕ => encodeOutput (hittingList p.1 p.2))
      (encPair encUnary encUnary) encBits ∧
    (ComputableInPolyTime hittingGenerator encBits encBits ∧
      ∀ n' s' : ℕ, 1 ≤ n' → 1 ≤ s' →
        hittingGenerator (inputWord n' s') = encodeOutput (hittingList n' s') ∧
          (hittingList n' s').dimension ≤ 256 * (n' + s' + 1) ^ 10 ∧
          (encodeOutput (hittingList n' s')).length ≤
            PolynomialBounds.outputConstant * (n' + s' + 1) ^ 104 ∧
          Hits s' (hittingList n' s')) :=
  ⟨by decide +kernel,
    ⟨by decide +kernel, by decide +kernel, outputWord_eq 0 1 0 1,
      hittingListWord_eq n s, hittingGenerator_inputWord hn hs⟩,
    parseInput_polytime, hittingList_polytime, hittingGenerator_spec⟩

end ComplexityTests.RationalHitting.Runtime
