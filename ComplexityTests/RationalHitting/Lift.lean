/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

import Complexity.Computability.Circuit.Rational.Runtime.Lift

/-!
# Regression tests for the integer lift list program

Concrete coefficient rows, Taylor test matrices and lift tables, checked by the kernel and
compiled, agreeing with the landed definitions `IntegralTest.padded` and
`ExecutableGenerator.inputTables`. The correctness theorems are instantiated on concrete
parameters, and the bit-length bounds on concrete inputs and at the generator's parameters for
`n = s = 0`, so their hypotheses are satisfiable.
-/

namespace ComplexityTests.RationalHitting.Lift

open Cslib.Circuits Cslib.Circuits.Rational

/-! ### Coefficient rows, Taylor test matrices, and lift tables -/

/-- info: ([8, 12, 6, 1], [1, -4, 6, -4, 1], 270) -/
#guard_msgs in
#eval (coeffRow 2 3, coeffRow (-1) 4, (coeffRow 3 5).getD 2 0)

/-- info: (true, true) -/
#guard_msgs in
#eval (testRows 4 2 1 2 == rowsOf (IntegralTest.padded 4 2 1 2),
  testRows 4 3 (-2) 5 == rowsOf (IntegralTest.padded 4 3 (-2) 5))

/-- info: [[-1, 1, 0, 0], [3, -1, 0, 0], [-3, -1, 0, 0], [1, 1, 0, 0]] -/
#guard_msgs in
#eval rowsOf (IntegralTest.padded 4 2 1 2)

/-- info: true -/
#guard_msgs in
#eval liftRows 1 2 4 2 1 2 3 == (ExecutableGenerator.inputTables 1 2 1 ![1, 2, 3]).toList.map
  fun A => rowsOf (DeterminantAlgorithm.denote A)

example :
    (coeffRow 2 3 = [8, 12, 6, 1] ∧
      coeffRow (-1) 4 = [1, -4, 6, -4, 1] ∧
      (coeffRow 3 5).getD 2 0 = 3 ^ 3 * (Nat.choose 5 2 : ℤ) ∧
      (coeffRow 3 5).getD 2 0 = 270 ∧
      coeffRows 1 3 = [[1], [1, 1], [1, 2, 1]]) ∧
    testRows 4 2 1 2 = [[-1, 1, 0, 0], [3, -1, 0, 0], [-3, -1, 0, 0], [1, 1, 0, 0]] ∧
    rowsOf (IntegralTest.padded 4 2 1 2) =
      [[-1, 1, 0, 0], [3, -1, 0, 0], [-3, -1, 0, 0], [1, 1, 0, 0]] ∧
    liftRows 0 1 2 1 1 1 1 = [[[0, 0], [2, 0]]] ∧
    liftRows 1 2 4 2 1 2 3 = (ExecutableGenerator.inputTables 1 2 1 ![1, 2, 3]).toList.map
      (fun A => rowsOf (DeterminantAlgorithm.denote A)) ∧
    liftRows 0 1 2 1 1 1 1 = [rowsOf (Generator.integralLift 0 1 0 ![1, 1, 1] 0)] ∧
    rowEntry (liftTable 4 2 (testRows 4 2 (1 : ℕ) (1 : ℕ)) (2 : ℕ) (3 : ℕ)) 6 0 =
      Generator.integralLift 1 2 1 ![1, 2, 3] 1 ⟨6, by decide⟩ ⟨0, by decide⟩ ∧
    liftRows 1 2 4 2 1 2 3 = [[
        [0, 0, -81, 162, 0, 0, -15, 0],
        [0, 0, -162, -81, 0, 0, 0, -15],
        [-9, -18, 0, 0, -135, 0, 0, 0],
        [18, -9, 0, 0, 0, -135, 0, 0],
        [0, 0, 45, 0, 0, 0, -81, -162],
        [0, 0, 0, 45, 0, 0, 162, -81],
        [405, 0, 0, 0, -9, 18, 0, 0],
        [0, 405, 0, 0, -18, -9, 0, 0]],
      [
        [-18, -6, -81, 162, 108, 54, 3, -54],
        [6, -18, -162, -81, -54, 108, 54, 3],
        [153, 36, 18, -6, -135, 0, 36, 162],
        [-36, 153, 6, 18, 0, -135, -162, 36],
        [-432, -54, -117, 54, 2, 6, -81, -162],
        [54, -432, -54, -117, -6, 2, 162, -81],
        [405, 0, 216, -162, -27, -36, -2, 6],
        [0, 405, 162, 216, 36, -27, -6, -2]]] := by
  refine ⟨⟨by decide +kernel, by decide +kernel, by decide +kernel,
      by rw [getD_coeffRow_eq]; decide +kernel, by decide +kernel⟩,
    by decide +kernel, ?_, by decide +kernel, liftRows_eq_inputTables 1 2 1 ![1, 2, 3],
    liftRows_eq 0 1 0 ![1, 1, 1],
    rowEntry_liftTable 1 2 1 ![1, 2, 3] 1 ⟨6, by decide⟩ ⟨0, by decide⟩,
    by decide +kernel⟩
  rw [← testRows_eq]
  decide +kernel

/-! ### Bit lengths and polynomial-time certificates -/

/-- info: 10 -/
#guard_msgs in
#eval ((liftRows 1 2 4 2 1 2 3).flatten.flatten.map intBits).foldr max 0

/-- info: (53, 4654) -/
#guard_msgs in
#eval (((liftRows 0 2 4 2 385 385 385).flatten.flatten.map intBits).foldr max 0,
  liftBits 0 4 385)

open Turing MultiTapeTM MultiTapeTM.ComputableTidilyInPolyTime

attribute [local fun_prop] ComputableInPolyTime.tidy in
example (k u v i j m : ℕ)
    {table₁ : List (List ℤ)} (htable₁ : table₁ ∈ liftRows 1 2 4 2 1 2 3) {row₁ : List ℤ}
    (hrow₁ : row₁ ∈ table₁) {z₁ : ℤ} (hz₁ : z₁ ∈ row₁)
    {table₀ : List (List ℤ)} (htable₀ : table₀ ∈ liftRows 0 2 4 2 385 385 385) {row₀ : List ℤ}
    (hrow₀ : row₀ ∈ table₀) {z₀ : ℤ} (hz₀ : z₀ ∈ row₀) :
    (liftBits 1 4 3 = 86 ∧ liftBits 0 4 385 = PolynomialBounds.logarithmic 0 0 + 2) ∧
    (intBits ((coeffRow (-1) 3).getD i 0) ≤ liftBits 1 4 3 ∧
      intBits ((0 :: coeffRow (-1) 3).getD i 0) ≤ liftBits 1 4 3 ∧
      intBits (-1 * (coeffRow (-1) 3).getD i 0) ≤ liftBits 1 4 3 ∧
      intBits ((0 :: coeffRow (-1) 3).getD i 0 + -1 * (coeffRow (-1) 3).getD i 0) ≤
        liftBits 1 4 3) ∧
    (intBits ((testTerms 4 (coeffRows (-1) 4) (coeffRows 1 4) 2 u v).take m).sum ≤
        liftBits 1 4 3 ∧
      intBits (rowEntry (testRows 4 2 1 2) u v) ≤ liftBits 1 4 3) ∧
    intBits ((liftSums 4 2 (testRows 4 2 1 1) 2 3 u v i j).take m).sum ≤ liftBits 1 4 3 ∧
    intBits z₁ ≤ liftBits 1 4 3 ∧
    intBits z₀ ≤ PolynomialBounds.logConstant * 1 ^ 22 + 2 ∧
    (encList encIntBin (coeffRow 2 3)).length ≤ coeffRowBound (encIntBin 2).length 3 ∧
    ComputableInPolyTime (fun p : ℤ × ℕ => coeffRow p.1 p.2)
      (encPair encIntBin encUnary) (encList encIntBin) ∧
    ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℤ × ℤ) => testRows p.1.1 p.1.2 p.2.1 p.2.2)
      (encPair (encPair encUnary encUnary) (encPair encIntBin encIntBin))
      (encList (encList encIntBin)) ∧
    ComputableInPolyTime
      (fun q : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
        liftRows q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2)
      (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary
        (encPair encUnary (encPair encUnary encUnary))))))
      (encList (encList (encList encIntBin))) :=
  let htest := intBits_test_le (by norm_num) (by norm_num) (by decide) (by decide) 2 k u v 0 m
    (by norm_num)
  ⟨⟨by decide +kernel, liftBits_parameters 0 0⟩,
    intBits_coeffRow_le (by norm_num) (by norm_num) (by decide) (by norm_num) i,
    ⟨htest.2.2.1, htest.2.2.2⟩,
    (intBits_lift_le (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide)
      2 2 u v i j 0 0 0 m (α := 0) (κ := 0) (by norm_num)).2.2.2.2.1,
    intBits_le_of_mem_liftRows (H := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) htable₁ hrow₁ hz₁,
    intBits_le_of_mem_liftRows_parameters (n := 0) (s := 0) (by decide) (by decide) (by decide)
      htable₀ hrow₀ hz₀,
    length_encList_coeffRow_le 2 le_rfl,
    .of_tidy (by fun_prop), .of_tidy (by fun_prop), liftRows_polytime⟩

end ComplexityTests.RationalHitting.Lift
