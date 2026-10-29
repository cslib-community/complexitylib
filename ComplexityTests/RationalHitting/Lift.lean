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

/-! ### Coefficient rows -/

example : coeffRow 2 3 = [8, 12, 6, 1] := by decide +kernel
example : coeffRow (-1) 4 = [1, -4, 6, -4, 1] := by decide +kernel
example : (coeffRow 3 5).getD 2 0 = 3 ^ 3 * (Nat.choose 5 2 : ℤ) := by decide +kernel
example : (coeffRow 3 5).getD 2 0 = 270 := by rw [getD_coeffRow_eq]; decide +kernel
example : coeffRows 1 3 = [[1], [1, 1], [1, 2, 1]] := by decide +kernel

/-- info: ([8, 12, 6, 1], [1, -4, 6, -4, 1], 270) -/
#guard_msgs in
#eval (coeffRow 2 3, coeffRow (-1) 4, (coeffRow 3 5).getD 2 0)

/-! ### Taylor test matrices -/

example : testRows 4 2 1 2 = [[-1, 1, 0, 0], [3, -1, 0, 0], [-3, -1, 0, 0], [1, 1, 0, 0]] := by
  decide +kernel

-- The list program agrees with `IntegralTest.padded`, compiled and through the theorem.
/-- info: (true, true) -/
#guard_msgs in
#eval (testRows 4 2 1 2 == rowsOf (IntegralTest.padded 4 2 1 2),
  testRows 4 3 (-2) 5 == rowsOf (IntegralTest.padded 4 3 (-2) 5))

example : rowsOf (IntegralTest.padded 4 2 1 2) =
    [[-1, 1, 0, 0], [3, -1, 0, 0], [-3, -1, 0, 0], [1, 1, 0, 0]] := by
  rw [← testRows_eq]
  decide +kernel

/-- info: [[-1, 1, 0, 0], [3, -1, 0, 0], [-3, -1, 0, 0], [1, 1, 0, 0]] -/
#guard_msgs in
#eval rowsOf (IntegralTest.padded 4 2 1 2)

/-! ### Lift tables -/

-- One matrix (`n = 0`) with `e = 0`: two residues, cyclotomic degree one.
example : liftRows 0 1 2 1 1 1 1 = [[[0, 0], [2, 0]]] := by decide +kernel

-- Two matrices (`n = 1`) with `e = 1`: four residues, cyclotomic degree two, dimension eight.
/-- info: true -/
#guard_msgs in
#eval liftRows 1 2 4 2 1 2 3 == (ExecutableGenerator.inputTables 1 2 1 ![1, 2, 3]).toList.map
  fun A => rowsOf (DeterminantAlgorithm.denote A)

example : (List.finRange (0 + 1)).map
    (fun a => rowsOf (Generator.integralLift 0 1 0 ![1, 1, 1] a)) = [[[0, 0], [2, 0]]] := by
  rw [← liftRows_eq 0 1 0 ![1, 1, 1]]
  decide +kernel

example :
    Generator.integralLift 1 2 1 ![1, 2, 3] 1 ⟨6, by decide⟩ ⟨0, by decide⟩ = 405 := by
  rw [← rowEntry_liftTable 1 2 1 ![1, 2, 3] 1 ⟨6, by decide⟩ ⟨0, by decide⟩]
  decide +kernel

-- The two lift tables, evaluated by the kernel.
example : liftRows 1 2 4 2 1 2 3 = [[
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
  decide +kernel

/-! ### Bit lengths -/

example : liftBits 1 4 3 = 86 := by decide +kernel
example : PolynomialBounds.logarithmic 0 0 + 2 = 4654 := by
  rw [← liftBits_parameters 0 0]
  decide +kernel

-- The hypotheses of the bounds hold on concrete inputs.
example (i : ℕ) :
    intBits ((coeffRow (-1) 3).getD i 0) ≤ liftBits 1 4 3 ∧
      intBits ((0 :: coeffRow (-1) 3).getD i 0) ≤ liftBits 1 4 3 ∧
      intBits (-1 * (coeffRow (-1) 3).getD i 0) ≤ liftBits 1 4 3 ∧
      intBits ((0 :: coeffRow (-1) 3).getD i 0 + -1 * (coeffRow (-1) 3).getD i 0) ≤
        liftBits 1 4 3 :=
  intBits_coeffRow_le (by norm_num) (by norm_num) (by decide) (by norm_num) i

example (k u v m : ℕ) :
    intBits ((testTerms 4 (coeffRows (-1) 4) (coeffRows 1 4) 2 u v).take m).sum ≤
      liftBits 1 4 3 ∧ intBits (rowEntry (testRows 4 2 1 2) u v) ≤ liftBits 1 4 3 :=
  let h := intBits_test_le (by norm_num) (by norm_num) (by decide) (by decide) 2 k u v 0 m
    (by norm_num)
  ⟨h.2.2.1, h.2.2.2⟩

example (u v i j m : ℕ) :
    intBits ((liftSums 4 2 (testRows 4 2 1 1) 2 3 u v i j).take m).sum ≤ liftBits 1 4 3 :=
  (intBits_lift_le (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide)
    2 2 u v i j 0 0 0 m (α := 0) (κ := 0) (by norm_num)).2.2.2.2.1

example {table : List (List ℤ)} (htable : table ∈ liftRows 1 2 4 2 1 2 3) {row : List ℤ}
    (hrow : row ∈ table) {z : ℤ} (hz : z ∈ row) : intBits z ≤ liftBits 1 4 3 :=
  intBits_le_of_mem_liftRows (H := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) htable hrow hz

-- The largest entry of these tables has ten bits.
/-- info: 10 -/
#guard_msgs in
#eval ((liftRows 1 2 4 2 1 2 3).flatten.flatten.map intBits).foldr max 0

-- At the generator's parameters for `n = s = 0`: `N = 2`, `M = 4`, `Dg = 2`, `H = 385`.
example {table : List (List ℤ)} (htable : table ∈ liftRows 0 2 4 2 385 385 385) {row : List ℤ}
    (hrow : row ∈ table) {z : ℤ} (hz : z ∈ row) :
    intBits z ≤ PolynomialBounds.logConstant * 1 ^ 22 + 2 :=
  intBits_le_of_mem_liftRows_parameters (n := 0) (s := 0) (by decide) (by decide) (by decide)
    htable hrow hz

/-- info: (53, 4654) -/
#guard_msgs in
#eval (((liftRows 0 2 4 2 385 385 385).flatten.flatten.map intBits).foldr max 0,
  liftBits 0 4 385)

/-! ### Polynomial-time certificates -/

open Turing MultiTapeTM

example : ComputableInPolyTime (fun p : ℤ × ℕ => coeffRow p.1 p.2)
    (encPair encIntBin encUnary) (encList encIntBin) := by
  fun_prop

example : ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℤ × ℤ) =>
    testRows p.1.1 p.1.2 p.2.1 p.2.2)
    (encPair (encPair encUnary encUnary) (encPair encIntBin encIntBin))
    (encList (encList encIntBin)) := by
  fun_prop

example : ComputableInPolyTime
    (fun p : ℕ × ℕ => (liftRows p.1 p.2 p.1 p.2 p.1 p.2 p.1).length)
    (encPair encUnary encUnary) encUnary :=
  (ComputableInPolyTime.of_tidy (.length_list (encList (encList encIntBin)))).comp
    (by fun_prop)

end ComplexityTests.RationalHitting.Lift
