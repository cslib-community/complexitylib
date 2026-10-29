/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.ExactTriangle.Hashing

/-!
# Modular Exact Triangle counting and prime-selection regressions

Concrete zeros, false positives, coefficient wraparound, minimum selection, the integer window
boundary and an admitted instance of the universal bound. These assert no native running time.
-/

namespace ComplexityTests.ExactTriangleHashing

open Cslib Cslib.Algorithms.ExactTriangle

private def ab (a _ : Fin 2) : ℤ := if a = 0 then 0 else 2
private def z (_ _ : Fin 2) : ℤ := 0

private theorem window16 : Nat.sqrtPrimeWindow 16 = {2, 3} := by
  rw [Nat.sqrtPrimeWindow_eq_filter]
  decide

-- Both endpoints matter: prime 2 is admitted at the lower endpoint for D=16;
-- prime 5 is excluded at the upper endpoint for D=25, and prime 3 is admitted there.
example : 2 ∈ Nat.sqrtPrimeWindow 16 ∧ 5 ∉ Nat.sqrtPrimeWindow 25 ∧ 3 ∈ Nat.sqrtPrimeWindow 25 := by
  simp only [Nat.mem_sqrtPrimeWindow_iff_sq]
  decide

example : 2 ∉ Nat.sqrtPrimeWindow 17 := by rw [Nat.mem_sqrtPrimeWindow_iff_sq]; decide

example : countZeroMod ab z z 2 = 8 ∧ countZeroMod ab z z 3 = 4 := by
  unfold countZeroMod weightSum ab z
  decide

example : zeroCount ab z z = 4 ∧ falsePositiveCount ab z z 2 = 4 ∧
    falsePositiveCount ab z z 3 = 0 := by
  unfold zeroCount falsePositiveCount IsFalsePositive weightSum ab z
  decide

example : countZeroMod ab z z 0 = 4 ∧ falsePositiveCount ab z z 0 = 0 := by
  unfold countZeroMod falsePositiveCount IsFalsePositive weightSum ab z
  decide

-- Counting distinguishes the two candidate primes; the minimum is 3.
example : IsSelectedPrime ab z z 16 3 ∧ ¬IsSelectedPrime ab z z 16 2 := by
  simp only [IsSelectedPrime, window16]
  unfold countZeroMod weightSum ab z
  decide

-- A tie permits either minimum prime; the predicate does not impose a tie-break.
example : IsSelectedPrime (fun _ _ : Fin 1 => 0) (fun _ _ => 0) (fun _ _ => 0) 16 2 ∧
    IsSelectedPrime (fun _ _ : Fin 1 => 0) (fun _ _ => 0) (fun _ _ => 0) 16 3 := by
  constructor <;> refine ⟨by rw [window16]; decide, ?_⟩ <;> intro q _ <;>
    simp [countZeroMod, weightSum]

example : HasZeroTriangle ab z z := ⟨0, 0, 0, rfl⟩
example : 0 < zeroCount ab z z := (zeroCount_pos_iff ab z z).mpr ⟨0, 0, 0, rfl⟩

private def one (_ _ : Fin 2) : ℤ := 1

example : ¬HasZeroTriangle one one one := by
  rintro ⟨a, b, c, h⟩
  norm_num [one] at h

example : zeroCount one one one = 0 ∧ countZeroMod one one one 3 = 8 ∧
    falsePositiveCount one one one 3 = 8 := by
  unfold zeroCount countZeroMod falsePositiveCount IsFalsePositive weightSum one
  decide

-- A negative residue and a positive residue wrap to exponent zero modulo 3.
example : CyclicIntRing.coeff (by decide : 3 ≠ 0) 0
    ((matP (fun _ _ : Fin 2 => (-1 : ℤ)) 3 *
      matQ (fun _ _ : Fin 2 => (1 : ℤ)) 3) 0 0) = 2 := by
  rw [coeff_matP_mul_matQ (fun _ _ : Fin 2 => (1 : ℤ))
    (fun _ _ : Fin 2 => (-1 : ℤ)) (by decide) 0 0 0 (by decide)]
  decide

-- These matrices are asymmetric: transposing either input changes the selected count.
private def ac (a c : Fin 2) : ℤ := if a = 0 then if c = 0 then -1 else 2 else 0
private def bc (b c : Fin 2) : ℤ := if b = 0 ∧ c = 1 then 1 else 0

example : CyclicIntRing.coeff (by decide : 3 ≠ 0) 0 ((matP ac 3 * matQ bc 3) 0 0) = 1 := by
  rw [coeff_matP_mul_matQ bc ac (by decide) 0 0 0 (by decide)]
  unfold ac bc
  decide

example : CyclicIntRing.coeff (by decide : 2 ≠ 0) 1 (CyclicIntRing.x 2 ^ 5) = 1 := by
  rw [CyclicIntRing.coeff_x_pow]
  norm_num

example : CyclicIntRing.coeff (by decide : 2 ≠ 0) 3 (CyclicIntRing.x 2 ^ 5) = 0 := by
  rw [CyclicIntRing.coeff_x_pow]
  norm_num

example : zeroCount (fun _ _ : Fin 0 => 0) (fun _ _ => 0) (fun _ _ => 0) = 0 := by
  simp [zeroCount]

example : ¬WeightsBoundedBy (fun _ _ : Fin 1 => (0 : ℤ)) (fun _ _ => 0) (fun _ _ => 0) (-1) := by
  norm_num [WeightsBoundedBy]

-- The full bound's n,D,kappa hypotheses and input bound have a concrete witness.
example : (falsePositiveCount (fun _ _ : Fin 16 => 0) (fun _ _ => 0) (fun _ _ => 0) 2 : ℝ) ≤
    falsePositiveConst * (1 * (16 : ℝ) ^ 3 * Real.log 16 / Real.sqrt 16) := by
  apply falsePositiveCount_le_const_mul (by decide : 16 ≤ 16) (by decide : 16 ≤ 16)
    (by norm_num : (1 : ℝ) ≤ 1)
  · norm_num [WeightsBoundedBy]
  · refine ⟨by rw [window16]; decide, ?_⟩
    intro q _
    simp [countZeroMod, weightSum]

end ComplexityTests.ExactTriangleHashing
