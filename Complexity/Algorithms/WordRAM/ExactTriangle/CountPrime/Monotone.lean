/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Bounds
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Monotone

/-!
# Uniform native counter budgets over modulus intervals

The public scalar, address, workspace and native instruction budgets are monotone in the
runtime modulus. Prime selection can therefore call the actual counter for different primes
using one numerical admission, frame envelope and instruction budget.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

/-- Increasing the modulus increases the signed magnitude budget. -/
theorem magnitudeBudget_monotone_modulus (k A : ℕ) :
    Monotone (fun p => magnitudeBudget p k A) := by
  intro p q hpq
  have hm := Nat.mul_le_mul_right (16 ^ k)
    (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hpq 4))
  unfold magnitudeBudget
  omega

/-- One address envelope suffices for every modulus below its supplied maximum. -/
theorem addressBudget_monotone_modulus (n k scratch a b c : ℕ) :
    Monotone (fun p => addressBudget n p k scratch a b c) := by
  intro p q hpq
  have hm := Nat.mul_le_mul_left (4 ^ k) hpq
  unfold addressBudget
  apply Nat.mul_le_mul_left 32
  omega

/-- All counter workspaces end before the workspace for the largest admitted modulus. -/
theorem memoryEnd_monotone_modulus (n k scratch : ℕ) :
    Monotone (fun p => memoryEnd n p k scratch) := by
  intro p q hpq
  have hm := Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (4 ^ k) hpq)
  unfold memoryEnd
  omega

/-- The complete native pre-halt counter cost is monotone in its runtime modulus. -/
theorem cost_monotone_modulus (n : ℕ) : Monotone (cost n) := by
  intro p q hpq
  have ht := Strassen.traceBudget_monotone (Nat.clog 2 n) hpq
  have hm := Nat.mul_le_mul_right (4 ^ Nat.clog 2 n)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 14 hpq) 48)
  unfold cost readyCost
  omega

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
