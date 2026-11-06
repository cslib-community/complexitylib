/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.State

/-!
# Monotonicity of the charged Strassen budget

At a fixed matrix depth, increasing the cyclic coefficient length can only increase the
proved native recursion budget. This permits a caller to budget a whole modulus interval
using its largest possible coefficient length.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

/-- The native recursive budget is monotone in the cyclic coefficient length. -/
theorem traceBudget_monotone (k : ℕ) : Monotone (fun p => traceBudget p k) := by
  intro p q hpq
  induction k with
  | zero =>
    exact Nat.add_le_add_right
      (Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left 42 hpq) hpq)
        (Nat.mul_le_mul_left 9 hpq)) 28
  | succ k ih =>
    exact Nat.add_le_add_right
      (Nat.add_le_add (Nat.mul_le_mul_left 7 ih)
        (Nat.mul_le_mul_left 692 (Nat.mul_le_mul_left (4 ^ k) hpq))) 900

end Cslib.Algorithms.WordRAM.Strassen
