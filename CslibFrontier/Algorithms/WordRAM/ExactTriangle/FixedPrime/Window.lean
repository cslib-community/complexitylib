/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Width

/-!
# Monotonicity of the per-record workspace reservation

`window_mono` bounds `CallableProduct.windowSize n Q` for `Q ≤ n * n` by the uniform `n * n`
reservation used in the one-slot fixed-prime traversal, without importing the execution proof.
It concerns a reserved address envelope, not a clearing loop.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime

open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- The existing callable scratch window grows monotonically with the query occurrence count. -/
theorem window_mono {n Q : ℕ} (hQ : Q ≤ n * n) :
    CallableProduct.windowSize n Q ≤ CallableProduct.windowSize n (n * n) := by
  unfold CallableProduct.windowSize CallableProduct.sourceWidth
  exact Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_left 128 (Nat.clog_mono_right 2 (by omega)))

end Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime
