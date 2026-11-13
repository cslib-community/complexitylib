/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.PACLearning.Compression.Shattering
import CslibFrontier.MachineLearning.PACLearning.Compression.Order

/-! Checks for the converse direction: compression schemes bound the VC dimension. The lower sets
of a linear order have a scheme of size `1`, so they shatter no three points (`2 ^ 3 > 7`); the
intervals have a scheme of size `2`, so they have finite VC dimension. -/

namespace CslibFrontierTests.CompressionShattering

open Cslib.MachineLearning.PACLearning

/-- `2 ^ n > 2 n + 1` for `n ≥ 3`. -/
theorem two_mul_add_one_lt_two_pow : ∀ n, 3 ≤ n → 2 * n + 1 < 2 ^ n
  | 3, _ => by norm_num
  | n + 4, _ => by
    have := two_mul_add_one_lt_two_pow (n + 3) (by omega)
    rw [pow_succ]
    omega

/-- The lower sets of `ℕ` shatter at most two points, from their scheme of size `1`. -/
example (W : Finset ℕ) (hW : SetShatters (lowerSetClass ℕ) ↑W) : W.card ≤ 2 := by
  have h := lowerSetScheme.two_pow_card_le_of_setShatters hW
  rw [pow_one] at h
  by_contra hlt
  exact (two_mul_add_one_lt_two_pow _ (by omega)).not_ge h

/-- The intervals of `ℝ` have finite VC dimension, from their scheme of size `2`. -/
example : HasFiniteVCDim (ordConnectedClass ℝ) :=
  ordConnectedScheme.hasFiniteVCDim

end CslibFrontierTests.CompressionShattering
