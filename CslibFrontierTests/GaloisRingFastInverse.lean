/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.PolyTime.GaloisRingArithmetic.FastInverse

/-! Accelerated inversion: actual coefficient examples, nonunits, and precision boundaries. -/

namespace CslibFrontierTests.GaloisRingFastInverse

open Cslib.GaloisRingArith

/-- Eight-bit precision requires three Newton rounds, and both implementations agree. -/
example : Nat.clog 2 8 = 3 ∧ fastInv 8 [1, 1] [3, 5] = inv 8 [1, 1] [3, 5] := by decide

/-- The accelerated result actually inverts this unit. -/
example : mul 8 [1, 1] [3, 5] (fastInv 8 [1, 1] [3, 5]) = [1, 0] := by decide

/-- The seed condition cannot be dropped for a nonunit. -/
example : mul 3 [1, 1] [2, 0] (fastInv 3 [1, 1] [2, 0]) ≠ [1, 0] := by decide

/-- At precision one, the seed already suffices and there are no Newton rounds. -/
example : fastInv 1 [1, 1] [0, 1] = seed 1 [1, 1] [0, 1] := rfl

/-- The theorem includes zero precision and requires no nontrivial-ring assumption. -/
example (fl x : List ℕ) {w : Ring 0 fl}
    (h : val 0 fl x * val 0 fl x ^ (2 ^ fl.length - 2) = 1 + 2 * w) :
    val 0 fl x * val 0 fl (fastInv 0 fl x) = 1 := val_mul_fastInv x h

end CslibFrontierTests.GaloisRingFastInverse
