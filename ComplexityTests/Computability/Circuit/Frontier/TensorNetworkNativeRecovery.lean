/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Frontier.TensorNetwork.NativeRecovery

/-! # Native tapered recovery on small instances

Computations over `(ℤ / 2 ^ N)[U] / (U ^ 2 + U + 1)` (`fl = [1, 1]`) with `L = 2` slots
(`a = 1`), and the correctness statements of the components. -/

namespace ComplexityTests.TensorNetworkNativeRecovery

open Cslib.GaloisRingArith Cslib.Circuits.Frontier Cslib.Circuits.Frontier.NativeRecovery

-- `2 - 5 = -3 = 5` modulo `8`.
example : diffConst 3 [1, 1] 2 5 = [5, 0] := by decide

-- `α / (t - q) = 4 / 2 = 2`, and `4 / (0 - 3) = -4 / 3 = 4` modulo `8` (since `3⁻¹ = 3`).
example : slopeConst 3 [1, 1] 1 3 1 = [2, 0] := by decide
example : slopeConst 3 [1, 1] 1 0 3 = [4, 0] := by decide

-- `(1 + z) ^ 2 = 1 + 2 z + z ^ 2`, truncated below `z ^ 2`.
example : tmul 3 [1, 1] 2 [[1, 0], [1, 0]] [[1, 0], [1, 0]] = [[1, 0], [2, 0]] := by decide

-- Cancelling `2`: `6 + 2 U = 2 (3 + U)`.
example : shiftDown 1 [6, 2] = [3, 1] := by decide

-- The capped `2`-adic valuation: `v₂ 12 = 2`, `v₂ 5 = 0`, and `0` at `0`.
example : (twoVal 4 12, twoVal 4 5, twoVal 4 0) = (2, 0, 0) := by decide

-- With `u = h = 1`, the odd nodes `t = ±1` have multiplicity `1` and `t = -2` has `0`.
example : (mult 1 1 1 1, mult 1 1 1 3, mult 1 1 1 0) = (1, 1, 0) := by decide

/-- **Recovery of `F(0)` for `F(T) = T + 5`.** Here `q_{±1} = 1`, so recovery reads the values
`F(-1) = 4` and `F(1) = 6` at the single point `ζ = 0`, and returns
`E_{-1}(0) F(-1) + E_1(0) F(1) = (4 + 6) / 2 = 5` modulo `8`, computing modulo `2 ^ (3 + 2)`. -/
example : recover 3 2 [1, 1] 1 1 1 [[0, 0]] [[], [[4, 0]], [], [[6, 0]]] = [5, 0] := by decide

/-- The same recovery with `Δ = (a + 1) ∑_t q_t = 4`, the shift that `val_recover` assumes. -/
example : recover 3 4 [1, 1] 1 1 1 [[0, 0]] [[], [[4, 0]], [], [[6, 0]]] = [5, 0] := by decide

/-- The reciprocal of `E_t(t + α z)` is correct, for every ring homomorphism from `ℤ_(2)`. -/
example (hirr : Irreducible ((monicOf [1, 1]).map (Int.castRingHom (ZMod 2))))
    (ρ : Valuation.integer (Rat.padicValuation 2) →+* Ring 5 [1, 1]) {i : ℕ} (hi : i < 2) :
    val 5 [1, 1] ((recip 5 [1, 1] 1 1 1 1 2).getD i []) =
      ρ (PowerSeries.coeff i (recipSeries 1 1 1 1)) :=
  val_recip hirr ρ (by norm_num) hi

/-- The multipliers are `2 ^ Δ E_t(0) (-t / α) ^ j`. -/
example : ((gamma 1 1 1 2 1 0 : Valuation.integer (Rat.padicValuation 2)) : ℚ) = 2 ^ 2 *
    (Polynomial.hermiteBasis (recoveryNodes 1) (fun q : ℤ => (q : ℚ)) (taperMult 1 1)
      (node 1 1)).eval 0 * (-(node 1 1 : ℚ) / 2 ^ (1 + 1)) ^ 0 :=
  coe_gamma (by norm_num) (by decide)

/-- The capped `2`-adic valuation is polynomial-time in unary. -/
example : Turing.MultiTapeTM.ComputableInPolyTime (fun n : ℕ => twoVal n n)
    Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary :=
  computableInPolyTime_twoVal Turing.MultiTapeTM.ComputableInPolyTime.id'
    Turing.MultiTapeTM.ComputableInPolyTime.id'

end ComplexityTests.TensorNetworkNativeRecovery
