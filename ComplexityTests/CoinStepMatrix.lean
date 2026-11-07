/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Foundations.LinearAlgebra.Matrix.CoinStep

/-!
# Tests for transition matrices of coin-driven maps
-/

namespace ComplexityTests.CoinStepMatrix

open Matrix

/-- From `0` the coin moves to `1` or `2`; the states `1` and `2` are fixed. -/
private def next : Fin 3 → Bool → Fin 3
  | 0, b => if b then 1 else 2
  | x, _ => x

private theorem next_mem (x : Fin 3) (_ : x ∈ (Finset.univ : Finset (Fin 3))) (b : Bool) :
    next x b ∈ (Finset.univ : Finset (Fin 3)) :=
  Finset.mem_univ _

-- Half of the `8` coin strings of length three end in `1` from `0`: those starting with `true`.
example : (coinStepMatrix next Finset.univ ^ 3 *ᵥ
    fun y : (Finset.univ : Finset (Fin 3)) => if (y : Fin 3) = 1 then (1 : ℕ) else 0)
      ⟨0, Finset.mem_univ _⟩ = 4 := by
  rw [coinStepMatrix_pow_mulVec next_mem (fun y => if y = 1 then 1 else 0)]
  decide

/-- Only the state `0` is live, so the live matrix squares to zero. -/
private theorem live_sq : (liveCoinStepMatrix next Finset.univ (· = 0) : Matrix _ _ ℚ) ^ 2 = 0 :=
  liveCoinStepMatrix_pow_eq_zero next_mem fun x _ w => by
    refine ⟨1, ?_⟩
    fin_cases x <;> cases h : w 0 <;> simp [next, List.ofFn_succ, h]

-- The walk from `0` stops after one step: one live coin string of length one ends in `1`, none
-- of length two, since the live condition fails at the second state.
example : (liveCoinStepMatrix next Finset.univ (· = 0) ^ 1 *ᵥ
    fun y : (Finset.univ : Finset (Fin 3)) => if (y : Fin 3) = 1 then (1 : ℕ) else 0)
      ⟨0, Finset.mem_univ _⟩ = 1 := by
  rw [liveCoinStepMatrix_pow_mulVec next_mem (fun y => if y = 1 then 1 else 0)]
  decide

example : (liveCoinStepMatrix next Finset.univ (· = 0) ^ 2 *ᵥ
    fun y : (Finset.univ : Finset (Fin 3)) => if (y : Fin 3) = 1 then (1 : ℕ) else 0)
      ⟨0, Finset.mem_univ _⟩ = 0 := by
  rw [liveCoinStepMatrix_pow_mulVec next_mem (fun y => if y = 1 then 1 else 0)]
  decide

-- With `S ^ 2 = 0`, the inverse of `1 - S` is `1 + S`.
example : (1 - (liveCoinStepMatrix next Finset.univ (· = 0) : Matrix _ _ ℚ))⁻¹ =
    1 + liveCoinStepMatrix next Finset.univ (· = 0) := by
  rw [inv_one_sub_eq_sum_pow live_sq, Finset.sum_range_succ, Finset.sum_range_one, pow_zero,
    pow_one]

end ComplexityTests.CoinStepMatrix
