/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DriverCorrect
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.InitializedEvaluatorCorrect
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.BalancedParameters
import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleSearchBounds

/-!
# Quantitative storage of Williams's native driver

With the initialized evaluator and balanced parameters, every candidate through the largest
guess fits a fixed multiple of the block width selected at that guess. The complete driver,
including its original-input scan, has squared storage at most a fixed-machine constant times
the largest guess multiplied by its binary length. No number of guesses multiplies the
candidate storage allowance.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.Driver

open MultiTapeTM

/-- An integer square bound states the square-root storage rate without real-valued rounding. -/
theorem space_sq_le (k s : ℕ) (Q : Type) : ∃ C, ∀ N τ : ℕ,
    (space k (InitializedEvaluator.scheduleAllowance k s Q) BalancedParameters.parameters
      N τ) ^ 2 ≤ C * (max (N + 1) τ * (max (N + 1) τ).size) := by
  obtain ⟨c, hc⟩ := ScheduleSearch.scheduleAllowance_le k s Q
  let K := 64 * (k + 2) * (18 * c + 20)
  refine ⟨4 * K ^ 2, ?_⟩
  intro N τ
  let G := max (N + 1) τ
  let B := BalancedParameters.blockWidth G
  have hG : 0 < G := by dsimp only [G]; omega
  have hNsize : N.size ≤ G.size := Nat.size_le_size (by dsimp only [G]; omega)
  have hGsize : G.size < 2 * B := BalancedParameters.size_lt_twice_blockWidth G
  have hB : 0 < B := BalancedParameters.blockWidth_pos G
  have hX : ∀ guess ≤ G,
      InitializedEvaluator.scheduleAllowance k s Q N
          (BalancedParameters.parameters.blockWidth guess)
          (BalancedParameters.parameters.horizon guess) +
        (BalancedParameters.parameters.blockWidth guess).size +
        BalancedParameters.parameters.horizon guess ≤
      c * (15 * B + N.size + 1) + 15 * B := by
    intro guess hguess
    change InitializedEvaluator.scheduleAllowance k s Q N (BalancedParameters.blockWidth guess)
        (BalancedParameters.horizon guess) + (BalancedParameters.blockWidth guess).size +
        BalancedParameters.horizon guess ≤ _
    have hcost := hc N (BalancedParameters.blockWidth guess) (BalancedParameters.horizon guess)
      (BalancedParameters.blockWidth_pos guess)
    have hstorage := BalancedParameters.storage_le guess
    have hmono : BalancedParameters.blockWidth guess ≤ B :=
      BalancedParameters.blockWidth_mono hguess
    have hbs : (BalancedParameters.blockWidth guess).size ≤
        BalancedParameters.blockWidth guess := by
      simpa only [length_encNat_eq_size] using
        length_encNat_le_self (BalancedParameters.blockWidth guess)
    have hhz : BalancedParameters.horizon guess ≤ BalancedParameters.horizon guess *
        ((BalancedParameters.blockWidth guess).size + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have hterm : BalancedParameters.blockWidth guess + BalancedParameters.horizon guess *
        ((BalancedParameters.blockWidth guess).size + 1) + N.size + 1 ≤ 15 * B + N.size + 1 := by
      omega
    have hmul := Nat.mul_le_mul_left c hterm
    omega
  have hinner : c * (15 * B + N.size + 1) + 15 * B + N.size + G.size + 1 ≤ (18 * c + 20) * B := by
    have hmul := Nat.mul_le_mul_left c (show 15 * B + N.size + 1 ≤ 18 * B by omega)
    nlinarith
  have hscalar : space k (InitializedEvaluator.scheduleAllowance k s Q)
      BalancedParameters.parameters N τ ≤ K * B :=
    calc
      _ ≤ 64 * (k + 2) * (c * (15 * B + N.size + 1) + 15 * B + N.size + G.size + 1) :=
        space_le_of_le k _ _ N τ _ hX
      _ ≤ 64 * (k + 2) * ((18 * c + 20) * B) := Nat.mul_le_mul_left _ hinner
      _ = K * B := by dsimp only [K]; ring
  have hbalanced : B ^ 2 ≤ 4 * (G * G.size) := BalancedParameters.blockWidth_sq_le hG
  calc
    _ ≤ (K * B) ^ 2 := Nat.pow_le_pow_left hscalar 2
    _ = K ^ 2 * B ^ 2 := by ring
    _ ≤ K ^ 2 * (4 * (G * G.size)) := Nat.mul_le_mul_left _ hbalanced
    _ = 4 * K ^ 2 * (G * G.size) := by ring

end Turing.MultiTapePTM.BlockComputation.Driver
