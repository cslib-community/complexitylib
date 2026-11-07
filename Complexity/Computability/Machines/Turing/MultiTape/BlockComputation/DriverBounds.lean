/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.DriverCorrect
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleSearchBounds
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts

/-!
# Quantitative storage of the complete native driver

The maximum over increasing guesses is bounded by the selected block width at the largest
guess. The complete driver, including its original-input scan, has squared storage at most a
fixed-machine constant times the largest guess multiplied by its binary length. No number of
guesses multiplies the candidate storage allowance.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.OuterSearch

open MultiTapeTM

/-- Taking a finite maximum of candidate allowances preserves the balanced storage shape. -/
theorem space_le (k s : ℕ) (Q : Type) : ∃ C, ∀ N A : ℕ,
    space k s Q N A ≤ C * (BalancedParameters.blockWidth A + N.size + 1) := by
  obtain ⟨c, hc⟩ := ScheduleSearch.space_le k s Q
  refine ⟨15 * c + 64, ?_⟩
  intro N A
  have hsup : candidateSpace k s Q N A ≤
      c * (15 * BalancedParameters.blockWidth A + N.size + 1) := by
    unfold candidateSpace
    apply Finset.sup_le
    intro guess hguess
    have hguessA : guess ≤ A := by
      have h := Finset.mem_range.mp hguess
      omega
    have hcost := hc N (BalancedParameters.blockWidth guess)
      (BalancedParameters.horizon guess) (BalancedParameters.blockWidth_pos guess)
    have hstorage := BalancedParameters.storage_le guess
    have hmono := BalancedParameters.blockWidth_mono hguessA
    have hterm : BalancedParameters.blockWidth guess + BalancedParameters.horizon guess *
        ((BalancedParameters.blockWidth guess).size + 1) + N.size + 1 ≤
        15 * BalancedParameters.blockWidth A + N.size + 1 := by nlinarith
    exact hcost.trans (Nat.mul_le_mul_left c hterm)
  have hsize := BalancedParameters.size_lt_twice_blockWidth A
  simp only [space, callerSpace, length_encNat_eq_size]
  nlinarith

end Turing.MultiTapePTM.BlockComputation.OuterSearch

namespace Turing.MultiTapePTM.BlockComputation.Driver

/-- The input scan and all increasing-guess candidates use one balanced-width allowance. -/
theorem space_le (k s : ℕ) (Q : Type) : ∃ C, ∀ N τ : ℕ,
    space k s Q N τ ≤ C *
      (BalancedParameters.blockWidth (max (N + 1) τ) + N.size + 1) := by
  obtain ⟨c, hc⟩ := OuterSearch.space_le k s Q
  refine ⟨c + 8, ?_⟩
  intro N τ
  have houter := hc N (max (N + 1) τ)
  have hlog : Nat.log2 N ≤ N.size := by
    by_cases hz : N = 0
    · subst N
      decide
    · exact ((Nat.log2_lt hz).mpr (Nat.lt_size_self N)).le
  dsimp only [space]
  nlinarith

/-- An integer square bound states the square-root storage rate without real-valued rounding. -/
theorem space_sq_le (k s : ℕ) (Q : Type) : ∃ C, ∀ N τ : ℕ,
    (space k s Q N τ) ^ 2 ≤
      C * (max (N + 1) τ * (max (N + 1) τ).size) := by
  obtain ⟨c, hc⟩ := space_le k s Q
  refine ⟨64 * c ^ 2, ?_⟩
  intro N τ
  let A := max (N + 1) τ
  have hA : 0 < A := by dsimp only [A]; omega
  have hN : N ≤ A := by dsimp only [A]; omega
  have hNsize := Nat.size_le_size hN
  have hAsize := BalancedParameters.size_lt_twice_blockWidth A
  have hblock := BalancedParameters.blockWidth_pos A
  have hshape := hc N τ
  have hscalar : space k s Q N τ ≤ 4 * c * BalancedParameters.blockWidth A := by
    change space k s Q N τ ≤ c *
      (BalancedParameters.blockWidth A + N.size + 1) at hshape
    have hterm : BalancedParameters.blockWidth A + N.size + 1 ≤
        4 * BalancedParameters.blockWidth A := by omega
    calc
      space k s Q N τ ≤ c * (BalancedParameters.blockWidth A + N.size + 1) := hshape
      _ ≤ c * (4 * BalancedParameters.blockWidth A) := Nat.mul_le_mul_left c hterm
      _ = 4 * c * BalancedParameters.blockWidth A := by ring
  have hsquare := Nat.mul_le_mul hscalar hscalar
  have hbalanced := BalancedParameters.blockWidth_sq_le hA
  have hscaled := Nat.mul_le_mul_left (16 * c ^ 2) hbalanced
  change (space k s Q N τ) ^ 2 ≤ 64 * c ^ 2 * (A * A.size)
  nlinarith

end Turing.MultiTapePTM.BlockComputation.Driver
