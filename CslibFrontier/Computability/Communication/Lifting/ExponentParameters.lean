/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Parameters for arbitrary positive discrepancy exponents

A positive discrepancy exponent can be bounded below by `1 / (2*k)` for a positive integer
`k`. Taking a real root of the alphabet size then supplies the base used by the polynomial
parameter certificate, without restricting the alphabet size to a perfect power.
-/

public section

namespace Cslib.Communication.Lifting

/-- Choose a reciprocal-integer exponent with an explicit bound on the integer parameter. -/
theorem exists_density_exponent_le {η : ℝ} (hη : 0 < η) :
    ∃ k : ℕ, 1 ≤ k ∧ 1 ≤ 2 * (k : ℝ) * η ∧ (k : ℝ) ≤ 1 / (2 * η) + 1 := by
  let k := ⌊1 / (2 * η)⌋₊ + 1
  have hk : 1 ≤ k := Nat.le_add_left 1 _
  have hlo := Nat.lt_floor_add_one (1 / (2 * η))
  have hhi := Nat.floor_le (by positivity : (0 : ℝ) ≤ 1 / (2 * η))
  refine ⟨k, hk, ?_, ?_⟩
  · have hh : 1 / (2 * η) < (k : ℝ) := by simpa only [k, Nat.cast_add, Nat.cast_one] using hlo
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * η)).mp hh
    nlinarith
  · dsimp [k]
    push_cast
    linarith

/-- Every positive discrepancy exponent admits a reciprocal-integer lower bound. -/
theorem exists_density_exponent {η : ℝ} (hη : 0 < η) :
    ∃ k : ℕ, 1 ≤ k ∧ 1 ≤ 2 * (k : ℝ) * η := by
  obtain ⟨k, hk, hηk, _⟩ := exists_density_exponent_le hη
  exact ⟨k, hk, hηk⟩

/-- Taking a real root supplies the polynomial base for any sufficiently large alphabet.
The hypothesis on `η` transfers the original discrepancy bound to the integer-parameter one. -/
theorem density_root_parameters {M N D η : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hη : 1 ≤ 2 * (k : ℝ) * η)
    (hN : 2 ≤ N) (hM : N ^ (2048 * k ^ 2) ≤ M) (hD : D ≤ M ^ (-η)) :
    let B := M ^ (((2048 * k ^ 2 : ℕ) : ℝ)⁻¹)
    2 ≤ B ∧ N ≤ B ∧ M = B ^ (2048 * k ^ 2) ∧ D ≤ (B ^ (1024 * k))⁻¹ := by
  let K := 2048 * k ^ 2
  have hK : K ≠ 0 := by dsimp [K]; positivity
  have hNpos : 0 ≤ N := by linarith
  have hMone : 1 ≤ M := (one_le_pow₀ (by linarith : 1 ≤ N)).trans hM
  have hMpos : 0 ≤ M := by linarith
  let B := M ^ ((K : ℝ)⁻¹)
  have hNB : N ≤ B := by
    have hh := Real.rpow_le_rpow (pow_nonneg hNpos K) hM
      (by positivity : (0 : ℝ) ≤ (K : ℝ)⁻¹)
    simpa only [Real.pow_rpow_inv_natCast hNpos hK] using hh
  have hBtwo : 2 ≤ B := hN.trans hNB
  have hBpos : 0 ≤ B := by linarith
  have hMB : M = B ^ K := (Real.rpow_inv_natCast_pow hMpos hK).symm
  refine ⟨hBtwo, hNB, hMB, hD.trans ?_⟩
  change M ^ (-η) ≤ (B ^ (1024 * k))⁻¹
  conv_lhs => rw [hMB]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hBpos,
    ← Real.rpow_natCast, ← Real.rpow_neg hBpos]
  apply Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ B)
  have hmul := mul_le_mul_of_nonneg_left hη
    (by positivity : (0 : ℝ) ≤ 1024 * (k : ℝ))
  dsimp [K]
  push_cast
  nlinarith

end Cslib.Communication.Lifting
