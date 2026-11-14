/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Algorithms.Quantum.PeriodFinding
import CslibFrontier.Foundations.Data.Nat.Totient
import CslibFrontier.Foundations.Data.Rat.Approximation

set_option linter.privateModule false

/-! Exact quantum period finding: instances and failures of the exact-period promise, the
quantum Fourier transform for `N = 2` (the Hadamard matrix), concrete outcome distributions and
recovery probabilities, and edge cases of the totient bound. -/

namespace CslibFrontierTests.QuantumPeriodFinding

open Cslib Cslib.Quantum Finset ZMod

/-! ### The promise -/

/-- Reduction modulo `3` on `ZMod 6`, which has exact period `3`. -/
def mod3 (x : ZMod 6) : ZMod 3 := (x.val : ZMod 3)

theorem hasExactPeriod_mod3 : HasExactPeriod mod3 3 :=
  ⟨by decide, fun x x' => by
    unfold mod3
    exact ZMod.natCast_eq_natCast_iff _ _ _⟩

-- The same function does not have exact period `2` (it is not even periodic with period `2`), nor
-- `6` (it is not injective on `ZMod 6`).
example : ¬HasExactPeriod mod3 2 := fun h => by
  have := (h.eq_iff 0 2).mpr (by decide)
  revert this
  decide

example : ¬HasExactPeriod mod3 6 := fun h => by
  have := (h.eq_iff 0 3).mp (by decide)
  revert this
  decide

-- A constant function has exact period `1`, and not period `2`.
example : HasExactPeriod (fun _ : ZMod 4 => (0 : ZMod 2)) 1 :=
  ⟨one_dvd _, fun _ _ => by simp [Nat.modEq_one]⟩

example : ¬HasExactPeriod (fun _ : ZMod 4 => (0 : ZMod 2)) 2 := fun h => by
  have := (h.eq_iff 0 1).mp rfl
  revert this
  decide

-- An injective function has exact period `N`.
example : HasExactPeriod (fun x : ZMod 4 => x) 4 :=
  ⟨dvd_rfl, fun x x' => by
    rw [Nat.ModEq, Nat.mod_eq_of_lt (ZMod.val_lt x), Nat.mod_eq_of_lt (ZMod.val_lt x')]
    exact ⟨fun h => h ▸ rfl, fun h => ZMod.val_injective _ h⟩⟩

-- Order finding: `2` has order `4` in `(ZMod 5)ˣ`, so `a ↦ 2 ^ a` on `ZMod 8` has exact period `4`.
/-- The unit `2` of `ZMod 5`. -/
def two5 : (ZMod 5)ˣ := ⟨2, 3, by decide, by decide⟩

theorem orderOf_two5 : orderOf two5 = 4 :=
  (orderOf_eq_iff (by decide)).mpr ⟨by decide, by decide⟩

theorem hasExactPeriod_two5 : HasExactPeriod (fun a : ZMod 8 => two5 ^ a.val) 4 :=
  orderOf_two5 ▸ hasExactPeriod_pow (orderOf_two5 ▸ by decide)

/-! ### The quantum Fourier transform -/

-- For `N = 2` the Fourier transform is the Hadamard matrix `Gate.hadamardMatrix`, with `ZMod 2`
-- indexed by `Bool` via `x ↦ (x = 1)`.
example : (qft 2 : Matrix (ZMod 2) (ZMod 2) ℂ) =
    Gate.hadamardMatrix.submatrix (fun x : ZMod 2 => decide (x = 1)) fun x => decide (x = 1) := by
  have h11 : (2 * Real.pi * Complex.I * ((1 : ZMod 2).val : ℂ) * ((1 : ZMod 2).val : ℂ) /
      ((2 : ℕ) : ℂ)) = Real.pi * Complex.I := by
    simp only [ZMod.val_one, Nat.cast_one, mul_one, Nat.cast_ofNat]
    field_simp
  have hcases : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
  ext i j
  rw [qft_apply_eq_exp, Matrix.submatrix_apply]
  rcases hcases i with rfl | rfl <;> rcases hcases j with rfl | rfl
  · simp [Gate.hadamardMatrix]
  · simp [Gate.hadamardMatrix]
  · simp [Gate.hadamardMatrix]
  · rw [h11, Complex.exp_pi_mul_I]
    simp [Gate.hadamardMatrix, div_eq_mul_inv]

-- The first row of the Fourier transform is constant: it maps `|0⟩` to the uniform superposition.
example (k : ZMod 5) :
    (qft 5 : Matrix (ZMod 5) (ZMod 5) ℂ) 0 k = (((Real.sqrt 5)⁻¹ : ℝ) : ℂ) := by
  rw [qft_apply, zero_mul, AddChar.map_zero_eq_one, mul_one]
  norm_num

/-! ### Outcome distributions -/

-- Period `3` on `ZMod 6`: the outcomes `0, 2, 4` each have probability `1 / 3`, and `1` never
-- occurs.
example : periodFindingOutcome mod3 2 = 3⁻¹ := by
  rw [hasExactPeriod_mod3.periodFindingOutcome_apply, ite_eq_left (by decide)]
  norm_num

example : periodFindingOutcome mod3 1 = 0 := by
  rw [hasExactPeriod_mod3.periodFindingOutcome_apply, ite_eq_right (by decide)]

-- Order finding with `r = 4` on `ZMod 8`: the outcome `6` has probability `1 / 4`, and `3` never
-- occurs.
example : periodFindingOutcome (fun a : ZMod 8 => two5 ^ a.val) 6 = 4⁻¹ := by
  rw [hasExactPeriod_two5.periodFindingOutcome_apply, ite_eq_left (by decide)]
  norm_num

example : periodFindingOutcome (fun a : ZMod 8 => two5 ^ a.val) 3 = 0 := by
  rw [hasExactPeriod_two5.periodFindingOutcome_apply, ite_eq_right (by decide)]

-- The standard oracle prepares the state that the analysis starts from.
example : unitaryEquiv (addOracle mod3) (unitaryEquiv (onFirst (qft 6)) (ket (0, 0))) =
    oracleState mod3 :=
  unitaryEquiv_addOracle_qft_ket_zero mod3

/-! ### Classical recovery -/

-- With `r = 3`, the recovery `N / gcd(N, y) = 3` succeeds on `y ∈ {2, 4}`, probability
-- `φ(3) / 3 = 2 / 3`; with `r = 4`, it succeeds on `y ∈ {2, 6}`, probability `φ(4) / 4 = 1 / 2`.
example : (periodFindingOutcome mod3).toOuterMeasure {y | 6 / Nat.gcd 6 y.val = 3} = 2 * 3⁻¹ := by
  rw [hasExactPeriod_mod3.periodFindingOutcome_recover, Nat.totient_prime Nat.prime_three]
  norm_num

example : (periodFindingOutcome (fun a : ZMod 8 => two5 ^ a.val)).toOuterMeasure
    {y | 8 / Nat.gcd 8 y.val = 4} = 2 * 4⁻¹ := by
  rw [hasExactPeriod_two5.periodFindingOutcome_recover]
  have : Nat.totient 4 = 2 := by decide
  rw [this]
  norm_num

/-! ### The totient bound -/

-- The bound `n ≤ φ n (log₂ n + 1)` is tight at `n = 2`.
example : 2 = Nat.totient 2 * (Nat.log 2 2 + 1) := by
  rw [Nat.totient_two, Nat.log_eq_one_iff'.mpr ⟨le_rfl, by norm_num⟩]
example : 30 ≤ Nat.totient 30 * (Nat.log 2 30 + 1) := Nat.le_totient_mul_log_add_one 30

/-! ### Uniqueness of rational approximation (Arora–Barak Chapter 20, Exercises 7 and 11) -/

-- Two distinct fractions `1 / 3` and `2 / 5` with denominators at most `5` are separated by at
-- least `1 / 25` (in fact `1 / 15`).
example : (1 : ℝ) / (5 : ℝ) ^ 2 < |((1 / 3 : ℚ) : ℝ) - ((2 / 5 : ℚ) : ℝ)| :=
  Rat.one_div_sq_lt_abs_sub_of_den_le_of_den_lt (N := 5) (q := 2 / 5) (r := 1 / 3)
    (by norm_num) (by norm_num) (by norm_num) |> fun h => by rwa [abs_sub_comm] at h

-- Exercise 20.7: any rational `q` with `q.den ≤ 6` within `1 / 72` of `2 / 5` equals `2 / 5`.
example {q : ℚ} (hq : q.den ≤ 6) (h : |(2 / 5 : ℝ) - q| ≤ 1 / (2 * (6 : ℝ) ^ 2)) :
    q = 2 / 5 :=
  Rat.eq_of_den_lt_of_abs_sub_le (α := 2 / 5) (N := 6) hq (by norm_num) h (by norm_num)

-- Exercise 20.11 (uniqueness): a coprime pair `(j, r)` with `0 < r ≤ 5` whose quotient lies within
-- `< 1 / 50` of `3 / 5` is `(3, 5)`.
example {j r : ℕ} (hr0 : 0 < r) (hr : r ≤ 5) (hcop : Nat.Coprime j r)
    (h : |(3 / 5 : ℝ) - (j : ℝ) / r| < 1 / (2 * (5 : ℝ) ^ 2)) : j = 3 ∧ r = 5 :=
  Rat.eq_of_coprime_of_abs_sub_div_lt (α := 3 / 5) hr0 hr (by decide) (by decide) hcop (by decide) h
    (by norm_num)

end CslibFrontierTests.QuantumPeriodFinding
