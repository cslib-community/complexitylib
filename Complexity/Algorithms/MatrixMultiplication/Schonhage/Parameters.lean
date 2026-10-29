/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Sparse
public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Tiling
public import Complexity.Foundations.Data.Nat.Choose.Real
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Parameters of finite thin multiplication

## Main results

* `K_mul_N0_le_D_pow`: bound `K L m * N0 L m` by `D m ^ 18` at `L = 19 * m`.
* `encoding_size_le`: the shared encoding length bound.

## References

Adapted selectively from [AlmanWilliams2026, Section 2] and
[Anthropic's pinned formal source](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2).
Source pin: `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. These are finite mathematical
counts and identities; they give no native program or instruction-cost certificate.
-/

@[expose] public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The binomial count at `L = 19 * m` is at most `(19 * Real.exp 1) ^ m`. This uses
`Nat.choose_le_exp_mul_div_pow` and includes `m = 0`, when both sides are one. -/
theorem K_le_pow (m : ℕ) : (K (19 * m) m : ℝ) ≤ (19 * Real.exp 1) ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [K]
  · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hbase : Real.exp 1 * ((19 * m : ℕ) : ℝ) / (m : ℝ) = 19 * Real.exp 1 := by
      push_cast
      field_simp
    exact hbase ▸ Nat.choose_le_exp_mul_div_pow (19 * m) m

/-- The real constant `19 * exp 1 * 3 ^ 18` is strictly less than `4 ^ 18`. -/
theorem nineteen_mul_exp_mul_three_pow_lt : 19 * Real.exp 1 * (3 : ℝ) ^ 18 < (4 : ℝ) ^ 18 := by
  calc 19 * Real.exp 1 * (3 : ℝ) ^ 18 < 19 * 2.7182818286 * (3 : ℝ) ^ 18 := by
        gcongr
        exact Real.exp_one_lt_d9
    _ < (4 : ℝ) ^ 18 := by norm_num

/-- `4^{18m} = D^18`. -/
private theorem four_pow_eq (m : ℕ) : ((4 : ℝ) ^ 18) ^ m = (D m : ℝ) ^ 18 := by
  rw [D, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ← pow_mul, mul_comm]

/-- At `L = 19 * m`, the product `K L m * N0 L m` is at most `D m ^ 18`. -/
theorem K_mul_N0_le_D_pow (m : ℕ) : K (19 * m) m * N0 (19 * m) m ≤ D m ^ 18 := by
  have hK := K_le_pow m
  have key : (K (19 * m) m : ℝ) * (N0 (19 * m) m : ℝ) ≤ (D m : ℝ) ^ 18 := by
    calc (K (19 * m) m : ℝ) * (N0 (19 * m) m : ℝ)
        ≤ (19 * Real.exp 1) ^ m * ((3 : ℝ) ^ 18) ^ m := by
          rw [N0_nineteen_mul m]
          push_cast
          rw [pow_mul]
          exact mul_le_mul_of_nonneg_right hK (by positivity)
      _ = (19 * Real.exp 1 * (3 : ℝ) ^ 18) ^ m := (mul_pow _ _ _).symm
      _ ≤ ((4 : ℝ) ^ 18) ^ m :=
          pow_le_pow_left₀ (by positivity) nineteen_mul_exp_mul_three_pow_lt.le m
      _ = (D m : ℝ) ^ 18 := four_pow_eq m
  exact_mod_cast key

/-- The size condition `D m ^ 18 ≤ N` bounds `K (19 * m) m * N0 (19 * m) m` by `N`. -/
theorem K_mul_N0_le (m N : ℕ) (hN : D m ^ 18 ≤ N) : K (19 * m) m * N0 (19 * m) m ≤ N :=
  (K_mul_N0_le_D_pow m).trans hN

/-- The size condition `D m ^ 18 ≤ N` bounds the band dimension at `L = 19 * m` by `N`. -/
theorem K0_mul_N0_le (m N : ℕ) (hN : D m ^ 18 ≤ N) : K0 (19 * m) m * N0 (19 * m) m ≤ N :=
  (Nat.mul_le_mul_right _ (Nat.sqrt_le_self _)).trans (K_mul_N0_le m N hN)

/-- Under `D m ^ 18 ≤ N`, padding to complete bands at `L = 19 * m` gives a dimension at most
`2 * N`. -/
theorem padN_le_two_mul_of_D_pow_le (m N : ℕ) (hN : D m ^ 18 ≤ N) : padN (19 * m) m N ≤ 2 * N :=
  padN_le_two_mul (19 * m) m N (K0_mul_N0_le m N hN)

/-- The real constant `10 ^ 19 * 2 ^ (1 / 9) / 3 ^ 18` is strictly less than `4 ^ 18`. -/
theorem ten_pow_mul_two_rpow_div_three_pow_lt :
    (10 : ℝ) ^ 19 * (2 : ℝ) ^ (1 / 9 : ℝ) / (3 : ℝ) ^ 18 < (4 : ℝ) ^ 18 := by
  have htwo : (2 : ℝ) ^ (1 / 9 : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (1 / 9 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  rw [div_lt_iff₀ (by positivity)]
  calc (10 : ℝ) ^ 19 * (2 : ℝ) ^ (1 / 9 : ℝ) ≤ (10 : ℝ) ^ 19 * 2 :=
        mul_le_mul_of_nonneg_left htwo (by positivity)
    _ < (4 : ℝ) ^ 18 * (3 : ℝ) ^ 18 := by norm_num

/-- At `L = 19 * m`, the real quotient `10 ^ L * 2 ^ (m / 9) / N0 L m` is at most `D m ^ 18`. -/
theorem ten_pow_div_N0_le (m : ℕ) :
    (10 : ℝ) ^ (19 * m) * (2 : ℝ) ^ ((m : ℝ) / 9) / (N0 (19 * m) m : ℝ) ≤ (D m : ℝ) ^ 18 := by
  have hroot : (2 : ℝ) ^ ((m : ℝ) / 9) = ((2 : ℝ) ^ (1 / 9 : ℝ)) ^ m := by
    rw [← Real.rpow_natCast _ m, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  calc (10 : ℝ) ^ (19 * m) * (2 : ℝ) ^ ((m : ℝ) / 9) / (N0 (19 * m) m : ℝ)
      = ((10 : ℝ) ^ 19 * (2 : ℝ) ^ (1 / 9 : ℝ) / (3 : ℝ) ^ 18) ^ m := by
        rw [N0_nineteen_mul m, hroot]
        push_cast
        rw [pow_mul, pow_mul, div_pow, mul_pow]
    _ ≤ ((4 : ℝ) ^ 18) ^ m := pow_le_pow_left₀ (by positivity)
        ten_pow_mul_two_rpow_div_three_pow_lt.le m
    _ = (D m : ℝ) ^ 18 := four_pow_eq m

/-- For `L = 19 * m` and `D m ^ 18 ≤ N`, the encoding index count `10 ^ L` is at most `2 ^ (-m
/ 9) * N * N0 L m`, as a real inequality (cf. [AlmanWilliams2026, equation (6)]). -/
theorem encoding_size_le (m N : ℕ) (hN : D m ^ 18 ≤ N) :
    (10 : ℝ) ^ (19 * m) ≤ (2 : ℝ) ^ (-(m : ℝ) / 9) * (N : ℝ) * (N0 (19 * m) m : ℝ) := by
  have hN0 : (0 : ℝ) < (N0 (19 * m) m : ℝ) := by exact_mod_cast N0_pos _ _
  have hN' : (D m : ℝ) ^ 18 ≤ (N : ℝ) := by exact_mod_cast hN
  have h := (ten_pow_div_N0_le m).trans hN'
  rw [div_le_iff₀ hN0] at h
  calc (10 : ℝ) ^ (19 * m)
      = (10 : ℝ) ^ (19 * m) * (2 : ℝ) ^ ((m : ℝ) / 9) * saving m := by
        rw [mul_assoc, mul_comm _ (saving m), saving_mul_two_rpow, mul_one]
    _ ≤ (N : ℝ) * (N0 (19 * m) m : ℝ) * saving m :=
        mul_le_mul_of_nonneg_right h (saving_pos m).le
    _ = saving m * (N : ℝ) * (N0 (19 * m) m : ℝ) := by ring

end Cslib.Algorithms.MatrixMultiplication.Schonhage
