/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Nat/Choose/Vandermonde.lean`)

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Complexity.Foundations.Data.Nat.Factorial
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# Products and sums of binomial coefficients

Choosing `D x` of `N x` elements in each of several disjoint blocks chooses `Σ D x` of the
`Σ N x` elements, so a product of binomial coefficients is at most the binomial coefficient of the
sums (`Nat.prod_choose_le_choose_sum`, from Vandermonde's identity). Fewer selected elements are
absorbed by stars and bars: `C(N, D) ≤ C(N + K, K)` for `D ≤ K`
(`Nat.choose_le_add_choose_of_le`). Quantitatively, `C(N + K, K) ≤ (3 R) ^ K` when `N + K ≤ R K`
(`Nat.add_choose_le_three_mul_pow`), from `K ^ K ≤ 3 ^ K K!`; this is the bound
`C(N + K, K) ≤ (e (N + K) / K) ^ K` with `e` replaced by `3`.

## Main results

* `Nat.prod_choose_le_choose_sum`: Vandermonde's inequality.
* `Nat.choose_le_choose_add_add`, `Nat.choose_le_add_choose_of_le`: monotonicity.
* `Nat.add_choose_le_three_mul_pow`: `C(N + K, K) ≤ (3 R) ^ K` when `N + K ≤ R K`.
-/

public section

namespace Nat

open Finset

/-- `C(n, k) ≤ C(n + j, k + j)`. -/
theorem choose_le_choose_add_add (n k j : ℕ) : n.choose k ≤ (n + j).choose (k + j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    refine ih.trans ?_
    rw [← Nat.add_assoc, ← Nat.add_assoc, Nat.choose_succ_succ]
    omega

/-- **Fewer selected elements**: `C(N, D) ≤ C(N + K, K)` for `D ≤ K`. -/
theorem choose_le_add_choose_of_le {N D K : ℕ} (hD : D ≤ K) : N.choose D ≤ (N + K).choose K := by
  calc N.choose D ≤ (N + (K - D)).choose (D + (K - D)) := choose_le_choose_add_add _ _ _
    _ = (N + (K - D)).choose K := by rw [Nat.add_sub_cancel' hD]
    _ ≤ (N + K).choose K := Nat.choose_le_choose _ (by omega)

/-- **Vandermonde's inequality**: a product of binomial coefficients is at most the binomial
coefficient of the sums. -/
theorem prod_choose_le_choose_sum {ι : Type*} (s : Finset ι) (N D : ι → ℕ) :
    ∏ x ∈ s, (N x).choose (D x) ≤ (∑ x ∈ s, N x).choose (∑ x ∈ s, D x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    calc (N a).choose (D a) * ∏ x ∈ s, (N x).choose (D x)
        ≤ (N a).choose (D a) * (∑ x ∈ s, N x).choose (∑ x ∈ s, D x) :=
          Nat.mul_le_mul_left _ ih
      _ ≤ (N a + ∑ x ∈ s, N x).choose (D a + ∑ x ∈ s, D x) := by
          rw [Nat.add_choose_eq]
          have hm : (D a, ∑ x ∈ s, D x) ∈ antidiagonal (D a + ∑ x ∈ s, D x) :=
            Finset.mem_antidiagonal.mpr rfl
          exact Finset.single_le_sum
            (f := fun ij : ℕ × ℕ => (N a).choose ij.1 * (∑ x ∈ s, N x).choose ij.2)
            (fun _ _ => Nat.zero_le _) hm

/-- **Stars and bars, quantitatively**: if `N + K ≤ R K`, then `C(N + K, K) ≤ (3 R) ^ K`. -/
theorem add_choose_le_three_mul_pow {N K R : ℕ} (hR : N + K ≤ R * K) :
    (N + K).choose K ≤ (3 * R) ^ K := by
  have hf := K.factorial_pos
  refine Nat.le_of_mul_le_mul_left ?_ hf
  calc K.factorial * (N + K).choose K = (N + K).descFactorial K :=
        (Nat.descFactorial_eq_factorial_mul_choose _ _).symm
    _ ≤ (N + K) ^ K := Nat.descFactorial_le_pow _ _
    _ ≤ (R * K) ^ K := Nat.pow_le_pow_left hR _
    _ = R ^ K * K ^ K := Nat.mul_pow _ _ _
    _ ≤ R ^ K * (3 ^ K * K.factorial) :=
        Nat.mul_le_mul_left _ (pow_self_le_three_pow_mul_factorial K)
    _ = K.factorial * (3 * R) ^ K := by
        rw [Nat.mul_pow]
        ring

end Nat
