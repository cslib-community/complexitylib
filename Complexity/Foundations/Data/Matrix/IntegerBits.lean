/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Binary digits of integer matrices

Finite binary expansions and their products, using Mathlib's pointwise positive and negative
parts. These are algebraic identities, with no algorithm or running-time assertion.

## Main definitions

* `Matrix.bit`: the binary digit matrix of a given weight.

## Main results

* `Matrix.eq_sum_two_pow_smul_bit`: expansion of a nonnegative bounded matrix.
* `Matrix.mul_eq_sum_two_pow_smul_bit_mul_bit`: expansion of a product into digit products.
* `Matrix.eq_map_posPart_sub_map_negPart`: reconstruction from pointwise signed parts.
* `Matrix.map_posPart_lt_and_map_negPart_lt`: bounds for both pointwise signed parts.

## References

Adapted from [Anthropic's MatrixLanguage.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec3/MatrixLanguage.lean),
`matBit` and `Footnote8.binary/product`. The adaptation permits general index types and uses
Mathlib's existing pointwise signed parts.
-/

@[expose] public section

namespace Cslib.Matrix

/-- The binary digit of weight `2^i`, entry by entry. For negative entries this is the
Euclidean remainder of the quotient; reconstruction below assumes nonnegative entries. -/
def bit {m n : Type*} (X : Matrix m n ℤ) (i : ℕ) : Matrix m n ℤ :=
  Matrix.of fun a j => X a j / 2 ^ i % 2

/-- `x mod 2^β` is the sum of the last `β` binary digits of `x`, with their weights. -/
private theorem emod_two_pow_eq_sum_digits (x : ℤ) (β : ℕ) :
    x % 2 ^ β = ∑ i ∈ Finset.range β, 2 ^ i * (x / 2 ^ i % 2) := by
  induction β with
  | zero => simp
  | succ β ih =>
    have h : x / (2 ^ β * 2) = x / 2 ^ β / 2 := (Int.ediv_ediv_of_nonneg (by positivity)).symm
    rw [Finset.sum_range_succ, ← ih, pow_succ, Int.emod_def, Int.emod_def x (2 ^ β),
      Int.emod_def (x / 2 ^ β), h]
    ring

/-- A matrix with entries in `[0, 2^β)` is the weighted sum of its first `β` digit matrices. -/
theorem eq_sum_two_pow_smul_bit {m n : Type*} (X : Matrix m n ℤ) (β : ℕ)
    (hX : ∀ a j, 0 ≤ X a j ∧ X a j < 2 ^ β) :
    X = ∑ i ∈ Finset.range β, (2 : ℤ) ^ i • bit X i := by
  ext a j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, bit, Matrix.of_apply, smul_eq_mul]
  rw [← emod_two_pow_eq_sum_digits, Int.emod_eq_of_lt (hX a j).1 (hX a j).2]

/-- Every digit matrix has entries zero or one, even for signed input. -/
theorem bit_eq_zero_or_one {m n : Type*} (X : Matrix m n ℤ) (i : ℕ) (a : m)
    (j : n) : bit X i a j = 0 ∨ bit X i a j = 1 := by
  simp only [bit, Matrix.of_apply]
  omega

/-- Expand a product of nonnegative bounded matrices into products of binary digits. -/
theorem mul_eq_sum_two_pow_smul_bit_mul_bit {m d n : Type*} [Fintype d]
    (X : Matrix m d ℤ) (Y : Matrix d n ℤ)
    (β : ℕ) (hX : ∀ a j, 0 ≤ X a j ∧ X a j < 2 ^ β) (hY : ∀ j b, 0 ≤ Y j b ∧ Y j b < 2 ^ β) :
    X * Y = ∑ i ∈ Finset.range β, ∑ j ∈ Finset.range β,
      (2 : ℤ) ^ (i + j) • (bit X i * bit Y j) := by
  conv_lhs => rw [eq_sum_two_pow_smul_bit X β hX, eq_sum_two_pow_smul_bit Y β hY]
  rw [Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_add]

/-- Entrywise positive and negative parts reconstruct an integer matrix.
`Matrix.map` reuses scalar signed parts without adding an ordering instance to matrices. -/
theorem eq_map_posPart_sub_map_negPart {m n : Type*} (X : Matrix m n ℤ) :
    X = X.map posPart - X.map negPart := by
  ext a j
  exact (posPart_sub_negPart (X a j)).symm

/-- Both pointwise signed parts of an absolutely bounded matrix satisfy the same nonnegative
bound. This uses the existing ordered-group operations, without introducing matrix variants. -/
theorem map_posPart_lt_and_map_negPart_lt {m n : Type*} (X : Matrix m n ℤ) {β : ℕ}
    (hX : ∀ a j, |X a j| < 2 ^ β) :
    (∀ a j, 0 ≤ (X.map posPart) a j ∧ (X.map posPart) a j < 2 ^ β) ∧
      ∀ a j, 0 ≤ (X.map negPart) a j ∧ (X.map negPart) a j < 2 ^ β := by
  have hpow : (0 : ℤ) < 2 ^ β := by positivity
  exact ⟨fun a j => ⟨le_max_right _ _, max_lt ((le_abs_self _).trans_lt (hX a j)) hpow⟩,
    fun a j => ⟨le_max_right _ _, max_lt ((neg_le_abs _).trans_lt (hX a j)) hpow⟩⟩

end Cslib.Matrix
