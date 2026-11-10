/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.LatticeReduction.Potential
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Tests for LLL-reduced bases and the LLL potential

Two-dimensional witnesses in `EuclideanSpace ℝ (Fin 2)` with unit vectors `e₀`, `e₁`:

* the standard basis `(e₀, e₁)` is `3/4`-reduced, so the hypotheses of the SVP bound
  `IsReduced.norm_le_sqrt_two_pow_mul` are satisfiable;
* `(e₀, ½ e₀ + e₁)` is `3/4`-reduced with `μ₁₀ = 1/2`, the extreme allowed by (1.4);
* `(e₀, e₀ + e₁)` is not size reduced (`μ₁₀ = 1`);
* `(2 e₀, e₀ + e₁)` violates the exchange condition at `(0, 1)`, swapping it is an exchange step,
  and the potential drops from `4` to `2 < (3/4) · 4`.
-/

namespace ComplexityTests.Algorithms.LatticeReduction

open InnerProductSpace Cslib.Algorithms.LatticeReduction

local notation "e₀" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e₁" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

/-! ### Dimension two -/

/-- In dimension two the potential is `‖b₀‖²`. -/
theorem potential_two {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Fin 2 → E) : potential b = ‖b 0‖ ^ 2 := by
  have h0 : gramPrefixDet b 0 = 1 := by simp [gramPrefixDet]
  have h1 := gramPrefixDet_succ b 0
  simp only [Fin.val_zero, zero_add] at h1
  rw [potential, Finset.prod_range_succ, Finset.prod_range_one, h0, one_mul, h1, h0, one_mul,
    ← bot_eq_zero, gramSchmidt_bot]

/-- In dimension two, the exchange condition at `(0, 1)` says `δ ‖b₀‖² ≤ ‖b₁‖²`. -/
theorem exchangeCondAt_two_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (δ : ℝ) (b : Fin 2 → E) : ExchangeCondAt δ b 0 1 ↔ δ * ‖b 0‖ ^ 2 ≤ ‖b 1‖ ^ 2 := by
  have h0 : gramSchmidt ℝ b 0 = b 0 := by rw [← bot_eq_zero, gramSchmidt_bot]
  have hsum := gramSchmidt_add_sum_coeff (𝕜 := ℝ) b 1
  have hIio : Finset.Iio (1 : Fin 2) = {0} := by decide
  rw [hIio, Finset.sum_singleton] at hsum
  rw [ExchangeCondAt, ← hsum, h0]

/-- Swapping a pair turns the first Gram–Schmidt vector into the old second vector. -/
example (b : Fin 2 → EuclideanSpace ℝ (Fin 2)) :
    gramSchmidt ℝ (b ∘ Equiv.swap 0 1) 0 = b 1 := by
  rw [← bot_eq_zero, gramSchmidt_bot]
  simp

/-! ### A reduced basis -/

/-- The standard basis of `ℤ²` is `3/4`-reduced. -/
theorem isReduced_std : IsReduced (3 / 4) ![e₀, e₁] := by
  have horth : Pairwise fun i j => inner ℝ (![e₀, e₁] i) (![e₀, e₁] j) = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [EuclideanSpace.inner_single_left]
  have hgs : gramSchmidt ℝ ![e₀, e₁] = ![e₀, e₁] := gramSchmidt_of_orthogonal ℝ horth
  refine ⟨?_, ?_⟩
  · intro i j hji
    fin_cases i <;> fin_cases j <;> simp_all [gramSchmidtCoeff, EuclideanSpace.inner_single_left]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [ExchangeCondAt, gramSchmidtCoeff,
      EuclideanSpace.inner_single_left, PiLp.norm_single]
    norm_num

/-- The SVP bound applies to the standard basis. -/
example {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ Submodule.span ℤ (Set.range ![e₀, e₁]))
    (hx0 : x ≠ 0) : ‖e₀‖ ≤ Real.sqrt 2 ^ 1 * ‖x‖ :=
  isReduced_std.norm_le_sqrt_two_pow_mul hx hx0

/-! ### A reduced basis with a nonzero size coefficient -/

/-- The basis `(e₀, ½ e₀ + e₁)`. -/
noncomputable abbrev bHalf : Fin 2 → EuclideanSpace ℝ (Fin 2) := ![e₀, (1 / 2 : ℝ) • e₀ + e₁]

/-- `μ₁₀ = 1/2` for `(e₀, ½ e₀ + e₁)`. -/
theorem gramSchmidtCoeff_bHalf : gramSchmidtCoeff ℝ bHalf 1 0 = 1 / 2 := by
  have h0 : gramSchmidt ℝ bHalf 0 = e₀ := gramSchmidt_bot ℝ bHalf
  rw [gramSchmidtCoeff, h0]
  simp [inner_add_right, inner_smul_right, EuclideanSpace.inner_single_left, PiLp.norm_single]

theorem norm_sq_bHalf_one : ‖bHalf 1‖ ^ 2 = 5 / 4 := by
  simp only [bHalf, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [@norm_add_sq_real, norm_smul, PiLp.norm_single, PiLp.norm_single, real_inner_smul_left,
    EuclideanSpace.inner_single_left]
  norm_num

theorem norm_bHalf_zero : ‖bHalf 0‖ = 1 := by
  simp only [bHalf, Matrix.cons_val_zero, PiLp.norm_single, norm_one]

/-- `(e₀, ½ e₀ + e₁)` is `3/4`-reduced with the extreme size coefficient `μ₁₀ = 1/2`. -/
theorem isReduced_bHalf : IsReduced (3 / 4) bHalf := by
  refine ⟨fun i j hji => ?_, fun i j hij => ?_⟩
  · have hlt := Fin.lt_def.1 hji
    obtain rfl : i = 1 := Fin.ext (by have := i.isLt; simp only [Fin.val_one]; omega)
    obtain rfl : j = 0 := Fin.ext <| by
      simp only [Fin.val_one] at hlt; simp only [Fin.val_zero]; omega
    rw [gramSchmidtCoeff_bHalf]
    norm_num
  · obtain rfl : j = 1 := Fin.ext (by have := j.isLt; simp only [Fin.val_one]; omega)
    obtain rfl : i = 0 := Fin.ext <| by
      simp only [Fin.val_one] at hij; simp only [Fin.val_zero]; omega
    rw [exchangeCondAt_two_iff, norm_sq_bHalf_one, norm_bHalf_zero]
    norm_num

/-! ### A basis that is not size reduced -/

/-- `(e₀, e₀ + e₁)` has `μ₁₀ = 1`, so it is not size reduced. -/
example : ¬ IsSizeReduced ![e₀, e₀ + e₁] := by
  intro h
  have h10 := h 1 0 (by decide)
  have h0 : gramSchmidt ℝ ![e₀, e₀ + e₁] 0 = e₀ := gramSchmidt_bot ℝ ![e₀, e₀ + e₁]
  rw [gramSchmidtCoeff, h0] at h10
  simp [inner_add_right, EuclideanSpace.inner_single_left, PiLp.norm_single] at h10
  norm_num at h10

/-! ### An exchange step -/

/-- The basis `(2 e₀, e₀ + e₁)`. -/
noncomputable abbrev bSwap : Fin 2 → EuclideanSpace ℝ (Fin 2) := ![(2 : ℝ) • e₀, e₀ + e₁]

theorem norm_sq_bSwap_zero : ‖bSwap 0‖ ^ 2 = 4 := by
  simp only [bSwap, Matrix.cons_val_zero, norm_smul, PiLp.norm_single, norm_one, mul_one,
    Real.norm_eq_abs]
  norm_num

theorem norm_sq_bSwap_one : ‖bSwap 1‖ ^ 2 = 2 := by
  simp only [bSwap, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [@norm_add_sq_real, PiLp.norm_single, PiLp.norm_single, EuclideanSpace.inner_single_left]
  norm_num

/-- `(2 e₀, e₀ + e₁)` violates the exchange condition at `(0, 1)`: `3/4 · 4 > 2`. -/
theorem not_exchangeCondAt_bSwap : ¬ ExchangeCondAt (3 / 4) bSwap 0 1 := by
  rw [exchangeCondAt_two_iff, norm_sq_bSwap_zero, norm_sq_bSwap_one]
  norm_num

/-- Swapping `(2 e₀, e₀ + e₁)` is an exchange step. -/
theorem isSwapStep_bSwap : IsSwapStep (3 / 4) bSwap (bSwap ∘ Equiv.swap 0 1) :=
  ⟨0, 1, rfl, not_exchangeCondAt_bSwap, rfl⟩

theorem potential_bSwap : potential bSwap = 4 := by
  rw [potential_two, norm_sq_bSwap_zero]

theorem potential_bSwap_swap : potential (bSwap ∘ Equiv.swap 0 1) = 2 := by
  rw [potential_two, Function.comp_apply, Equiv.swap_apply_left, norm_sq_bSwap_one]

/-- The exchange step strictly decreases the potential: `2 < (3/4) · 4`. -/
example : potential (bSwap ∘ Equiv.swap 0 1) < 3 / 4 * potential bSwap := by
  rw [potential_bSwap, potential_bSwap_swap]
  norm_num

end ComplexityTests.Algorithms.LatticeReduction
