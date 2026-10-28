/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Circuit.Arithmetic.GeneralLowerBound

/-!
# Set-multilinearization and the lower bound for formulas over any field

The set-multilinear part of the formula `x₀ · (x₁ + 1)` on both blocks computes the
set-multilinear part of its polynomial, and is set-multilinear with product-depth at most two.

The headline holds over every field, of any characteristic, with no set-multilinearity
hypothesis. It is nontrivial once `k` is large compared with `log₂ (smCost d)`: at
`d = 1331 = 11 ^ 3`, `Δ = 1`, `k = 614760` and `n ≥ 2 ^ k`, where `d ^ (1 / (4 ^ Δ - 1)) = 11`
and the bound reads `2 ^ 30738 ≤ smCost 1331 * nodeCount F` with `smCost 1331 ≤ 2 ^ 30638`,
every formula of product-depth one computing `IMM_{n,1331}` has at least `2 ^ 100` nodes. The
hypotheses are met by the sum over paths (`immFormula`). At small `d`, such as `d = 11` with
`Δ = 1`, the bound is trivial: `d ^ (1 / 3) < 10` makes the exponent negative.
-/

namespace ComplexityTests.ArithmeticGeneralLowerBound

open Cslib.Circuits Cslib.Circuits.Arithmetic Cslib.Circuits.Arithmetic.SPFormula MvPolynomial

/-! ### Set-multilinearization -/

/-- The formula `x₀ · (x₁ + 1)`, over two blocks of one variable each. -/
private noncomputable def F01 : SPFormula ℚ 2 :=
  .mul ![.input 0, add ![1, 1] ![.input 1, const 1]]

example : (smPart (fun i : Fin 2 => i) Finset.univ F01).polynomial =
    smProj (fun i : Fin 2 => i) Finset.univ F01.polynomial :=
  polynomial_smPart _ _

example : (smPart (fun i : Fin 2 => i) Finset.univ F01).IsSetMultilinear (fun i : Fin 2 => i)
    Finset.univ :=
  isSetMultilinear_smPart _ _

example : (smPart (fun i : Fin 2 => i) Finset.univ F01).productDepth ≤ 2 * F01.productDepth :=
  productDepth_smPart_le _ _

example : (smPart (fun i : Fin 2 => i) Finset.univ F01).nodeCount ≤
    smCost 2 ^ F01.productDepth * F01.nodeCount :=
  nodeCount_smPart_le _ _

/-! ### The headline, nonvacuously -/

/-- The size factor for `d + 1 ≤ 2 ^ 11`: `2 * (d + 1) ^ 2 ≤ 2 ^ 23`, so
`smCost d = 4 * (2 * (d + 1) ^ 2) ^ (d + 1) ≤ 2 ^ (23 (d + 1) + 2)`. -/
private theorem smCost_le_of_le {d : ℕ} (hd : d + 1 ≤ 2 ^ 11) :
    smCost d ≤ 2 ^ (23 * (d + 1) + 2) := by
  have h1 : 2 * (d + 1) ^ 2 ≤ 2 ^ 23 :=
    calc 2 * (d + 1) ^ 2 ≤ 2 * (2 ^ 11) ^ 2 := by gcongr
      _ = 2 ^ 23 := by norm_num
  calc smCost d = 4 * (2 * (d + 1) ^ 2) ^ (d + 1) := by
        rw [smCost, gadgetCost]
        ring
    _ ≤ 4 * (2 ^ 23) ^ (d + 1) := by gcongr
    _ = 2 ^ (23 * (d + 1) + 2) := by
        rw [pow_add, ← pow_mul]
        ring

/-- `smCost 1331 ≤ 2 ^ 30638`. -/
private theorem smCost_le : smCost 1331 ≤ 2 ^ 30638 :=
  (smCost_le_of_le (by norm_num)).trans_eq
    (congrArg (2 ^ ·) (by norm_num : 23 * (1331 + 1) + 2 = 30638))

/-- `1331 ^ (1 / (4 ^ 1 - 1)) = 11`. -/
private theorem rpow_eq : (1331 : ℝ) ^ (1 / (4 ^ 1 - 1 : ℝ)) = 11 := by
  rw [show (1 / (4 ^ 1 - 1 : ℝ)) = ((3 : ℕ) : ℝ)⁻¹ by norm_num,
    show (1331 : ℝ) = 11 ^ 3 by norm_num, Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]

/-- **The lower bound over any field** at `d = 1331`, `Δ = 1`, `k = 614760` and `n ≥ 2 ^ k`: every
formula of product-depth one computing `IMM_{n,1331}` has at least `2 ^ 100` nodes. -/
private theorem two_pow_le_nodeCount {K : Type*} [Field K] {n : ℕ} [NeZero n]
    (hn : 2 ^ 614760 ≤ n) {F : SPFormula K (1331 * (n * n))} (hFΔ : F.productDepth ≤ 1)
    (hFP : rename (immVarEquiv n 1331) F.polynomial = imm K n 1331) :
    2 ^ 100 ≤ F.nodeCount := by
  have h := two_rpow_le_of_imm (immVarEquiv n 1331) (k := 614760) (Δ := 1) (by norm_num) hn
    le_rfl hFΔ hFP
  simp only [Nat.cast_ofNat] at h
  rw [rpow_eq,
    show (614760 : ℝ) * (11 / 20 - 1 / 2) = ((30738 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    pow_one] at h
  have hc : (smCost 1331 : ℝ) ≤ 2 ^ 30638 := by exact_mod_cast smCost_le
  have h' : (2 : ℝ) ^ 30638 * 2 ^ 100 ≤ 2 ^ 30638 * F.nodeCount := by
    rw [← pow_add]
    exact h.trans (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _))
  exact_mod_cast le_of_mul_le_mul_left h' (by positivity)

/-- The sum over paths for `IMM_{n,1331}` meets the hypotheses. -/
example {K : Type*} [Field K] {n : ℕ} [NeZero n] (hn : 2 ^ 614760 ≤ n) :
    2 ^ 100 ≤ (immFormula K n 1331).nodeCount :=
  two_pow_le_nodeCount hn (productDepth_immFormula_le _) (rename_polynomial_immFormula _)

end ComplexityTests.ArithmeticGeneralLowerBound
