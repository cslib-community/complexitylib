/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Circuit.Arithmetic.SetMultilinearLowerBound

/-!
# Lower bound for set-multilinear formulas computing IMM

Substituting `x₀ ↦ x₀` and `x₁ ↦ 0` into the formula `x₀ · x₁` keeps its size and
set-multilinearity and computes `0`. The word of Lemma 15 at `k = 10` and `d = 3` is
`7, -10, 7`, and it is `10`-unbiased. The hypotheses of the headline are met for every `n` and `d`
by the sum over paths (`immFormula`). At `d = 11`, `k = 110`, `n = 2 ^ 110` and `Δ = 1` the bound
reads `2 ^ (11 / 2) ≤ F.nodeCount`, so every syntactically set-multilinear formula of
product-depth one computing `IMM_{2 ^ 110, 11}` has more than `45` nodes.
-/

namespace ComplexityTests.ArithmeticSetMultilinearLowerBound

open Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial

/-! ### Substitution -/

/-- The product `x₀ · x₁`, on blocks `0` and `1`. -/
private noncomputable def prod01 : SPFormula ℚ 2 :=
  .mul ![.input 0, .input 1]

private theorem prod01_isSetMultilinear :
    prod01.IsSetMultilinear (fun i : Fin 2 => i) Finset.univ := by
  have h := SPFormula.IsSetMultilinear.mul (blk := fun i : Fin 2 => i) ![.input 0, .input 1]
    (fun j => {j}) (fun i j hij => Finset.disjoint_singleton.2 hij) fun j => by
      fin_cases j
      · exact SPFormula.IsSetMultilinear.input (K := ℚ) (blk := fun i : Fin 2 => i) 0
      · exact SPFormula.IsSetMultilinear.input (K := ℚ) (blk := fun i : Fin 2 => i) 1
  have hu : Finset.univ.biUnion (fun j : Fin 2 => ({j} : Finset (Fin 2))) = Finset.univ := by
    decide
  rwa [hu] at h

/-- Keep `x₀`, set `x₁` to `0`. -/
private def ρ01 : Fin 2 → Option (Fin 2) := ![some 0, none]

example : (SPFormula.subst ρ01 prod01).IsSetMultilinear (fun i : Fin 2 => i) Finset.univ :=
  prod01_isSetMultilinear.subst fun i j h => by
    fin_cases i <;> simp_all [ρ01]

example : (SPFormula.subst ρ01 prod01).nodeCount = prod01.nodeCount :=
  SPFormula.nodeCount_subst ρ01 prod01

example : (SPFormula.subst ρ01 prod01).polynomial = 0 := by
  rw [SPFormula.polynomial_subst]
  simp [prod01, ρ01]

/-! ### The word -/

/-- `⌊10 / √2⌋ = 7`, since `7 ^ 2 * 2 ≤ 10 ^ 2 < 8 ^ 2 * 2`. -/
private theorem floor_ten_div_sqrt_two : ⌊((10 : ℕ) : ℝ) / √2⌋ = 7 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h0 := Real.sqrt_nonneg 2
  have hpos : 0 < √2 := by positivity
  rw [Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ hpos]
    push_cast
    nlinarith
  · rw [div_lt_iff₀ hpos]
    push_cast
    nlinarith

/-- The word of Lemma 15 at `k = 10` and `d = 3` is `7, -10, 7`, with prefix sums `0, 7, -3, 4`,
and it is `10`-unbiased. -/
example : sqrtTwoWord 10 3 = ![7, -10, 7] ∧ IsUnbiased (sqrtTwoWord 10 3) 10 := by
  refine ⟨?_, isUnbiased_sqrtTwoWord 10 3⟩
  rw [sqrtTwoWord, floor_ten_div_sqrt_two]
  decide

/-! ### The headline, nonvacuously -/

/-- The hypotheses of the lower bound are met for every `n` and `d`, by the sum over paths. -/
example (n d : ℕ) [NeZero n] :
    (immFormula ℚ n d).IsSetMultilinear (fun v => (immVarEquiv n d v).1) Finset.univ ∧
      (immFormula ℚ n d).productDepth ≤ 1 ∧
      rename (immVarEquiv n d) (immFormula ℚ n d).polynomial = imm ℚ n d :=
  ⟨isSetMultilinear_immFormula n, productDepth_immFormula_le n, rename_polynomial_immFormula n⟩

/-- **LST Lemma 15** at `d = 11`, `k = 110`, `n = 2 ^ 110` and `Δ = 1`, where the exponent
`k (d / 20 - 1 / 2)` is `11 / 2`: every syntactically set-multilinear formula of product-depth
one computing `IMM_{2 ^ 110, 11}` has more than `45` nodes. -/
private theorem two_rpow_le_nodeCount {F : SPFormula ℚ (11 * (2 ^ 110 * 2 ^ 110))}
    (hF : F.IsSetMultilinear (fun v => (immVarEquiv (2 ^ 110) 11 v).1) Finset.univ)
    (hFΔ : F.productDepth ≤ 1)
    (hFP : rename (immVarEquiv (2 ^ 110) 11) F.polynomial = imm ℚ (2 ^ 110) 11) :
    (2 : ℝ) ^ (11 / 2 : ℝ) ≤ F.nodeCount := by
  have h := hF.two_rpow_le_nodeCount_of_imm (immVarEquiv _ _) (k := 110) (by norm_num) le_rfl
    le_rfl hFΔ hFP
  convert h using 2
  norm_num

/-- `45 < 2 ^ (11 / 2)`, since `45 ^ 2 < 2 ^ 11`. -/
private theorem forty_five_lt : (45 : ℝ) < 2 ^ (11 / 2 : ℝ) := by
  rw [show (11 / 2 : ℝ) = (11 : ℝ) * (1 / 2) by norm_num, Real.rpow_mul (by norm_num),
    ← Real.sqrt_eq_rpow, Real.lt_sqrt (by norm_num)]
  norm_num

example {F : SPFormula ℚ (11 * (2 ^ 110 * 2 ^ 110))}
    (hF : F.IsSetMultilinear (fun v => (immVarEquiv (2 ^ 110) 11 v).1) Finset.univ)
    (hFΔ : F.productDepth ≤ 1)
    (hFP : rename (immVarEquiv (2 ^ 110) 11) F.polynomial = imm ℚ (2 ^ 110) 11) :
    45 < F.nodeCount := by
  exact_mod_cast forty_five_lt.trans_le (two_rpow_le_nodeCount hF hFΔ hFP)

/-- The sum over paths for `IMM_{2 ^ 110, 11}` meets these hypotheses. -/
example : (2 : ℝ) ^ (11 / 2 : ℝ) ≤ (immFormula ℚ (2 ^ 110) 11).nodeCount :=
  two_rpow_le_nodeCount (isSetMultilinear_immFormula _) (productDepth_immFormula_le _)
    (rename_polynomial_immFormula _)

end ComplexityTests.ArithmeticSetMultilinearLowerBound
