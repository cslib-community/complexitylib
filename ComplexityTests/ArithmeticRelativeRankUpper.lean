/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Circuit.Arithmetic.RelativeRankUpper

/-!
# Upper bound on the relative rank of set-multilinear formulas

LST Claim 17 at `a = b = 1`, and its failure at `a = b = 0`. The hypotheses of LST Claim 16 are
met by one block of `2 ^ 7` variables with `k = 10` and the letter `⌊10 / √2⌋ = 7`, and the
claim bounds the relative rank of a variable there by `2 ^ (-1 / 2)`. The formula `0` is
set-multilinear on every set of blocks and computes zero, the case that Claim 16's base case treats
separately.
-/

namespace ComplexityTests.ArithmeticRelativeRankUpper

open Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial

/-! ### LST Claim 17 -/

example : 1 / (4 * |((1 : ℤ) : ℝ) / √2| + 2) ≤ |((1 : ℤ) : ℝ) / √2 - ((1 : ℤ) : ℝ)| :=
  one_div_le_abs_div_sqrt_two_sub (Or.inl one_ne_zero)

/-- Claim 17 fails at `a = b = 0`, which its statement excludes. -/
example : ¬ (1 / (4 * |((0 : ℤ) : ℝ) / √2| + 2) ≤ |((0 : ℤ) : ℝ) / √2 - ((0 : ℤ) : ℝ)|) := by
  norm_num

/-! ### One block of `2 ^ 7` variables, `k = 10` -/

/-- `⌊10 / √2⌋ = 7`. -/
private theorem floor_ten_div_sqrt_two : ⌊(10 : ℝ) / √2⌋ = 7 := by
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

/-- All `2 ^ 7` variables in block `0`. -/
private def blk7 : Fin 128 → Fin 1 := fun _ => 0

/-- The word `(7)` of length one. -/
private def w7 : Fin 1 → ℤ := fun _ => 7

private theorem hblk7 (i : Fin 1) :
    Fintype.card {x : Fin 128 // blk7 x = i} = 2 ^ (w7 i).natAbs := by
  rw [Fintype.card_subtype, Subsingleton.elim i 0]
  simp [blk7, w7]

private theorem hw7 (i : Fin 1) : w7 i = ⌊((10 : ℕ) : ℝ) / √2⌋ ∨ w7 i = -((10 : ℕ) : ℤ) := by
  left
  rw [Nat.cast_ofNat, floor_ten_div_sqrt_two]
  rfl

/-- **LST Claim 16** for the variable `x₀`, a set-multilinear formula of one node on block `0`:
its relative rank is at most `2 ^ (-1 / 2)`. -/
example : relRank blk7 (wordPos w7 ∩ {0}) (wordNeg w7 ∩ {0})
    (X 0 : MvPolynomial (Fin 128) ℚ) ≤ 2 ^ (-(1 / 2 : ℝ)) := by
  have h := SPFormula.IsSetMultilinear.relRank_polynomial_le (K := ℚ) (k := 10) hblk7
    (by norm_num) hw7 le_rfl (SPFormula.IsSetMultilinear.input 0) (Nat.zero_le 1)
  refine h.trans_eq ?_
  rw [Formula.nodeCount_input, Finset.card_singleton]
  norm_num

/-! ### Product-depth zero on two blocks -/

/-- The formula `0` has product-depth zero and is set-multilinear on two blocks... -/
example : (SPFormula.zero : SPFormula ℚ 2).productDepth = 0 ∧
    (SPFormula.zero : SPFormula ℚ 2).IsSetMultilinear (fun i : Fin 2 => i) Finset.univ :=
  ⟨SPFormula.productDepth_zero, SPFormula.isSetMultilinear_zero _⟩

/-- ... and computes zero, as the base case of Claim 16 requires. -/
example : (SPFormula.zero : SPFormula ℚ 2).polynomial = 0 :=
  SPFormula.isSetMultilinear_zero (blk := fun i : Fin 2 => i) Finset.univ
    |>.card_le_one_or_polynomial_eq_zero SPFormula.productDepth_zero
    |>.resolve_left (by decide)

end ComplexityTests.ArithmeticRelativeRankUpper
