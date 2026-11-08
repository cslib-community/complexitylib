/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.KhrapchenkoDepth

/-! Clients for Yablonskii's formulas for parity, the formula depth of parity and
Khrapchenko's bounds for majority. -/

namespace ComplexityTests.FormulaDepth

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

-- The parity of four bits has formula depth exactly four.
example : formulaDepth (parity 4) = 4 :=
  formulaDepth_parity_two_pow 2

-- The parity of five bits has formula depth five or six.
example : 5 ≤ formulaDepth (parity 5) ∧ formulaDepth (parity 5) ≤ 6 :=
  ⟨two_mul_add_one_le_formulaDepth_parity (k := 2) (r := 1) one_pos,
    formulaDepth_parity_two_pow_add_le (k := 2) (r := 1) (by norm_num)⟩

-- Yablonskii's formula for the parity of five bits: leaf size at most `4 · 7 = 28` and depth six.
example : (yablonskiiFormula 2 1 0 (by norm_num) le_rfl : Formula signature 5).Computes
    interpretation (parity 5) :=
  computes_yablonskiiFormula 2 1 (by norm_num)

example : (yablonskiiFormula 2 1 0 (by norm_num) le_rfl : Formula signature 5).leafSize ≤ 28 :=
  leafSize_yablonskiiFormula_le 2 1 0 (by norm_num) le_rfl

example :
    (yablonskiiFormula 2 1 0 (by norm_num) le_rfl : Formula signature 5).depthWith binaryCost = 6 :=
  depthWith_binaryCost_yablonskiiFormula 2 1 0 (by norm_num) le_rfl

-- The uniform bound `9 n ^ 2 / 8` matches Yablonskii's bound for five bits.
example : ∃ F : Formula signature 5, F.Computes interpretation (parity 5) ∧ F.leafSize ≤ 28 := by
  obtain ⟨F, hF, hL⟩ := exists_formula_parity_eight_mul_leafSize_le 5
  exact ⟨F, hF, by omega⟩

-- With Khrapchenko's bound, the least formula for the parity of five bits has 25 to 28 leaves.
example : ∃ F : Formula signature 5, F.Computes interpretation (parity 5) ∧
    25 ≤ F.leafSize ∧ F.leafSize ≤ 28 := by
  obtain ⟨F, hF, hL⟩ := exists_formula_parity_two_pow_add (k := 2) (r := 1) (by norm_num)
  exact ⟨F, hF, sq_le_leafSize_of_computes_parity hF, hL⟩

-- Every formula for the majority of five bits has at least nine leaves, and depth at least four.
example {F : Formula signature 5} (hF : F.Computes interpretation (majority 5)) :
    9 ≤ F.leafSize :=
  sq_div_four_le_leafSize_of_computes_majority hF

example : 4 ≤ formulaDepth (majority 5) := by
  have h := clog_sq_div_four_le_formulaDepth_majority 5
  have h9 : Nat.clog 2 ((5 + 1) ^ 2 / 4) = 4 := by
    rw [show (5 + 1) ^ 2 / 4 = 9 by norm_num]
    refine le_antisymm (Nat.clog_le_of_le_pow (by norm_num)) ?_
    exact (Nat.lt_clog_iff_pow_lt one_lt_two).2 (by norm_num)
  omega

-- Splitting a block of consecutive bits.
example (x : BitString 5) :
    parityOn ({i | 0 ≤ (i : ℕ) ∧ (i : ℕ) < 0 + (2 + 3)} : Finset (Fin 5)) x =
      (parityOn ({i | 0 ≤ (i : ℕ) ∧ (i : ℕ) < 0 + 2} : Finset (Fin 5)) x ^^
        parityOn ({i | 0 + 2 ≤ (i : ℕ) ∧ (i : ℕ) < 0 + 2 + 3} : Finset (Fin 5)) x) :=
  parityOn_consecutive_add 0 2 3 x

end ComplexityTests.FormulaDepth
