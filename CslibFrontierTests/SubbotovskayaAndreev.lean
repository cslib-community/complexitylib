/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.Formula.Andreev

/-! Clients and non-vacuity checks for formula restrictions, Subbotovskaya's shrinkage lemma, and
Andreev's formula lower bound. -/

namespace CslibFrontierTests.SubbotovskayaAndreev

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Formula

-- Non-vacuity of `Formula.IsSimplified`: a conjunction of an input and a negated input is
-- simplified and satisfies `size + 2 ≤ 3 * leafSize`.
example :
    ((Formula.input (0 : Fin 2)).and (Formula.input 1).not : Formula signature 2).IsSimplified :=
  .and (.input 0) (.not_input 1)

example :
    ((Formula.input (0 : Fin 2)).and (Formula.input 1).not : Formula signature 2).size + 2 ≤
      3 * ((Formula.input (0 : Fin 2)).and (Formula.input 1).not : Formula signature 2).leafSize :=
  (IsSimplified.and (.input 0) (.not_input 1)).size_add_two_le

-- Non-vacuity of `Formula.IsLeafMinimal`: a single input formula is leaf-minimal (the projection
-- is not constant, so any formula computing it has at least one leaf).
example : (Formula.input (0 : Fin 2) : Formula signature 2).IsLeafMinimal := by
  intro G hG
  rw [leafSize_input]
  by_contra! h0
  have hzero : G.leafSize = 0 := by omega
  have hconst := eval_eq_of_leafSize_eq_zero hzero interpretation (fun _ => false) (fun _ => true)
  rw [hG, hG, eval_input, eval_input] at hconst
  exact Bool.false_ne_true hconst

-- Restricting a conjunction `x₀ ∧ x₁` by `x₀ = false` simplifies it to the constant `false` with
-- zero leaves.
example :
    (((Formula.input (0 : Fin 2)).and (Formula.input 1) : Formula signature 2).restrictAt
      0 false).leafSize = 0 := by
  rfl

-- Subbotovskaya's parity lower bound on 4 bits: `4 ^ 3 = 64 ≤ L(parity 4) ^ 2`.
example : 64 ≤ formulaSize (parity 4) ^ 2 :=
  pow_three_le_formulaSize_parity_sq 4

example {F : Formula signature 4} (hF : F.Computes interpretation (parity 4)) :
    64 ≤ F.leafSize ^ 2 :=
  pow_three_le_leafSize_sq_of_computes_parity hF

-- Subbotovskaya's shrinkage instantiated for `parity 8` restricted to `k = 2` free bits.
example :
    ∃ ρ ∈ PartialAssignment.withFree (Fin 8) 2,
      formulaSize (parity 8 ∘ ρ.fill) ^ 2 * 512 ≤ formulaSize (parity 8) ^ 2 * 8 :=
  exists_withFree_formulaSize_sq_mul_pow_three_le (parity 8) (by decide) (by decide)

-- Andreev's reduction instantiated with `h = parity 4` (`b = 4`, `r = 3`, `m = 6`):
-- `(L(parity 4) - 24) ^ 2 * 216 ≤ 108 * L(andreev 4 6) ^ 2`.
example :
    (formulaSize (parity 4) - 2 * 4 * 3) ^ 2 * 6 ^ 3 ≤
      4 * formulaSize (andreev 4 6) ^ 2 * 3 ^ 3 :=
  formulaSize_sub_sq_mul_pow_three_le_andreev (parity 4) (by decide) (by decide) (by decide)
    (by decide)

-- Andreev's explicit `n ^ (5 / 2 - o(1))` lower bound provides a threshold `B` above which
-- `2 ^ (5 * b) ≤ 144 * b ^ 2 * (⌊log₂ b⌋ + 2) ^ 3 * L(andreev b (2 ^ b)) ^ 2`.
example :
    ∃ B : ℕ, ∀ b ≥ B,
      2 ^ (5 * b) ≤
        144 * b ^ 2 * (Nat.log 2 b + 2) ^ 3 * formulaSize (andreev b (2 ^ b)) ^ 2 :=
  two_pow_five_mul_le_formulaSize_andreev_sq

end CslibFrontierTests.SubbotovskayaAndreev
