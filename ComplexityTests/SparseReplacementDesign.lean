/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.SparseReplacementDesign
import Mathlib.Tactic.NormNum

/-!
# Tests for `Complexity.Foundations.BooleanAnalysis.SparseReplacementDesign`

Concrete checks and nonvacuous witnesses for neutral-singleton augmented equation scopes,
`designRowNormBound`, `exists_replacementDesign_augmentedEquationScope`, and the
`ReplacementDesign` specializations of cleared-denominator zero counting and heavy-variable
branch recovery.
-/

@[expose] public noncomputable section

namespace Cslib.BitString.SparseReplacementDesignTests

open Finset Polynomial
open scoped BigOperators
open Cslib.BalancedSchedules Cslib.LinearAlgebra

/-- Concrete equation family on `Fin 3` with two equations:
- equation `0`: `x₀ + x₀ x₁ = 0` (monomials `{0}`, `{0, 1}`; scope `{0, 1}`),
- equation `1`: `x₁ x₂ + 1 = 0` (monomials `{1, 2}`, `∅`; scope `{1, 2}`). -/
def sampleEqs : Fin 2 → Finset (Finset (Fin 3))
  | ⟨0, _⟩ => {{0}, {0, 1}}
  | ⟨1, _⟩ => {{1, 2}, ∅}

/-- Total incidence of `augmentedEquationScope sampleEqs` is `(2 + 2) + 3 = 7 ≥ 3`. -/
example :
    (∑ f : Fin 2 ⊕ Fin 3, #(augmentedEquationScope sampleEqs f)) = 7 ∧
      3 ≤ ∑ f : Fin 2 ⊕ Fin 3, #(augmentedEquationScope sampleEqs f) := by
  refine ⟨?_, le_sum_card_augmentedEquationScope sampleEqs⟩
  rw [sum_card_augmentedEquationScope]
  decide

/-- Variable `1 : Fin 3` belongs to both equation scopes plus its neutral singleton scope
(`2 + 1 = 3` scopes total), whereas variable `0 : Fin 3` belongs to `1 + 1 = 2` scopes. -/
example :
    #{f : Fin 2 ⊕ Fin 3 | (1 : Fin 3) ∈ augmentedEquationScope sampleEqs f} = 3 ∧
      #{f : Fin 2 ⊕ Fin 3 | (0 : Fin 3) ∈ augmentedEquationScope sampleEqs f} = 2 := by
  rw [card_filter_mem_augmentedEquationScope, card_filter_mem_augmentedEquationScope]
  decide

/-- Explicit value of `designRowNormBound 3 2`:
`commonDenom 3 2 = 1! * 3! = 6` and `1 + (1 + 2 ^ 3) * 2 * (4 * 3) ^ 1 = 1 + 9 * 2 * 12 = 217`,
so `designRowNormBound 3 2 = 6 * 217 = 1302`. -/
example :
    commonDenom 3 2 = 6 ∧
      designRowNormBound 3 2 = 1302 ∧
      commonDenom 3 2 ≤ designRowNormBound 3 2 ∧
      0 < designRowNormBound 3 2 := by
  refine ⟨by decide, by decide, commonDenom_le_designRowNormBound 3 2, designRowNormBound_pos 3 2⟩

/-- Empty equation family on `n = 16384` variables used to witness
`exists_replacementDesign_augmentedEquationScope` with `b₀ = 0` (`b = 1`), `w = 1`, `Q = 3`,
`r = 2`, `A₀ = 0`, `R = 2`, `τ = 1 / 2`. -/
def emptyEqs16384 : Fin 0 → Finset (Finset (Fin 16384)) :=
  Fin.elim0

/-- Nonvacuous witness of `exists_replacementDesign_augmentedEquationScope` and exact modular
recovery of `commonZeroCount = 2 ^ 16384` at precision `ℓ = 16385`. -/
theorem exists_design_and_recover_emptyEqs16384 :
    ∃ D : ReplacementDesign (augmentedEquationScope emptyEqs16384) 3 2 0 2 (1 / 2),
      ((univariateClearedParityTruncatedSum (univ : Finset (Fin 0)) emptyEqs16384
          (commonDenom 3 2 : ℤ) 3 16385
          (designReplacementScaledIntMap D Sum.inl)).eval 0 /
        clearedProductDenom (commonDenom 3 2 : ℤ) 3 16385 #(univ : Finset (Fin 0))) %
          ((2 : ℤ) ^ 16385) =
        (2 : ℤ) ^ 16384 := by
  have hcard : #(measurementIndices 3 2 0 2) = 10 := by
    rw [card_measurementIndices_eq]
    decide
  have htail : binomTailProb 3 2 0 2 ≤ (1 / 2 : ℚ) / ((2 : ℚ) * ((0 + 1 : ℕ) : ℚ)) := by
    rw [binomTailProb_eq_div 3 2 0 2 (by decide), hcard]
    norm_num
  have hne : Nonempty (ReplacementDesign (augmentedEquationScope emptyEqs16384) 3 2 0 2 (1 / 2)) :=
    exists_replacementDesign_augmentedEquationScope emptyEqs16384 (b₀ := 0) (w := 1)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num)
      (by intro a ha; omega)
      (fun v => by simp)
      (fun i => Fin.elim0 i)
      (by decide)
      (by decide)
      htail
  obtain ⟨D⟩ := hne
  refine ⟨D, ?_⟩
  have hrec :=
    emod_ediv_eval_zero_clearedParityTruncatedSum_design_eq_commonZeroCount D Sum.inl
      (univ : Finset (Fin 0)) emptyEqs16384 (k := 3) (ℓ := 16385) (by decide)
      (fun i => Fin.elim0 i)
  have hcount : (commonZeroCount (univ : Finset (Fin 0)) emptyEqs16384 : ℤ) = (2 : ℤ) ^ 16384 := by
    have hempty : (univ : Finset (Fin 0)) = ∅ := rfl
    rw [hempty, commonZeroCount_empty, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  exact hrec.trans hcount

end Cslib.BitString.SparseReplacementDesignTests
