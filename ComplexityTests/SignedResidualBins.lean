/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module

import Complexity.Computability.LogSpaceDerandomization.SignedResidualBins
import Mathlib.Tactic.FinCases

/-! Nonconstant signed residuals, clipped routing, raw ranks and substituted preparations. -/

set_option linter.privateModule false

namespace ComplexityTests.SignedResidualBins

open Matrix Finset
open scoped BigOperators

private noncomputable def base : Matrix (Fin 2) (Fin 2) ℝ :=
  of fun x y => if x = 0 ∧ y = 1 then 1 else if x = 1 ∧ y = 0 then 100 else 0
private noncomputable def correction : Matrix (Fin 2) (Fin 2) ℝ :=
  of fun x y => if x = 0 ∧ y = 1 then 3 else 0
private noncomputable abbrev raw := CorrectionRowRecipe.residual base correction correction 0

-- Same whole functions give negative, oversized and zero entries.
example : raw 0 1 = -2 ∧ raw 1 0 = 100 ∧ raw 0 0 = 0 := by
  norm_num [CorrectionRowRecipe.residual, base, correction, Fin.sum_univ_two]

private noncomputable def switch (d : ℝ) : ℝ := min 1 (max 0 (2 * d - 1))
private noncomputable def scales (i : ℕ) : ℝ := (1 / 2) ^ i
private noncomputable def route (w : ℝ) : ℝ := min 1 (max 0 (w / 4))
private noncomputable abbrev cutoff := boundedRoutedBinCutoff switch scales 3

-- Top clipping includes the routing argument: 3 * (3/4), not 3 * route(100).
example : cutoff 0 route (raw 1 0) = 9 / 4 := by
  norm_num [boundedRoutedBinCutoff, routedBinCutoff, Cslib.binWeight,
    switch, scales, route, CorrectionRowRecipe.residual, base, correction, Fin.sum_univ_two]

example : cutoff 0 route (raw 0 1) = 0 ∧ cutoff 0 route (raw 0 0) = 0 := by
  norm_num [boundedRoutedBinCutoff, routedBinCutoff, Cslib.binWeight,
    switch, scales, route, CorrectionRowRecipe.residual, base, correction, Fin.sum_univ_two]

-- Fine bins keep their original upper support: oversized entries vanish rather than clipping.
example : cutoff 1 route (raw 1 0) = 0 := by
  norm_num [boundedRoutedBinCutoff, routedBinCutoff, Cslib.binWeight,
    switch, scales, route, CorrectionRowRecipe.residual, base, correction, Fin.sum_univ_two]

private abbrev full (_ : Unit) (_ : Fin 2) : Prop := True
private noncomputable def prep (_ : Unit × Unit) : Matrix (Fin 2) (Fin 2) ℝ :=
  of fun x y => if x = y then 20 else -7

-- A negative preparation estimate clips the denominator to 1/2; a zero raw entry stays zero.
example : DenseRowRecipe.normalized (cutoff 0 route) (fun _ => 1) 1 1
    full full full raw prep ((), ()) 1 0 = 9 / 2 := by
  norm_num [DenseRowRecipe.normalized, CorrectionRowRecipe.normalizer, full, prep,
    boundedRoutedBinCutoff, routedBinCutoff, Cslib.binWeight, rowGate,
    switch, scales, route, CorrectionRowRecipe.residual, base, correction, Fin.sum_univ_two]

example : DenseRowRecipe.normalized (cutoff 0 route) (fun _ => 1) 1 1
    full full full raw prep ((), ()) 0 0 = 0 := by
  norm_num [DenseRowRecipe.normalized, boundedRoutedBinCutoff, routedBinCutoff,
    CorrectionRowRecipe.residual, base, correction, Fin.sum_univ_two]

-- The row gate sees the original oversized 100. Scalar top clipping cannot open this gate.
example : DenseRowRecipe.normalized (cutoff 0 route) (fun r => if r ≤ 4 then 1 else 0) 1 1
    full full full raw prep ((), ()) 1 0 = 0 := by
  norm_num [DenseRowRecipe.normalized, rowGate, kthLargest, full,
    CorrectionRowRecipe.residual, base, correction, Fin.sum_univ_two,
    Fin.univ_succ, filter_insert, filter_singleton]

-- The actual evaluator substitutes the signed child functions before preparing the row.
example : ResidualBinTask.value switch scales 3 0 route (fun d => if 0 < d then 1 else 0)
    (fun _ => 1) 1 full full full (fun _ => base) (fun _ => correction) (fun _ => correction)
    (fun _ => 0) prep .preparation ((), ()) 0 1 = 0 := by
  norm_num [ResidualBinTask.value, DenseRowRecipe.preparation, atomPrep, rowGate,
    scales, CorrectionRowRecipe.residual, base, correction, Fin.sum_univ_two]

example : ResidualBinTask.value switch scales 3 0 route (fun _ => 1)
    (fun _ => 1) 1 full full full (fun _ => base) (fun _ => correction) (fun _ => correction)
    (fun _ => 0) prep .normalized ((), ()) 1 0 = 9 / 2 := by
  norm_num [ResidualBinTask.value, DenseRowRecipe.normalized, CorrectionRowRecipe.normalizer,
    full, prep, boundedRoutedBinCutoff, routedBinCutoff, Cslib.binWeight, rowGate,
    switch, scales, route, CorrectionRowRecipe.residual, base, correction, Fin.sum_univ_two]

-- A distinct left child must not be replaced by the negative endpoint correction.
-- Reusing the negative correction as the left factor would add 300 at (0,0).
example : ResidualBinTask.value switch scales 3 0 route (fun _ => 1)
    (fun _ => 1) 1 full full full (fun _ => base) (fun _ => correction)
    (fun _ => 0) (fun _ => base) prep .raw ((), ()) 0 0 = 0 := by
  norm_num [ResidualBinTask.value, CorrectionRowRecipe.residual, base, correction,
    Fin.sum_univ_two]

end ComplexityTests.SignedResidualBins
