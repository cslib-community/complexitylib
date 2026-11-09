/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Sensitivity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.Bridge
import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.Separation

/-!
# A superquadratic separation of block sensitivity from sensitivity

Every Boolean function satisfies `s(f) ≤ bs(f)` [Nisan1991], and Huang's theorem [Huang2019]
bounds block sensitivity polynomially in sensitivity
(`QueryComplexity.blockSensitivity_le_two_mul_sensitivity_pow_four`). Rubinstein's function shows
that `bs(f)` can be quadratic in `s(f)` [Rubinstein1995]. OpenAI's construction
[OpenAI2026Sensitivity] goes beyond the square: for every constant `C` there is a nonconstant
Boolean function `f` with `bs(f) > C · s(f)²`, and there is a family whose block sensitivity is at
least a fixed power `α > 2` of its sensitivity.

Sensitivity here is CSLib's `BitString.sensitivity`, the maximum number of sensitive coordinates
at a single input (not average sensitivity), and block sensitivity is CSLib's
`QueryComplexity.blockSensitivity`. The `blockSensitivityAt` statements bound the block
sensitivity at the all-false input, where the function takes the value `false`. The construction
is carried out in the `Internal` modules with measures over arbitrary finite coordinate types;
`Internal.Bridge` identifies those with CSLib's measures on `Fin n`.

Since `bs(f) ≤ C(f) ≤ D(f)`, the same functions separate certificate complexity and deterministic
decision-tree complexity from squared sensitivity. These consequences are short deductions from
the separation.

## Main results

* `QueryComplexity.exists_two_pow_div_le_blockSensitivityAt_div_sensitivity_sq`: for every
  `d ≥ 1` there is a nonconstant `f` with `bs(f, 0) / s(f) ^ 2 ≥ 2 ^ d / (4 (d + 2) ^ 2)`.
* `QueryComplexity.exists_mul_sensitivity_sq_lt_blockSensitivityAt`: for every `C` there is a
  nonconstant `f` with `f 0 = false` and `C * s(f) ^ 2 < bs(f, 0)`.
* `QueryComplexity.exists_mul_sensitivity_sq_lt_blockSensitivity`: for every `C` there is a
  nonconstant `f` with `C * s(f) ^ 2 < bs(f)`.
* `QueryComplexity.exists_sensitivity_rpow_le_blockSensitivityAt`: a family with
  `s(f) ^ α ≤ bs(f)` for a fixed `α > 2` and unbounded block sensitivity.
* `QueryComplexity.exists_mul_sensitivity_sq_lt_certificateComplexity`: the same separation for
  certificate complexity.
* `DecisionTree.exists_mul_sensitivity_sq_lt_complexity`,
  `DecisionTree.exists_sensitivity_rpow_le_complexity`: the same separations for deterministic
  decision-tree complexity.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/Separation.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
* [N. Nisan, *CREW PRAMs and decision trees*][Nisan1991]
* [D. Rubinstein, *Sensitivity vs. block sensitivity of Boolean functions*][Rubinstein1995]
* [H. Huang, *Induced subgraphs of hypercubes and a proof of the Sensitivity
  Conjecture*][Huang2019]
-/

@[expose] public section

namespace Cslib

open BitString Filter

namespace QueryComplexity

/-- **Quantitative superquadratic separation**: for every `d ≥ 1` there is a nonconstant Boolean
function `f` with `f 0 = false` and `bs(f, 0) / s(f) ^ 2 ≥ 2 ^ d / (4 (d + 2) ^ 2)`. -/
theorem exists_two_pow_div_le_blockSensitivityAt_div_sensitivity_sq (d : ℕ) (hd : 1 ≤ d) :
    ∃ (n : ℕ) (f : BooleanFunction n), 0 < n ∧ f (fun _ => false) = false ∧
      (∃ x y, f x ≠ f y) ∧
      (2 : ℝ) ^ d / (4 * ((d : ℝ) + 2) ^ 2) ≤
        (blockSensitivityAt f (fun _ => false) : ℝ) / (sensitivity f : ℝ) ^ 2 := by
  obtain ⟨n, f, hn, hf, hnc, h⟩ := SensitivitySeparation.Internal.quantitative_separation d hd
  refine ⟨n, f, hn, hf, hnc, ?_⟩
  rwa [← SensitivitySeparation.Internal.sensitivity_eq_bitString_sensitivity,
    ← SensitivitySeparation.Internal.blockSensitivityAt_eq_queryComplexity_blockSensitivityAt]

/-- For every `C` there is a nonconstant Boolean function `f` with `f 0 = false` and
`C * s(f) ^ 2 < bs(f, 0)`. -/
theorem exists_mul_sensitivity_sq_lt_blockSensitivityAt (C : ℝ) :
    ∃ (n : ℕ) (f : BooleanFunction n), 0 < n ∧ f (fun _ => false) = false ∧
      (∃ x y, f x ≠ f y) ∧
      C * (sensitivity f : ℝ) ^ 2 < (blockSensitivityAt f (fun _ => false) : ℝ) := by
  obtain ⟨n, f, hn, hf, hnc, h⟩ :=
    SensitivitySeparation.Internal.unbounded_quadratic_separation C
  refine ⟨n, f, hn, hf, hnc, ?_⟩
  rwa [← SensitivitySeparation.Internal.sensitivity_eq_bitString_sensitivity,
    ← SensitivitySeparation.Internal.blockSensitivityAt_eq_queryComplexity_blockSensitivityAt]

/-- **Block sensitivity is not quadratically bounded by sensitivity**: for every `C` there is a
nonconstant Boolean function `f` with `C * s(f) ^ 2 < bs(f)`. -/
theorem exists_mul_sensitivity_sq_lt_blockSensitivity (C : ℝ) :
    ∃ (n : ℕ) (f : BooleanFunction n), 0 < n ∧ (∃ x y, f x ≠ f y) ∧
      C * (sensitivity f : ℝ) ^ 2 < (blockSensitivity f : ℝ) := by
  obtain ⟨n, f, hn, -, hnc, h⟩ := exists_mul_sensitivity_sq_lt_blockSensitivityAt C
  exact ⟨n, f, hn, hnc, h.trans_le (mod_cast blockSensitivityAt_le_blockSensitivity f _)⟩

/-- **Fixed-power separation**: for some `α > 2` there is a family of nonconstant Boolean
functions `F m` with `F m 0 = false` and `s(F m) ^ α ≤ bs(F m, 0)`, whose block sensitivity at
the all-false input tends to infinity. -/
theorem exists_sensitivity_rpow_le_blockSensitivityAt :
    ∃ α : ℝ, 2 < α ∧ ∃ (n : ℕ → ℕ) (F : ∀ m, BooleanFunction (n m)),
      (∀ m, 0 < n m ∧ F m (fun _ => false) = false ∧ (∃ x y, F m x ≠ F m y) ∧
        (sensitivity (F m) : ℝ) ^ α ≤ (blockSensitivityAt (F m) (fun _ => false) : ℝ)) ∧
      Tendsto (fun m => (blockSensitivityAt (F m) (fun _ => false) : ℝ)) atTop atTop := by
  obtain ⟨α, hα, n, F, hall, hlim⟩ := SensitivitySeparation.Internal.fixed_power_separation
  refine ⟨α, hα, n, F, fun m => ?_, ?_⟩
  · obtain ⟨hn, hf, hnc, hpow⟩ := hall m
    refine ⟨hn, hf, hnc, ?_⟩
    rwa [← SensitivitySeparation.Internal.sensitivity_eq_bitString_sensitivity,
      ← SensitivitySeparation.Internal.blockSensitivityAt_eq_queryComplexity_blockSensitivityAt]
  · simpa only
      [SensitivitySeparation.Internal.blockSensitivityAt_eq_queryComplexity_blockSensitivityAt]
      using hlim

/-- Certificate complexity is not quadratically bounded by sensitivity: for every `C` there is a
nonconstant Boolean function `f` with `C * s(f) ^ 2 < C(f)`. -/
theorem exists_mul_sensitivity_sq_lt_certificateComplexity (C : ℝ) :
    ∃ (n : ℕ) (f : BooleanFunction n), 0 < n ∧ (∃ x y, f x ≠ f y) ∧
      C * (sensitivity f : ℝ) ^ 2 < (certificateComplexity f : ℝ) := by
  obtain ⟨n, f, hn, hnc, h⟩ := exists_mul_sensitivity_sq_lt_blockSensitivity C
  exact ⟨n, f, hn, hnc, h.trans_le (mod_cast blockSensitivity_le_certificateComplexity f)⟩

end QueryComplexity

namespace DecisionTree

open QueryComplexity

/-- Deterministic decision-tree complexity is not quadratically bounded by sensitivity: for every
`C` there is a nonconstant Boolean function `f` with `C * s(f) ^ 2 < D(f)`. -/
theorem exists_mul_sensitivity_sq_lt_complexity (C : ℝ) :
    ∃ (n : ℕ) (f : BooleanFunction n), 0 < n ∧ (∃ x y, f x ≠ f y) ∧
      C * (sensitivity f : ℝ) ^ 2 < (complexity f : ℝ) := by
  obtain ⟨n, f, hn, hnc, h⟩ := exists_mul_sensitivity_sq_lt_certificateComplexity C
  exact ⟨n, f, hn, hnc, h.trans_le (mod_cast certificateComplexity_le_complexity f)⟩

/-- Fixed-power separation of decision-tree complexity from sensitivity: for some `α > 2` there
is a family of nonconstant Boolean functions `F m` with `s(F m) ^ α ≤ D(F m)` and
`D(F m) → ∞`. -/
theorem exists_sensitivity_rpow_le_complexity :
    ∃ α : ℝ, 2 < α ∧ ∃ (n : ℕ → ℕ) (F : ∀ m, BooleanFunction (n m)),
      (∀ m, 0 < n m ∧ (∃ x y, F m x ≠ F m y) ∧
        (sensitivity (F m) : ℝ) ^ α ≤ (complexity (F m) : ℝ)) ∧
      Tendsto (fun m => (complexity (F m) : ℝ)) atTop atTop := by
  obtain ⟨α, hα, n, F, hall, hlim⟩ := exists_sensitivity_rpow_le_blockSensitivityAt
  have hle (m : ℕ) : (blockSensitivityAt (F m) (fun _ => false) : ℝ) ≤ complexity (F m) :=
    mod_cast ((blockSensitivityAt_le_blockSensitivity (F m) _).trans
      (blockSensitivity_le_certificateComplexity (F m))).trans
      (certificateComplexity_le_complexity (F m))
  refine ⟨α, hα, n, F, fun m => ?_, tendsto_atTop_mono hle hlim⟩
  obtain ⟨hn, -, hnc, hpow⟩ := hall m
  exact ⟨hn, hnc, hpow.trans (hle m)⟩

end DecisionTree

end Cslib
