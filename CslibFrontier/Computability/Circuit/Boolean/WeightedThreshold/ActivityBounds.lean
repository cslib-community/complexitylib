/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.InnerProduct
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Foundations.Data.Nat.Choose.Real

/-!
# Logarithmic size-activity bounds for inner product

A weighted threshold program computing inner product on `m` coordinates per side satisfies
`m / 2 ≤ e * log₂ (exp 1 * q / e)` and `e / exp 1 * 2 ^ (m / (2 * e)) ≤ q`, where
`q` counts the gates and `e` is their maximum activity. The same bounds hold when both quantities
count only input-reading gates. These consequences of the exact binomial-sum bound hold throughout
`e ≤ q`, including activity above half the gate count.

Positive-dimensional inner product requires positive input-reading activity. The numerical
bounds also include zero-dimensional inputs, using the usual total real operations at `e = 0`.
The circuit statements require a gate output. The input-reading bounds exclude gates reading
only earlier gates; the total-gate bounds include them. No restriction on depth or real coefficient
magnitude is imposed.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.inputActivity_pos_of_dotProduct`: positive activity
  when the input on each side has at least one coordinate.
* `Cslib.Circuits.Boolean.WeightedThreshold.le_inputActivity_mul_logb_of_dotProduct`: the
  logarithmic size-activity bound.
* `Cslib.Circuits.Boolean.WeightedThreshold.inputActivity_mul_rpow_le_card_of_dotProduct`: the
  rearranged lower bound on the number of input-reading gates.
* `Cslib.Circuits.Boolean.WeightedThreshold.le_gateActivity_mul_logb_of_dotProduct` and
  `Cslib.Circuits.Boolean.WeightedThreshold.gateActivity_mul_rpow_le_of_dotProduct`: the
  corresponding bounds using all gates and their maximum activity.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Theorem 3.2]
  [ThresholdCircuitRepresentations2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset BitString

variable {n g : ℕ} {ι : Type*} [Fintype ι]

/-- Computing positive-dimensional inner product requires positive input-reading activity. -/
theorem inputActivity_pos_of_dotProduct
    (p : Program signature n g) (split : Fin n ≃ ι ⊕ ι)
    (readout : (Fin g → Bool) → Bool) (hm : 0 < Fintype.card ι)
    (h : ∀ x y, readout (p.eval interpretation (inputOfSplit split x y)) = x ⬝ᵥ y) :
    0 < inputActivity p := by
  by_contra he
  have he0 : inputActivity p = 0 := by omega
  have hsum := two_pow_le_sum_choose_sq_of_dotProduct p split readout h
  have hle : 2 ^ Fintype.card ι ≤ 1 := by simpa [he0] using hsum
  exact (not_le_of_gt (Nat.one_lt_two_pow hm.ne')) hle

/-- The input-reading activity and gate count obey the logarithmic size-activity bound. -/
theorem le_inputActivity_mul_logb_of_dotProduct
    (p : Program signature n g) (split : Fin n ≃ ι ⊕ ι)
    (readout : (Fin g → Bool) → Bool)
    (h : ∀ x y, readout (p.eval interpretation (inputOfSplit split x y)) = x ⬝ᵥ y) :
    (Fintype.card ι : ℝ) / 2 ≤
      inputActivity p * Real.logb 2 (Real.exp 1 * (inputGates p).card / inputActivity p) :=
  le_mul_logb_of_two_pow_le_sum_choose_sq (inputActivity_le_card p)
    (two_pow_le_sum_choose_sq_of_dotProduct p split readout h)

/-- Inner product requires at least `e / exp 1 * 2 ^ (m / (2 * e))` input-reading gates. -/
theorem inputActivity_mul_rpow_le_card_of_dotProduct
    (p : Program signature n g) (split : Fin n ≃ ι ⊕ ι)
    (readout : (Fin g → Bool) → Bool)
    (h : ∀ x y, readout (p.eval interpretation (inputOfSplit split x y)) = x ⬝ᵥ y) :
    inputActivity p / Real.exp 1 *
      (2 : ℝ) ^ ((Fintype.card ι : ℝ) / (2 * inputActivity p)) ≤ (inputGates p).card :=
  mul_rpow_le_of_two_pow_le_sum_choose_sq (inputActivity_le_card p)
    (two_pow_le_sum_choose_sq_of_dotProduct p split readout h)

/-- The logarithmic size-activity bound for a native single-output circuit with a gate output. -/
theorem le_inputActivity_mul_logb_of_circuit_dotProduct
    (c : Circuit signature n 1) (split : Fin n ≃ ι ⊕ ι)
    (houtput : ∃ gate, c.outputs 0 = .gate gate)
    (h : ∀ x y, c.eval interpretation (inputOfSplit split x y) 0 = x ⬝ᵥ y) :
    (Fintype.card ι : ℝ) / 2 ≤ inputActivity c.program *
      Real.logb 2 (Real.exp 1 * (inputGates c.program).card / inputActivity c.program) :=
  le_mul_logb_of_two_pow_le_sum_choose_sq (inputActivity_le_card c.program)
    (two_pow_le_sum_choose_sq_of_circuit_dotProduct c split houtput h)

/-- The rearranged input-reading-gate lower bound for a circuit with a gate output. -/
theorem inputActivity_mul_rpow_le_card_of_circuit_dotProduct
    (c : Circuit signature n 1) (split : Fin n ≃ ι ⊕ ι)
    (houtput : ∃ gate, c.outputs 0 = .gate gate)
    (h : ∀ x y, c.eval interpretation (inputOfSplit split x y) 0 = x ⬝ᵥ y) :
    inputActivity c.program / Real.exp 1 *
      (2 : ℝ) ^ ((Fintype.card ι : ℝ) / (2 * inputActivity c.program)) ≤
        (inputGates c.program).card :=
  mul_rpow_le_of_two_pow_le_sum_choose_sq (inputActivity_le_card c.program)
    (two_pow_le_sum_choose_sq_of_circuit_dotProduct c split houtput h)

/-- The maximum activity across all gates obeys the logarithmic size-activity bound. -/
theorem le_gateActivity_mul_logb_of_dotProduct
    (p : Program signature n g) (split : Fin n ≃ ι ⊕ ι)
    (readout : (Fin g → Bool) → Bool)
    (h : ∀ x y, readout (p.eval interpretation (inputOfSplit split x y)) = x ⬝ᵥ y) :
    (Fintype.card ι : ℝ) / 2 ≤
      gateActivity p * Real.logb 2 (Real.exp 1 * g / gateActivity p) :=
  le_mul_logb_of_two_pow_le_sum_choose_sq (gateActivity_le p)
    (two_pow_le_sum_choose_gateActivity_sq_of_dotProduct p split readout h)

/-- Inner product requires at least `e / exp 1 * 2 ^ (m / (2 * e))` gates at total activity `e`. -/
theorem gateActivity_mul_rpow_le_of_dotProduct
    (p : Program signature n g) (split : Fin n ≃ ι ⊕ ι)
    (readout : (Fin g → Bool) → Bool)
    (h : ∀ x y, readout (p.eval interpretation (inputOfSplit split x y)) = x ⬝ᵥ y) :
    gateActivity p / Real.exp 1 *
      (2 : ℝ) ^ ((Fintype.card ι : ℝ) / (2 * gateActivity p)) ≤ g :=
  mul_rpow_le_of_two_pow_le_sum_choose_sq (gateActivity_le p)
    (two_pow_le_sum_choose_gateActivity_sq_of_dotProduct p split readout h)

/-- The total-gate logarithmic bound for a native single-output circuit with a gate output. -/
theorem le_gateActivity_mul_logb_of_circuit_dotProduct
    (c : Circuit signature n 1) (split : Fin n ≃ ι ⊕ ι)
    (houtput : ∃ gate, c.outputs 0 = .gate gate)
    (h : ∀ x y, c.eval interpretation (inputOfSplit split x y) 0 = x ⬝ᵥ y) :
    (Fintype.card ι : ℝ) / 2 ≤
      gateActivity c.program * Real.logb 2 (Real.exp 1 * c.size / gateActivity c.program) :=
  le_mul_logb_of_two_pow_le_sum_choose_sq (gateActivity_le c.program)
    (two_pow_le_sum_choose_gateActivity_sq_of_circuit_dotProduct c split houtput h)

/-- The rearranged total-gate lower bound for a circuit with a gate output. -/
theorem gateActivity_mul_rpow_le_of_circuit_dotProduct
    (c : Circuit signature n 1) (split : Fin n ≃ ι ⊕ ι)
    (houtput : ∃ gate, c.outputs 0 = .gate gate)
    (h : ∀ x y, c.eval interpretation (inputOfSplit split x y) 0 = x ⬝ᵥ y) :
    gateActivity c.program / Real.exp 1 *
      (2 : ℝ) ^ ((Fintype.card ι : ℝ) / (2 * gateActivity c.program)) ≤ c.size :=
  mul_rpow_le_of_two_pow_le_sum_choose_sq (gateActivity_le c.program)
    (two_pow_le_sum_choose_gateActivity_sq_of_circuit_dotProduct c split houtput h)

end Cslib.Circuits.Boolean.WeightedThreshold
