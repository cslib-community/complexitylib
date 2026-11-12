/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Probability.EventCount
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic.NormNum

/-!
# Expected event counts

The empty list has expectation zero even on an infinite sample space. Repeating the same fair-coin
event twice gives expectation one, with no independence between the two occurrences. The measure
API also works for a measure of total mass two, retaining multiplicity in its bound.
-/

namespace CslibFrontierTests.EventCount

open Cslib.Probability MeasureTheory
open scoped ENNReal

-- The PMF interface does not introduce a finite or measurable sample-space requirement.
example (μ : PMF ℕ) :
    ∑' ω, μ ω * ((([] : List ℕ).countP fun x => decide (ω = x) : ℕ) : ℝ≥0∞) ≤ 0 := by
  have h := PMF.tsum_mul_countP_le μ (fun ω x => ω = x) 0 [] (by simp)
  simpa only [List.length_nil, Nat.cast_zero, zero_mul] using h

-- Both list entries describe the same event, so they are completely dependent.
example :
    ∑' ω : Bool, PMF.uniformOfFintype Bool ω *
      ((([false, false] : List Bool).countP fun x => decide (ω = x) : ℕ) : ℝ≥0∞) ≤ 1 := by
  have h := PMF.tsum_mul_countP_le (PMF.uniformOfFintype Bool)
    (fun ω x : Bool => ω = x) (1 / 2) [false, false] (by
      intro x _
      change (PMF.uniformOfFintype Bool).toOuterMeasure {x} ≤ 1 / 2
      rw [PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply,
        Fintype.card_bool, Nat.cast_ofNat, one_div])
  refine h.trans ?_
  change (2 : ℝ≥0∞) * (1 / 2) ≤ 1
  rw [one_div, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

-- The upper bound above is attained; treating the list as a set would incorrectly halve it.
example :
    ∑' ω : Bool, PMF.uniformOfFintype Bool ω *
      ((([false, false] : List Bool).countP fun x => decide (ω = x) : ℕ) : ℝ≥0∞) = 1 := by
  rw [tsum_fintype, Fintype.sum_bool]
  norm_num [PMF.uniformOfFintype_apply]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

-- The general measure statement requires neither probability normalization nor independence.
example :
    Measurable (fun ω : Bool =>
      ((([true, true] : List Bool).countP fun x => decide (ω = x) : ℕ) : ℝ≥0∞)) ∧
      (∫⁻ ω : Bool,
        ((([true, true] : List Bool).countP fun x => decide (ω = x) : ℕ) : ℝ≥0∞)
          ∂(Measure.dirac true + Measure.dirac true)) ≤ 4 := by
  have h := measurable_and_lintegral_countP_le (Measure.dirac true + Measure.dirac true)
    (fun ω x : Bool => ω = x) 2 [true, true]
    (fun _ _ => MeasurableSet.of_discrete) (by
      intro x hx
      have hx' : x = true := by simpa using hx
      subst x
      simp
      norm_num)
  refine ⟨h.1, h.2.trans ?_⟩
  change (2 : ℝ≥0∞) * 2 ≤ 4
  norm_num

end CslibFrontierTests.EventCount
