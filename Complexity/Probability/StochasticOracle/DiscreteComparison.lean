/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.AdaptiveBinomial
public import Complexity.Probability.PMF.Expect
import Mathlib.Tactic

/-!
# Exact Boolean observations of arbitrary discrete response laws

The comparison variable in [Wang2027], Appendix A.5 (PDF p. 16), is Boolean,
while actual responses and hidden metadata need not have finite alphabets.
These lemmas push forward only that exact indicator. They never replace the
response process or assume independent responses.

## Main results

* `indicator_mean`: exact indicator probability on an unrestricted PMF.
* `binary_mean_upper`, `binary_mean_lower`: conditional monotone binary payoffs.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.DiscreteComparison
open scoped ENNReal
variable {S : Type*}

/-- Expected indicator is its actual Boolean pushforward mass. -/
theorem indicator_mean (μ : PMF S) (event : S → Bool) :
    (∑' s, μ s * (if event s then 1 else 0)) = μ.map event true := by
  rw [← PMF.tsum_map_mul μ event (fun bit => if bit then 1 else 0), tsum_bool]
  simp

private theorem binary_mean (μ : PMF S) (event : S → Bool) (a b : ℝ) :
    (∑' s, μ s * ENNReal.ofReal (if event s then b else a)) =
      μ.map event false * ENNReal.ofReal a + μ.map event true * ENNReal.ofReal b := by
  rw [← PMF.tsum_map_mul μ event (fun bit => ENNReal.ofReal (if bit then b else a)), tsum_bool]
  simp

/-- A conditional indicator upper envelope controls any nonnegative increasing
binary payoff, even with an infinite response alphabet. -/
theorem binary_mean_upper (μ : PMF S) (event : S → Bool) (p a b : ℝ)
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hab : a ≤ b)
    (hprob : (∑' s, μ s * (if event s then 1 else 0)) ≤ ENNReal.ofReal p) :
    (∑' s, μ s * ENNReal.ofReal (if event s then b else a)) ≤
      ENNReal.ofReal ((1 - p) * a + p * b) := by
  rw [binary_mean]
  have hq := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hprob
  rw [indicator_mean, ENNReal.toReal_ofReal hp] at hq
  have hsum := PMF.sum_toReal (μ.map event)
  simp only [Fintype.sum_bool] at hsum
  have hb : 0 ≤ b := ha.trans hab
  have hfin : μ.map event false * ENNReal.ofReal a +
      μ.map event true * ENNReal.ofReal b ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (μ.map event |>.apply_ne_top _) (by simp),
      ENNReal.mul_ne_top (μ.map event |>.apply_ne_top _) (by simp)⟩
  apply (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (μ.map event |>.apply_ne_top _) (by simp))
    (ENNReal.mul_ne_top (μ.map event |>.apply_ne_top _) (by simp))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]
  have ht : 0 ≤ (1 - p) * a + p * b := by
    nlinarith [ENNReal.toReal_nonneg (a := (μ.map event) true)]
  rw [ENNReal.toReal_ofReal ht]
  nlinarith

/-- The corresponding lower envelope for a nonnegative increasing binary payoff. -/
theorem binary_mean_lower (μ : PMF S) (event : S → Bool) (p a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hprob : ENNReal.ofReal p ≤ ∑' s, μ s * (if event s then 1 else 0)) :
    ENNReal.ofReal ((1 - p) * a + p * b) ≤
      ∑' s, μ s * ENNReal.ofReal (if event s then b else a) := by
  rw [binary_mean]
  have hq : p ≤ ((μ.map event) true).toReal := by
    by_cases hp0 : 0 ≤ p
    · rw [indicator_mean] at hprob
      have he := ENNReal.toReal_mono ((μ.map event).apply_ne_top true) hprob
      rwa [ENNReal.toReal_ofReal hp0] at he
    · exact (le_of_not_ge hp0).trans ENNReal.toReal_nonneg
  have hsum := PMF.sum_toReal (μ.map event)
  simp only [Fintype.sum_bool] at hsum
  have hb : 0 ≤ b := ha.trans hab
  have hfin : μ.map event false * ENNReal.ofReal a +
      μ.map event true * ENNReal.ofReal b ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (μ.map event |>.apply_ne_top _) (by simp),
      ENNReal.mul_ne_top (μ.map event |>.apply_ne_top _) (by simp)⟩
  apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin).mp
  by_cases ht : 0 ≤ (1 - p) * a + p * b
  · rw [ENNReal.toReal_ofReal ht, ENNReal.toReal_add
      (ENNReal.mul_ne_top (μ.map event |>.apply_ne_top _) (by simp))
      (ENNReal.mul_ne_top (μ.map event |>.apply_ne_top _) (by simp))]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]
    nlinarith
  · rw [ENNReal.ofReal_of_nonpos (le_of_not_ge ht), ENNReal.toReal_zero]
    exact ENNReal.toReal_nonneg

/-- Nonnegative payoffs remain nonnegative under the existing comparison recurrence. -/
theorem bernoulli_nonneg (p : Set.Icc (0 : ℝ) 1) (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    (turns count : ℕ) : 0 ≤ bernoulliExpectation p f turns count := by
  induction turns generalizing count with
  | zero => exact hf count
  | succ turns ih =>
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr p.2.2) (ih _))
      (mul_nonneg p.2.1 (ih _))

end Cslib.Probability.StochasticOracle.DiscreteComparison
