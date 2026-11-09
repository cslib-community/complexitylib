/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.CenteredBinomial
public import Complexity.Languages.Probabilistic.Concentration
import Complexity.Probability.PMF.Event

/-!
# Concentration of the centered-binomial program

The actual sampler subtracts two independent counts of `η` fair bits. If the difference has
magnitude at least `B`, one count deviates from its mean by at least `B/2`. The existing count
bound and a union bound give `4 exp (-B²/(2η))`. This original supporting corollary is not an
optimal centered-binomial tail estimate. The public bound requires positive width; width zero
already reduces to the deterministic program `pure 0`.

## Main results

* `sampleCenteredBinomial_tail_le`: a non-strict magnitude tail of the actual program.
* `sampleCenteredBinomial_strict_tail_le`: the corresponding strict tail bound.
-/

public section

namespace Cslib.ProbComp

open Probability

/-- A non-strict magnitude tail of the actual two-count sampler. The cutoff is real and
nonnegative; integer endpoint atoms are included. The factor-four estimate is not optimal. -/
theorem sampleCenteredBinomial_tail_le {η : ℕ} (hη : 0 < η) {B : ℝ} (hB : 0 ≤ B) :
    (eval (sampleCenteredBinomial η)).toOuterMeasure {z | B ≤ |(z : ℝ)|} ≤
      ENNReal.ofReal (4 * Real.exp (-B ^ 2 / (2 * η))) := by
  let μ := eval (OracleComp.countTrue η (uniform Bool))
  let C := 2 * Real.exp (-B ^ 2 / (2 * η))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hcount : μ.toOuterMeasure {a | B / 2 ≤ |(a : ℝ) - η / 2|} ≤
      ENNReal.ofReal C := by
    rw [ENNReal.le_ofReal_iff_toReal_le (PMF.toOuterMeasure_ne_top _ _) hC]
    have h := countTrue_deviation η (uniform Bool) (ε := B / 2) (by positivity)
    have hmean : (eval (uniform Bool) true).toReal = 1 / 2 := by
      norm_num [eval_uniform, PMF.uniformOfFintype_apply]
    rw [hmean] at h
    have hexponent : -2 * (B / 2) ^ 2 / (η : ℝ) = -B ^ 2 / (2 * η) := by
      field_simp
    simpa only [mul_one_div, hexponent] using h
  have hlaw : eval (sampleCenteredBinomial η) =
      μ.bind (fun a => μ.map (fun b : ℕ => (a : ℤ) - (b : ℤ))) := by
    simp [sampleCenteredBinomial, μ, eval_bind]
  rw [hlaw]
  calc
    _ ≤ μ.toOuterMeasure {a | |(a : ℝ) - η / 2| < B / 2}ᶜ + ENNReal.ofReal C := by
      apply PMF.toOuterMeasure_bind_failure_le
      intro a _ ha
      change |(a : ℝ) - η / 2| < B / 2 at ha
      rw [PMF.toOuterMeasure_map_apply]
      refine (μ.toOuterMeasure.mono ?_).trans hcount
      intro b hb
      change B ≤ |(((a : ℤ) - b : ℤ) : ℝ)| at hb
      push_cast at hb
      change B / 2 ≤ |(b : ℝ) - η / 2|
      by_contra hn
      have hnb := lt_of_not_ge hn
      have htri : |(a : ℝ) - b| ≤ |(a : ℝ) - η / 2| + |(b : ℝ) - η / 2| := by
        convert abs_sub ((a : ℝ) - η / 2) ((b : ℝ) - η / 2) using 1; congr 1; ring
      linarith
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal C := by
      apply add_le_add _ le_rfl
      simpa only [Set.compl_ofPred, not_lt] using hcount
    _ = _ := by
      rw [← ENNReal.ofReal_add hC hC]
      congr 1
      dsimp only [C]
      ring

/-- A strict tail excludes atoms exactly at the cutoff and is bounded by the non-strict tail.
In particular, equality with the support radius must not be treated as a strict tail. -/
theorem sampleCenteredBinomial_strict_tail_le {η : ℕ} (hη : 0 < η) {B : ℝ} (hB : 0 ≤ B) :
    (eval (sampleCenteredBinomial η)).toOuterMeasure {z | B < |(z : ℝ)|} ≤
      ENNReal.ofReal (4 * Real.exp (-B ^ 2 / (2 * η))) := by
  calc
    _ ≤ (eval (sampleCenteredBinomial η)).toOuterMeasure {z | B ≤ |(z : ℝ)|} := by
      apply (eval (sampleCenteredBinomial η)).toOuterMeasure.mono
      intro z hz
      exact le_of_lt (show B < |(z : ℝ)| from hz)
    _ ≤ _ := sampleCenteredBinomial_tail_le hη hB

end Cslib.ProbComp
