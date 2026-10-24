/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Layouts.Gaussian.Straddle
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The Gaussian coefficient and its numerical bound

The cubic layout coefficient of Gaussian edge scores is
`p = (3 / (2π)) arccos ((1 + 2√2)/4) ≈ 0.14035`, the straddling bound at the limiting adjacent
correlation `2√2/3` (`Cslib.Circuits.Frontier.Gaussian.gaussianCoefficient_eq`). It is positive,
and the circuit coefficient `1 + 1 / (2p) = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625` is at
least `114/25 = 4.56` (`Cslib.Circuits.Frontier.Gaussian.circuitCoefficient_ge_456`), by
rational bounds on `√2`, `cos` and `π`.

## Main definitions

* `Cslib.Circuits.Frontier.Gaussian.gaussianCoefficient`: the coefficient `p`.

## Main results

* `Cslib.Circuits.Frontier.Gaussian.gaussianCoefficient_pos`: `p > 0`.
* `Cslib.Circuits.Frontier.Gaussian.one_add_inv_two_mul_gaussianCoefficient`: the circuit
  coefficient `1 + 1 / (2p)`.
* `Cslib.Circuits.Frontier.Gaussian.circuitCoefficient_ge_456249`: the circuit coefficient is at
  least `456249/100000 = 4.56249`.
* `Cslib.Circuits.Frontier.Gaussian.circuitCoefficient_ge_456`: the circuit coefficient is at
  least `114/25 = 4.56`.
-/

@[expose] public section

open Real

namespace Cslib.Circuits.Frontier.Gaussian

/-- The cubic layout coefficient of Gaussian edge scores, `(3 / (2π)) arccos ((1 + 2√2)/4)`. -/
noncomputable def gaussianCoefficient : ℝ :=
  3 / (2 * π) * arccos ((1 + 2 * √2) / 4)

/-- The Gaussian coefficient is the straddling bound at the limiting correlation `2√2/3`. -/
theorem gaussianCoefficient_eq : gaussianCoefficient = straddleBound (2 * √2 / 3) := by
  rw [gaussianCoefficient, straddleBound]
  congr 2
  ring

/-- A crude lower bound, `p ≥ 1/20`, from `cos (π/30) ≥ (1 + 2√2)/4`. -/
theorem gaussianCoefficient_ge : 1 / 20 ≤ gaussianCoefficient := by
  have hsqrt : √2 < 71 / 50 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hpi4 := pi_le_four
  have hθ : π / 30 ≤ arccos ((1 + 2 * √2) / 4) := by
    have hcos : (1 + 2 * √2) / 4 ≤ cos (π / 30) := by
      have := one_sub_sq_div_two_le_cos (x := π / 30)
      have hsq : (π / 30) ^ 2 ≤ (4 / 30) ^ 2 := by gcongr
      linarith
    calc π / 30 = arccos (cos (π / 30)) :=
          (arccos_cos (by positivity) (by linarith [pi_pos])).symm
      _ ≤ _ := arccos_le_arccos hcos
  unfold gaussianCoefficient
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [pi_pos]

/-- The Gaussian layout coefficient `gaussianCoefficient` is positive. -/
theorem gaussianCoefficient_pos : 0 < gaussianCoefficient :=
  lt_of_lt_of_le (by norm_num) gaussianCoefficient_ge

/-- The circuit coefficient `1 + 1 / (2p)` of the cubic coefficient `p`. -/
theorem one_add_inv_two_mul_gaussianCoefficient :
    1 + 1 / (2 * gaussianCoefficient) = 1 + π / (3 * arccos ((1 + 2 * √2) / 4)) := by
  have hsqrt : √2 < 3 / 2 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
  have h : 0 < arccos ((1 + 2 * √2) / 4) := arccos_pos.mpr (by linarith)
  unfold gaussianCoefficient
  congr 1
  field_simp

private theorem cos_two_mul_le {x u v : ℝ} (hlo : x ^ 2 ≤ 2) (hu : cos x ≤ u)
    (hv : 2 * u ^ 2 - 1 ≤ v) : cos (2 * x) ≤ v := by
  have hnonneg : 0 ≤ cos x := by linarith [one_sub_sq_div_two_le_cos (x := x)]
  have hsq := pow_le_pow_left₀ hnonneg hu 2
  rw [cos_two_mul]
  linarith [hsq]

/-- **The sharpened numerical bound.** The circuit coefficient
`1 + π / (3 arccos ((1 + 2√2)/4))` is at least `456249/100000 = 4.56249`.

With `θ = arccos ((1 + 2√2)/4) = 0.29395038…`, the bound `θ ≤ 0.2939509` holds by bounding the
cosine at `0.2939509 / 32` via `cos_bound` and doubling five times:
`cos (0.2939509) ≤ 0.9571067065 < 0.95710678 ≤ (1 + 2√2)/4`. Then
`π / (3 · 0.2939509) > 3.1415926 / 0.8818527 > 3.56249`. -/
theorem circuitCoefficient_ge_456249 :
    (456249 / 100000 : ℝ) ≤ 1 + π / (3 * arccos ((1 + 2 * √2) / 4)) := by
  have hsqrt : (141421356 : ℝ) / 100000000 < √2 := (lt_sqrt (by norm_num)).mpr (by norm_num)
  have hsqrt' : √2 < 3 / 2 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
  have ha : 0 < arccos ((1 + 2 * √2) / 4) := arccos_pos.mpr (by linarith)
  have hcos : cos (2939509 / 10000000) ≤ (1 + 2 * √2) / 4 := by
    have hb := cos_bound (x := 2939509 / 320000000) (by norm_num)
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2939509 / 320000000)] at hb
    have h0 : cos (2939509 / 320000000) ≤ 999957809389 / 1000000000000 := by
      linarith [(abs_le.mp hb).2]
    have h1 := cos_two_mul_le (by norm_num) h0
      (v := 999831241117 / 1000000000000) (by norm_num)
    have h2 := cos_two_mul_le (by norm_num) h1
      (v := 249831255357 / 250000000000) (by norm_num)
    have h3 := cos_two_mul_le (by norm_num) h2
      (v := 199460199381 / 200000000000) (by norm_num)
    have h4 := cos_two_mul_le (by norm_num) h3
      (v := 123652319607 / 125000000000) (by norm_num)
    have h5 := cos_two_mul_le (by norm_num) h4
      (v := 957106706457 / 1000000000000) (by norm_num)
    norm_num only at h5
    linarith [h5, hsqrt]
  have hangle : arccos ((1 + 2 * √2) / 4) ≤ 2939509 / 10000000 :=
    (arccos_le_arccos hcos).trans_eq (arccos_cos (by norm_num) (by linarith [pi_gt_d20]))
  have hdiv : (356249 / 100000 : ℝ) ≤ π / (3 * arccos ((1 + 2 * √2) / 4)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [pi_gt_d20, hangle]
  linarith

/-- **The numerical bound.** The circuit coefficient `1 + π / (3 arccos ((1 + 2√2)/4))` is at
least `114/25 = 4.56`. -/
theorem circuitCoefficient_ge_456 :
    (114 / 25 : ℝ) ≤ 1 + π / (3 * arccos ((1 + 2 * √2) / 4)) :=
  le_trans (by norm_num) circuitCoefficient_ge_456249

end Cslib.Circuits.Frontier.Gaussian
