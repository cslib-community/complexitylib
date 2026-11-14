/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Cauchy–Schwarz for real integrals and integrability of moments

The **Cauchy–Schwarz inequality** `(∫ f g)² ≤ (∫ f²) (∫ g²)` for real functions whose squares and
product are integrable (`MeasureTheory.sq_integral_mul_le`). Unlike Mathlib's Hölder inequality
`integral_mul_le_Lp_mul_Lq_of_nonneg`, it needs no sign condition and is stated with natural squares
rather than real powers and roots. The proof is the discriminant argument: `t ↦ ∫ (t f - g)²` is a
nonnegative quadratic polynomial.

For a real random variable in `Lⁿ`, the moments `E[zʲ]` and absolute moments `E[|z|ʲ]` of order
`j ≤ n` are integrable under a finite measure (`MeasureTheory.integrable_pow_of_memLp`,
`MeasureTheory.integrable_abs_pow_of_memLp`). By Cauchy–Schwarz, the expectations of a `K`-Lipschitz
function of two random variables in `L²` differ by at most `K` times their `L²` distance
(`LipschitzWith.abs_integral_comp_sub_le_sqrt`).

## Main results

* `MeasureTheory.sq_integral_mul_le`: Cauchy–Schwarz, `(∫ f g)² ≤ (∫ f²) (∫ g²)`.
* `MeasureTheory.integrable_pow_of_memLp`: `z ∈ Lⁿ` and `j ≤ n` give `zʲ` integrable.
* `MeasureTheory.integrable_abs_pow_of_memLp`: `z ∈ Lⁿ` and `j ≤ n` give `|z|ʲ` integrable.
* `LipschitzWith.abs_integral_comp_sub_le_sqrt`: for `K`-Lipschitz `ψ` and `X`, `Y` in `L²`,
  `|E[ψ(X)] - E[ψ(Y)]| ≤ K √E[(X - Y)²]`.
-/

public section

namespace MeasureTheory

/-- **Cauchy–Schwarz** for real integrals: `(∫ f g)² ≤ (∫ f²) (∫ g²)`. -/
theorem sq_integral_mul_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f g : Ω → ℝ}
    (hf : Integrable (fun x => f x ^ 2) P) (hg : Integrable (fun x => g x ^ 2) P)
    (hfg : Integrable (fun x => f x * g x) P) :
    (∫ x, f x * g x ∂P) ^ 2 ≤ (∫ x, f x ^ 2 ∂P) * ∫ x, g x ^ 2 ∂P := by
  have h (t : ℝ) : 0 ≤ (∫ x, f x ^ 2 ∂P) * (t * t) + (-2 * ∫ x, f x * g x ∂P) * t +
      ∫ x, g x ^ 2 ∂P := by
    have h1 : ∫ x, (t * f x - g x) ^ 2 ∂P =
        ∫ x, ((t * t) * f x ^ 2 + (-2 * t) * (f x * g x) + g x ^ 2) ∂P := by
      congr 1 with x : 1; ring
    have h2 : ∫ x, (t * f x - g x) ^ 2 ∂P = (∫ x, f x ^ 2 ∂P) * (t * t) +
        (-2 * ∫ x, f x * g x ∂P) * t + ∫ x, g x ^ 2 ∂P := by
      rw [h1, integral_add (f := fun x => t * t * f x ^ 2 + -2 * t * (f x * g x))
        ((hf.const_mul _).add (hfg.const_mul _)) hg,
        integral_add (f := fun x => t * t * f x ^ 2) (g := fun x => -2 * t * (f x * g x))
        (hf.const_mul _) (hfg.const_mul _), integral_const_mul, integral_const_mul]
      ring
    rw [← h2]
    exact integral_nonneg fun x => sq_nonneg _
  have := discrim_le_zero h
  rw [discrim] at this
  nlinarith

/-- Moments of order at most `n` of a real random variable in `Lⁿ` are integrable. -/
theorem integrable_pow_of_memLp {μ : Measure ℝ} [IsFiniteMeasure μ] {n : ℕ} (h : MemLp id n μ)
    {j : ℕ} (hj : j ≤ n) : Integrable (fun s => s ^ j) μ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  have h' : MemLp id (j : ENNReal) μ := h.mono_exponent (by exact_mod_cast hj)
  refine (h'.integrable_norm_pow hj0.ne').mono' (by fun_prop) (ae_of_all _ fun s => ?_)
  simp [norm_pow]

/-- Absolute moments of order at most `n` of a real random variable in `Lⁿ` are integrable. -/
theorem integrable_abs_pow_of_memLp {μ : Measure ℝ} [IsFiniteMeasure μ] {n : ℕ}
    (h : MemLp id n μ) {j : ℕ} (hj : j ≤ n) : Integrable (fun s => |s| ^ j) μ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  have h' : MemLp id (j : ENNReal) μ := h.mono_exponent (by exact_mod_cast hj)
  simpa using h'.integrable_norm_pow hj0.ne'

/-- For `K`-Lipschitz `ψ` and `X`, `Y` in `L²` on a probability space,
`|E[ψ(X)] - E[ψ(Y)]| ≤ K √E[(X - Y)²]`, by Cauchy–Schwarz. -/
theorem _root_.LipschitzWith.abs_integral_comp_sub_le_sqrt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {ψ : ℝ → ℝ} {K : NNReal} (hψ : LipschitzWith K ψ)
    {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    |∫ ω, ψ (X ω) ∂P - ∫ ω, ψ (Y ω) ∂P| ≤ K * √(∫ ω, (X ω - Y ω) ^ 2 ∂P) := by
  have hlip (a b : ℝ) : |ψ a - ψ b| ≤ K * |a - b| := by
    simpa [Real.dist_eq] using hψ.dist_le_mul a b
  have hI {U : Ω → ℝ} (hU : MemLp U 2 P) : Integrable (fun ω => ψ (U ω)) P := by
    refine Integrable.mono' (((hU.integrable one_le_two).norm.const_mul K).add
      (integrable_const |ψ 0|)) (hψ.continuous.comp_aestronglyMeasurable hU.aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    have h := hlip (U ω) 0
    rw [sub_zero] at h
    simp only [Pi.add_apply, Real.norm_eq_abs]
    linarith [abs_sub_abs_le_abs_sub (ψ (U ω)) (ψ 0)]
  have hD : MemLp (fun ω => X ω - Y ω) 2 P := hX.sub hY
  have hDa : Integrable (fun ω => |X ω - Y ω|) P := (hD.integrable one_le_two).abs
  have hCS : ∫ ω, |X ω - Y ω| ∂P ≤ √(∫ ω, (X ω - Y ω) ^ 2 ∂P) := by
    refine Real.le_sqrt_of_sq_le ?_
    have h := sq_integral_mul_le (P := P)
      (f := fun ω => |X ω - Y ω|) (g := fun _ => 1)
      (by simpa only [sq_abs] using hD.integrable_sq) (integrable_const _) (by simpa using hDa)
    simpa only [mul_one, sq_abs, one_pow, integral_const, probReal_univ, smul_eq_mul] using h
  rw [← integral_sub (hI hX) (hI hY)]
  calc |∫ ω, (ψ (X ω) - ψ (Y ω)) ∂P| ≤ ∫ ω, |ψ (X ω) - ψ (Y ω)| ∂P :=
        abs_integral_le_integral_abs
    _ ≤ ∫ ω, K * |X ω - Y ω| ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (hDa.const_mul _)
          (ae_of_all _ fun ω => hlip _ _)
    _ = K * ∫ ω, |X ω - Y ω| ∂P := integral_const_mul _ _
    _ ≤ K * √(∫ ω, (X ω - Y ω) ^ 2 ∂P) := by gcongr

end MeasureTheory
