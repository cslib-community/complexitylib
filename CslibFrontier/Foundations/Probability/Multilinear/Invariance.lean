/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.Multilinear.Bonami
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.Analysis.Calculus.Taylor
import CslibFrontier.Foundations.MeasureTheory.Integral.CauchySchwarz
import CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate

/-!
# The Basic Invariance Principle

Let `F` be a formal multilinear polynomial of degree at most `k`, and let `x = (x₁, …, xₙ)` and
`y = (y₁, …, yₙ)` be sequences of independent random variables, each satisfying Hypothesis 11.65
(`HasInvarianceMoments`: mean `0`, variance `1`, third moment `0`, fourth moment at most `9`). If
`ψ : ℝ → ℝ` is `C⁴` with `‖ψ⁗‖_∞ ≤ C`, then
`|E[ψ(F(x))] - E[ψ(F(y))]| ≤ C / 12 · 9 ^ k · ∑_t Inf_t[F] ^ 2`
(`abs_integral_comp_multilinearEval_sub_le`) [O'Donnell, Section 11.6, Basic Invariance
Principle, equation (11.29)][ODonnell2014]. In particular `F(x)` and `F(y)` are close in
distribution when every coordinate has small influence: if `Var[F] ≤ 1` and every `Inf_t[F] ≤ ε`,
the bound is `C / 12 · k 9 ^ k · ε` (`abs_integral_comp_multilinearEval_sub_le_of_influence_le`,
Corollary 11.67). The typical instance takes `x` uniform `±1` bits and `y` standard Gaussians
(`CslibFrontier.Foundations.BooleanAnalysis.Invariance`).

The proof is Lindeberg's replacement method. The hybrids `Measure.pi (s.piecewise ν μ)` replace the
coordinates in `s` one at a time (`MeasureTheory.abs_integral_pi_sub_le_sum`). Replacing coordinate
`t` writes `F = E_t F + z · D_t F` with `E_t F`, `D_t F` independent of the new coordinate `z`; by
Taylor's theorem to third order, the first three moments of `x_t` and `y_t` agree, so the step costs
at most `C / 24 · (E[x_t⁴] + E[y_t⁴]) · E[(D_t F)⁴] ≤ 3 C / 4 · E[(D_t F)⁴]`
(`HasInvarianceMoments.abs_integral_sub_le`). The Bonami Lemma for the hybrid ensemble
(`integral_multilinearEval_pow_four_le`) bounds `E[(D_t F)⁴] ≤ 9 ^ (k - 1) Inf_t[F] ^ 2`.

With a `C³` test function and a second-order expansion, the same argument gives
`|E[ψ(F(x))] - E[ψ(F(y))]| ≤ C / 3 · 3 ^ k · ∑_t Inf_t[F] ^ (3 / 2)` when `‖ψ‴‖_∞ ≤ C`
(`abs_integral_comp_multilinearEval_sub_le_of_contDiff_three`): the step costs
`C / 6 · (E|x_t|³ + E|y_t|³) · E|D_t F|³`, Cauchy–Schwarz gives `E|z|³ ≤ √(E z² E z⁴) ≤ 3`, and
`E|D_t F|³ ≤ √(E (D_t F)² E (D_t F)⁴) ≤ 3 ^ (k - 1) Inf_t[F] ^ (3 / 2)`. This is the analogue under
Hypothesis 11.65 of [O'Donnell, Remark 11.66][ODonnell2014], which instead assumes the variables
are `(2, 3, ρ)`-hypercontractive with second moment `1` and has the factor `(1 / ρ) ^ (3 k)` in
place of `3 ^ k`; the hypercontractive version (Exercise 11.47) is not formalized here.

## Main results

* `ProbabilityTheory.abs_integral_sub_integral_le_of_moments`: the one-dimensional replacement
  step, for laws with matching moments up to order `n` and a `C^(n+1)` test function.
* `ProbabilityTheory.abs_integral_comp_multilinearEval_sub_le`: the Basic Invariance Principle.
* `ProbabilityTheory.abs_integral_comp_multilinearEval_sub_le_of_influence_le`: Corollary 11.67.
* `ProbabilityTheory.abs_integral_comp_multilinearEval_sub_le_of_contDiff_three`: the `C³` form.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Section 11.6.
-/

public section

open MeasureTheory Finset
open scoped Nat ENNReal

namespace ProbabilityTheory

/-! ### One coordinate -/

/-- **The one-dimensional replacement step.** If the laws `μ` and `ν` have finite moments of order
`n + 1` and the same moments of orders `0, …, n`, and `ψ` is `C^(n+1)` with `|ψ⁽ⁿ⁺¹⁾| ≤ C`, then
for all `a`, `b`, `|E_μ ψ(a + s b) - E_ν ψ(a + s b)|` is at most
`C / (n + 1)! · |b| ^ (n + 1) · (E_μ |s| ^ (n + 1) + E_ν |s| ^ (n + 1))`. -/
theorem abs_integral_sub_integral_le_of_moments {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {n : ℕ} (hμ : MemLp id ((n + 1 : ℕ) : ℝ≥0∞) μ)
    (hν : MemLp id ((n + 1 : ℕ) : ℝ≥0∞) ν)
    (hmom : ∀ j ≤ n, ∫ s, s ^ j ∂μ = ∫ s, s ^ j ∂ν)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (n + 1) ψ) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv (n + 1) ψ y| ≤ C) (a b : ℝ) :
    |∫ s, ψ (a + s * b) ∂μ - ∫ s, ψ (a + s * b) ∂ν| ≤
      C / (n + 1)! * |b| ^ (n + 1) * (∫ s, |s| ^ (n + 1) ∂μ + ∫ s, |s| ^ (n + 1) ∂ν) := by
  set T : ℝ → ℝ := fun s => ∑ j ∈ range (n + 1), iteratedDeriv j ψ a * (s * b) ^ j / (j ! : ℝ)
  set R : ℝ → ℝ := fun s => ψ (a + s * b) - T s
  set K : ℝ := C / (n + 1)! * |b| ^ (n + 1)
  have hR (s : ℝ) : |R s| ≤ K * |s| ^ (n + 1) := by
    calc |R s| ≤ C * |s * b| ^ (n + 1) / (n + 1)! := abs_sub_sum_iteratedDeriv_le hψ hC a (s * b)
      _ = K * |s| ^ (n + 1) := by rw [abs_mul, mul_pow]; ring
  have hψc : Continuous ψ := hψ.continuous
  have hTint {m : Measure ℝ} [IsProbabilityMeasure m] (hm : MemLp id ((n + 1 : ℕ) : ℝ≥0∞) m) :
      Integrable T m ∧ ∫ s, T s ∂m =
        ∑ j ∈ range (n + 1), iteratedDeriv j ψ a * b ^ j / j ! * ∫ s, s ^ j ∂m := by
    have hint (j : ℕ) (hj : j ∈ range (n + 1)) :
        Integrable (fun s => iteratedDeriv j ψ a * (s * b) ^ j / j !) m := by
      have := (integrable_pow_of_memLp hm (j := j) (by
        have := mem_range.1 hj; omega)).const_mul (iteratedDeriv j ψ a * b ^ j / j !)
      refine this.congr (ae_of_all _ fun s => ?_)
      simp only [mul_pow]; ring
    refine ⟨integrable_finsetSum _ hint, ?_⟩
    rw [integral_finsetSum _ hint]
    refine sum_congr rfl fun j _ => ?_
    rw [← integral_const_mul]
    congr 1 with s : 1; simp only [mul_pow]; ring
  have hRint {m : Measure ℝ} [IsProbabilityMeasure m] (hm : MemLp id ((n + 1 : ℕ) : ℝ≥0∞) m) :
      Integrable R m :=
    ((integrable_abs_pow_of_memLp hm le_rfl).const_mul K).mono'
      (by fun_prop : Continuous R).aestronglyMeasurable
      (ae_of_all _ fun s => by simpa using hR s)
  have hsplit {m : Measure ℝ} [IsProbabilityMeasure m] (hm : MemLp id ((n + 1 : ℕ) : ℝ≥0∞) m) :
      ∫ s, ψ (a + s * b) ∂m = ∫ s, T s ∂m + ∫ s, R s ∂m := by
    rw [← integral_add (hTint hm).1 (hRint hm)]
    congr 1 with s : 1; simp [R]
  have hRle {m : Measure ℝ} [IsProbabilityMeasure m] (hm : MemLp id ((n + 1 : ℕ) : ℝ≥0∞) m) :
      |∫ s, R s ∂m| ≤ K * ∫ s, |s| ^ (n + 1) ∂m := by
    rw [← integral_const_mul]
    exact (abs_integral_le_integral_abs).trans (integral_mono (hRint hm).abs
      ((integrable_abs_pow_of_memLp hm le_rfl).const_mul K) hR)
  have hT : ∫ s, T s ∂μ = ∫ s, T s ∂ν := by
    rw [(hTint hμ).2, (hTint hν).2]
    refine sum_congr rfl fun j hj => ?_
    rw [hmom j (Nat.lt_succ_iff.1 (mem_range.1 hj))]
  rw [hsplit hμ, hsplit hν, hT, add_sub_add_left_eq_sub, mul_add]
  exact (abs_sub _ _).trans (add_le_add (hRle hμ) (hRle hν))

namespace HasInvarianceMoments

variable {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Under Hypothesis 11.65, `E|z|³ ≤ √(E z² · E z⁴) ≤ 3`. -/
theorem integral_abs_pow_three_le (hμ : HasInvarianceMoments μ) : ∫ s, |s| ^ 3 ∂μ ≤ 3 := by
  have hm4 : MemLp id ((4 : ℕ) : ℝ≥0∞) μ := by exact_mod_cast hμ.memLp_four
  have h := sq_integral_mul_le (P := μ) (f := fun s => |s|) (g := fun s => s ^ 2)
    (by simpa using integrable_pow_of_memLp hm4 (j := 2) (by norm_num))
    (by simpa only [← pow_mul] using integrable_pow_of_memLp hm4 (j := 4) le_rfl)
    ((integrable_abs_pow_of_memLp hm4 (j := 3) (by norm_num)).congr (ae_of_all _ fun s => by
      simp only; rw [← sq_abs s]; ring))
  have h3 : ∫ s, |s| * s ^ 2 ∂μ = ∫ s, |s| ^ 3 ∂μ := by
    congr 1 with s : 1; rw [← sq_abs s]; ring
  simp only [sq_abs, ← pow_mul] at h
  rw [h3, hμ.integral_sq, one_mul] at h
  have h0 : 0 ≤ ∫ s, |s| ^ 3 ∂μ := integral_nonneg fun _ => by positivity
  nlinarith [hμ.integral_pow_four_le]

/-- **The replacement step under Hypothesis 11.65, `C⁴` form.** If `ψ` is `C⁴` with `|ψ⁗| ≤ C`,
then `|E_ν ψ(a + s b) - E_μ ψ(a + s b)| ≤ C / 24 · (E_ν s⁴ + E_μ s⁴) · b⁴ ≤ 3 C / 4 · b⁴`. -/
theorem abs_integral_sub_le (hμ : HasInvarianceMoments μ) (hν : HasInvarianceMoments ν)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 4 ψ) {C : ℝ} (hC : ∀ y, |iteratedDeriv 4 ψ y| ≤ C) (a b : ℝ) :
    |∫ s, ψ (a + s * b) ∂ν - ∫ s, ψ (a + s * b) ∂μ| ≤ 3 / 4 * C * |b| ^ 4 := by
  have h := abs_integral_sub_integral_le_of_moments (n := 3) (by exact_mod_cast hν.memLp_four)
    (by exact_mod_cast hμ.memLp_four) ?_ hψ hC a b
  · have h4 (m : Measure ℝ) (hm : HasInvarianceMoments m) : ∫ s, |s| ^ (3 + 1) ∂m ≤ 9 := by
      simpa [Even.pow_abs (by decide : Even 4)] using hm.integral_pow_four_le
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    refine h.trans ?_
    have hf : ((3 + 1)! : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hf]
    have hb4 : 0 ≤ C / 24 * |b| ^ (3 + 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add (h4 ν hν) (h4 μ hμ)) hb4]
  · intro j hj
    interval_cases j
    · simp
    · simpa using hν.integral_id.trans hμ.integral_id.symm
    · rw [hν.integral_sq, hμ.integral_sq]
    · rw [hν.integral_pow_three, hμ.integral_pow_three]

/-- **The replacement step under Hypothesis 11.65, `C³` form.** If `ψ` is `C³` with `|ψ‴| ≤ C`,
then `|E_ν ψ(a + s b) - E_μ ψ(a + s b)| ≤ C / 6 · (E_ν |s|³ + E_μ |s|³) · |b|³ ≤ C · |b|³`. -/
theorem abs_integral_sub_le_of_contDiff_three (hμ : HasInvarianceMoments μ)
    (hν : HasInvarianceMoments ν) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 3 ψ) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv 3 ψ y| ≤ C) (a b : ℝ) :
    |∫ s, ψ (a + s * b) ∂ν - ∫ s, ψ (a + s * b) ∂μ| ≤ C * |b| ^ 3 := by
  have h := abs_integral_sub_integral_le_of_moments (n := 2)
    (by exact_mod_cast hν.memLp_four.mono_exponent (by norm_num))
    (by exact_mod_cast hμ.memLp_four.mono_exponent (by norm_num)) ?_ hψ hC a b
  · have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    refine h.trans ?_
    have hf : ((2 + 1)! : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [hf]
    have hb3 : 0 ≤ C / 6 * |b| ^ (2 + 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left
      (add_le_add hν.integral_abs_pow_three_le hμ.integral_abs_pow_three_le) hb3]
  · intro j hj
    interval_cases j
    · simp
    · simpa using hν.integral_id.trans hμ.integral_id.symm
    · rw [hν.integral_sq, hμ.integral_sq]

end HasInvarianceMoments

/-! ### The hybrid argument -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem hasInvarianceMoments_piecewise (s : Finset ι) {μ ν : ι → Measure ℝ}
    (hμ : ∀ i, HasInvarianceMoments (μ i)) (hν : ∀ i, HasInvarianceMoments (ν i)) (i : ι) :
    HasInvarianceMoments (s.piecewise ν μ i) := by
  by_cases h : i ∈ s
  · rw [Finset.piecewise_eq_of_mem _ _ _ h]; exact hν i
  · rw [Finset.piecewise_eq_of_notMem _ _ _ h]; exact hμ i

omit [DecidableEq ι] in
/-- A test function with bounded `(n+1)`st derivative, `n + 1 ≤ 4`, composed with a multilinear
polynomial of `L⁴` variables is integrable. -/
theorem integrable_comp_multilinearEval (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, MemLp id 4 (μ i)) (c : Finset ι → ℝ) {ψ : ℝ → ℝ} {n : ℕ} (hn : n + 1 ≤ 4)
    (hψ : ContDiff ℝ (n + 1) ψ) {C : ℝ} (hC : ∀ y, |iteratedDeriv (n + 1) ψ y| ≤ C) :
    Integrable (fun z => ψ (multilinearEval c z)) (Measure.pi μ) := by
  obtain ⟨K, hK⟩ := hψ.exists_abs_le_mul_one_add_pow_of_abs_iteratedDeriv_le hC
  refine (((integrable_const 1).add
    (integrable_abs_multilinearEval_pow μ hμ c hn)).const_mul K).mono'
    (hψ.continuous.comp (continuous_multilinearEval c)).aestronglyMeasurable
    (ae_of_all _ fun z => ?_)
  simpa [Real.norm_eq_abs] using hK (multilinearEval c z)

/-- One step of the hybrid argument for a multilinear polynomial: if each one-coordinate
replacement costs at most `K |b| ^ p` for the coefficient `b` of the replaced variable, then
replacing coordinate `t` costs at most `K E|D_t F| ^ p` over the hybrid. -/
private theorem abs_integral_pi_piecewise_insert_sub_le (μ ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (hμ : ∀ i, HasInvarianceMoments (μ i)) (hν : ∀ i, HasInvarianceMoments (ν i))
    (c : Finset ι → ℝ) {ψ : ℝ → ℝ} (hψ : ∀ s : Finset ι,
      Integrable (fun z => ψ (multilinearEval c z)) (Measure.pi (s.piecewise ν μ)))
    {p : ℕ} (hp : p ≤ 4) {K : ℝ}
    (h1 : ∀ t a b, |∫ s, ψ (a + s * b) ∂ν t - ∫ s, ψ (a + s * b) ∂μ t| ≤ K * |b| ^ p)
    {s : Finset ι} {t : ι} (ht : t ∉ s) :
    |∫ z, ψ (multilinearEval c z) ∂Measure.pi ((insert t s).piecewise ν μ) -
      ∫ z, ψ (multilinearEval c z) ∂Measure.pi (s.piecewise ν μ)| ≤
      K * ∫ z, |multilinearEval (multilinearDerivCoeff c t) z| ^ p
        ∂Measure.pi (s.piecewise ν μ) := by
  have := isProbabilityMeasure_piecewise μ ν s
  have hPm := hasInvarianceMoments_piecewise s hμ hν
  rw [integral_pi_piecewise_insert_sub μ ν ht hψ, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (ae_of_all _ fun _ => abs_nonneg _)
    ((integrable_abs_multilinearEval_pow _ (fun i => (hPm i).memLp_four) _ hp).const_mul K)
    (ae_of_all _ fun v => ?_))
  simp only [multilinearEval_update c t]
  exact h1 t _ _

/-- `9 E[(D_t F)⁴] ≤ 9 ^ k Inf_t[F] ^ 2` for `F` of degree at most `k` (the Bonami Lemma for
`D_t F`, of degree at most `k - 1`). -/
private theorem integral_multilinearDerivCoeff_pow_four_le (P : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (P i)] (hP : ∀ i, HasInvarianceMoments (P i)) {k : ℕ}
    {c : Finset ι → ℝ} (hc : ∀ S, k < #S → c S = 0) (t : ι) :
    9 * ∫ z, multilinearEval (multilinearDerivCoeff c t) z ^ 4 ∂Measure.pi P ≤
      9 ^ k * multilinearInfluence c t ^ 2 := by
  rcases k with _ | k
  · have hD0 := multilinearDerivCoeff_eq_zero_of_degree_zero hc t
    have hI : multilinearInfluence c t = 0 := by
      rw [multilinearInfluence_eq_sum_multilinearDerivCoeff_sq, hD0]; simp
    simp [hD0, hI]
  · have := integral_multilinearEval_pow_four_le P hP
      (multilinearDerivCoeff_eq_zero_of_card_lt hc t)
    rw [← multilinearInfluence_eq_sum_multilinearDerivCoeff_sq] at this
    rw [pow_succ', mul_assoc]
    exact mul_le_mul_of_nonneg_left this (by norm_num)

variable (μ ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]

/-- **The Basic Invariance Principle** [O'Donnell, Section 11.6, equation (11.29)][ODonnell2014].
Let `F` be a formal multilinear polynomial of degree at most `k`, and let `x` and `y` be vectors of
independent random variables with laws `μ i` and `ν i`, each satisfying Hypothesis 11.65. If
`ψ : ℝ → ℝ` is `C⁴` with `|ψ⁗| ≤ C`, then
`|E[ψ(F(x))] - E[ψ(F(y))]| ≤ C / 12 · 9 ^ k · ∑_t Inf_t[F] ^ 2`. -/
theorem abs_integral_comp_multilinearEval_sub_le (hμ : ∀ i, HasInvarianceMoments (μ i))
    (hν : ∀ i, HasInvarianceMoments (ν i)) {k : ℕ} {c : Finset ι → ℝ}
    (hc : ∀ S, k < #S → c S = 0) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 4 ψ) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv 4 ψ y| ≤ C) :
    |∫ z, ψ (multilinearEval c z) ∂Measure.pi μ - ∫ z, ψ (multilinearEval c z) ∂Measure.pi ν| ≤
      C / 12 * 9 ^ k * ∑ t, multilinearInfluence c t ^ 2 := by
  have hint (s : Finset ι) :
      Integrable (fun z => ψ (multilinearEval c z)) (Measure.pi (s.piecewise ν μ)) := by
    have := isProbabilityMeasure_piecewise μ ν s
    exact integrable_comp_multilinearEval _
      (fun i => (hasInvarianceMoments_piecewise s hμ hν i).memLp_four) c (n := 3) le_rfl hψ hC
  rw [mul_sum]
  refine abs_integral_pi_sub_le_sum μ ν _ fun s t ht => ?_
  have := isProbabilityMeasure_piecewise μ ν s
  refine (abs_integral_pi_piecewise_insert_sub_le μ ν hμ hν c hint le_rfl
    (fun t a b => (hμ t).abs_integral_sub_le (hν t) hψ hC a b) ht).trans ?_
  have hD := integral_multilinearDerivCoeff_pow_four_le _
    (hasInvarianceMoments_piecewise s hμ hν) hc t
  simp only [Even.pow_abs (by decide : Even 4)]
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  nlinarith [mul_le_mul_of_nonneg_left hD hC0]

/-- `∑_t Inf_t[F] ^ 2 ≤ ε k ∑_{S ≠ ∅} F̂(S) ^ 2` when `F` has degree at most `k` and every
influence is at most `ε` [O'Donnell, proof of Corollary 11.67][ODonnell2014]. -/
theorem sum_multilinearInfluence_sq_le {k : ℕ} {c : Finset ι → ℝ} (hc : ∀ S, k < #S → c S = 0)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ t, multilinearInfluence c t ≤ ε) :
    ∑ t, multilinearInfluence c t ^ 2 ≤ ε * k * ∑ S with S ≠ ∅, c S ^ 2 := by
  have hk : ∑ S, (#S : ℝ) * c S ^ 2 ≤ k * ∑ S with S ≠ ∅, c S ^ 2 := by
    rw [mul_sum, sum_filter]
    refine sum_le_sum fun S _ => ?_
    split_ifs with hS
    · rcases le_or_gt #S k with h | h
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (sq_nonneg _)
      · rw [hc S h]; simp
    · rw [not_not.1 hS]; simp
  calc ∑ t, multilinearInfluence c t ^ 2 ≤ ∑ t, ε * multilinearInfluence c t :=
        sum_le_sum fun t _ => by
          rw [sq]; exact mul_le_mul_of_nonneg_right (hε t) (multilinearInfluence_nonneg c t)
    _ = ε * ∑ S, (#S : ℝ) * c S ^ 2 := by rw [← mul_sum, sum_multilinearInfluence]
    _ ≤ ε * (k * ∑ S with S ≠ ∅, c S ^ 2) := mul_le_mul_of_nonneg_left hk hε0
    _ = _ := by ring

/-- **Invariance for polynomials with small influences** [O'Donnell, Corollary 11.67]
[ODonnell2014]. In the setting of `abs_integral_comp_multilinearEval_sub_le`, if moreover
`Var[F] = ∑_{S ≠ ∅} F̂(S) ^ 2 ≤ 1` and `Inf_t[F] ≤ ε` for every `t`, then
`|E[ψ(F(x))] - E[ψ(F(y))]| ≤ C / 12 · k 9 ^ k · ε`. The hypothesis `0 ≤ ε` only matters when there
are no coordinates. -/
theorem abs_integral_comp_multilinearEval_sub_le_of_influence_le
    (hμ : ∀ i, HasInvarianceMoments (μ i)) (hν : ∀ i, HasInvarianceMoments (ν i)) {k : ℕ}
    {c : Finset ι → ℝ} (hc : ∀ S, k < #S → c S = 0) (hvar : ∑ S with S ≠ ∅, c S ^ 2 ≤ 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ t, multilinearInfluence c t ≤ ε) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ 4 ψ) {C : ℝ} (hC : ∀ y, |iteratedDeriv 4 ψ y| ≤ C) :
    |∫ z, ψ (multilinearEval c z) ∂Measure.pi μ - ∫ z, ψ (multilinearEval c z) ∂Measure.pi ν| ≤
      C / 12 * k * 9 ^ k * ε := by
  refine (abs_integral_comp_multilinearEval_sub_le μ ν hμ hν hc hψ hC).trans ?_
  have h := sum_multilinearInfluence_sq_le hc hε0 hε
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have h2 : ε * k * ∑ S with S ≠ ∅, c S ^ 2 ≤ ε * k := by
    have := mul_le_mul_of_nonneg_left hvar (by positivity : 0 ≤ ε * k); linarith
  calc C / 12 * 9 ^ k * ∑ t, multilinearInfluence c t ^ 2 ≤ C / 12 * 9 ^ k * (ε * k) :=
        mul_le_mul_of_nonneg_left (h.trans h2) (by positivity)
    _ = _ := by ring

/-- `3 E|D_t F|³ ≤ 3 ^ k Inf_t[F] ^ (3 / 2)` for `F` of degree at most `k`: Cauchy–Schwarz gives
`(E|D_t F|³)² ≤ E[(D_t F)²] E[(D_t F)⁴]`, and `E[(D_t F)²] = Inf_t[F]`, while the Bonami Lemma gives
`E[(D_t F)⁴] ≤ 9 ^ (k - 1) Inf_t[F] ^ 2`. -/
private theorem integral_abs_multilinearDerivCoeff_pow_three_le (P : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (P i)] (hP : ∀ i, HasInvarianceMoments (P i)) {k : ℕ}
    {c : Finset ι → ℝ} (hc : ∀ S, k < #S → c S = 0) (t : ι) :
    3 * ∫ z, |multilinearEval (multilinearDerivCoeff c t) z| ^ 3 ∂Measure.pi P ≤
      3 ^ k * multilinearInfluence c t ^ ((3 : ℝ) / 2) := by
  set D := multilinearEval (multilinearDerivCoeff c t)
  set I := multilinearInfluence c t
  have hI0 : 0 ≤ I := multilinearInfluence_nonneg c t
  have hm4 (i : ι) := (hP i).memLp_four
  have h2 : ∫ z, D z ^ 2 ∂Measure.pi P = I := by
    rw [integral_multilinearEval_sq_of_hasInvarianceMoments P hP,
      ← multilinearInfluence_eq_sum_multilinearDerivCoeff_sq]
  have h4 := integral_multilinearDerivCoeff_pow_four_le P hP hc t
  have hD2 : Integrable (fun z => D z ^ 2) (Measure.pi P) :=
    integrable_multilinearEval_pow P hm4 _ (by norm_num)
  have hD4 : Integrable (fun z => D z ^ 4) (Measure.pi P) :=
    integrable_multilinearEval_pow P hm4 _ le_rfl
  have hD3 : Integrable (fun z => |D z| ^ 3) (Measure.pi P) :=
    integrable_abs_multilinearEval_pow P hm4 _ (by norm_num)
  have hCS := sq_integral_mul_le (P := Measure.pi P) (f := fun z => |D z|)
    (g := fun z => D z ^ 2) (by simpa using hD2) (by simpa only [← pow_mul] using hD4)
    (hD3.congr (ae_of_all _ fun z => by simp only; rw [← sq_abs (D z)]; ring))
  have h3 : ∫ z, |D z| * D z ^ 2 ∂Measure.pi P = ∫ z, |D z| ^ 3 ∂Measure.pi P := by
    congr 1 with z : 1; rw [← sq_abs (D z)]; ring
  simp only [sq_abs, ← pow_mul, Nat.reduceMul] at hCS
  rw [h3, h2] at hCS
  set M := ∫ z, |D z| ^ 3 ∂Measure.pi P
  have hM0 : 0 ≤ M := integral_nonneg fun _ => by positivity
  have hR0 : 0 ≤ 3 ^ k * I ^ ((3 : ℝ) / 2) := by positivity
  have hR : (3 ^ k * I ^ ((3 : ℝ) / 2)) ^ 2 = 9 ^ k * I ^ 3 := by
    rw [mul_pow, ← Real.rpow_mul_natCast hI0, ← pow_mul, mul_comm k, pow_mul]
    norm_num
  refine (pow_le_pow_iff_left₀ (by positivity) hR0 two_ne_zero).1 ?_
  rw [hR]
  nlinarith [mul_le_mul_of_nonneg_left h4 hI0]

/-- **The Basic Invariance Principle, `C³` form.** In the setting of
`abs_integral_comp_multilinearEval_sub_le`, if `ψ` is only `C³` with `|ψ‴| ≤ C`, then
`|E[ψ(F(x))] - E[ψ(F(y))]| ≤ C / 3 · 3 ^ k · ∑_t Inf_t[F] ^ (3 / 2)`. This is the analogue under
Hypothesis 11.65 of [O'Donnell, Remark 11.66][ODonnell2014], whose hypothesis is instead
`(2, 3, ρ)`-hypercontractivity of the variables and whose factor is `(1 / ρ) ^ (3 k)`; the factor
`3 ^ k` here is the value of that factor at `ρ = 3 ^ (-1 / 3)`. -/
theorem abs_integral_comp_multilinearEval_sub_le_of_contDiff_three
    (hμ : ∀ i, HasInvarianceMoments (μ i)) (hν : ∀ i, HasInvarianceMoments (ν i)) {k : ℕ}
    {c : Finset ι → ℝ} (hc : ∀ S, k < #S → c S = 0) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 3 ψ) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv 3 ψ y| ≤ C) :
    |∫ z, ψ (multilinearEval c z) ∂Measure.pi μ - ∫ z, ψ (multilinearEval c z) ∂Measure.pi ν| ≤
      C / 3 * 3 ^ k * ∑ t, multilinearInfluence c t ^ ((3 : ℝ) / 2) := by
  have hint (s : Finset ι) :
      Integrable (fun z => ψ (multilinearEval c z)) (Measure.pi (s.piecewise ν μ)) := by
    have := isProbabilityMeasure_piecewise μ ν s
    exact integrable_comp_multilinearEval _
      (fun i => (hasInvarianceMoments_piecewise s hμ hν i).memLp_four) c (n := 2) (by norm_num)
      hψ hC
  rw [mul_sum]
  refine abs_integral_pi_sub_le_sum μ ν _ fun s t ht => ?_
  have := isProbabilityMeasure_piecewise μ ν s
  refine (abs_integral_pi_piecewise_insert_sub_le μ ν hμ hν c hint (by norm_num)
    (fun t a b => (hμ t).abs_integral_sub_le_of_contDiff_three (hν t) hψ hC a b) ht).trans ?_
  have hD := integral_abs_multilinearDerivCoeff_pow_three_le _
    (hasInvarianceMoments_piecewise s hμ hν) hc t
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  nlinarith [mul_le_mul_of_nonneg_left hD hC0]

end ProbabilityTheory
