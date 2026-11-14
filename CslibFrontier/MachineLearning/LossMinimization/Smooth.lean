/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.LossMinimization.RLM
public import Mathlib.Analysis.Calculus.FDeriv.Basic
import CslibFrontier.Foundations.Analysis.Calculus.LipschitzDeriv
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Stability of regularized loss minimization for smooth losses

For losses that are convex, nonnegative and `β`-smooth (differentiable with a `β`-Lipschitz
derivative) the RLM rule with a `σ`-strongly convex regularizer is stable relative to its own fit:
for `4β ≤ σ m`, the expected replace-one gap is at most `10β / (σ m)` times the expected empirical
risk of the output [ShalevShwartzBenDavid2014, Section 13.3.2]. Unlike the Lipschitz case
(`Cslib.MachineLearning.IsRLM.isReplaceOneStable`), the loss need not be Lipschitz; the rate
shrinks with the fit of the rule.

With Tikhonov regularization `r‖w‖²` (the source writes `λ` for `r`) and `2β ≤ r m`, the factor is
`5β / (r m)`, which proves [ShalevShwartzBenDavid2014, Corollary 13.7] with `5` in place of the
source's `48`. The source bounds the distance between the two minimizers through the quadratic
growth of one objective and then uses `(a + b)² ≤ 3(a² + b²)`; here both growth terms enter
(`Cslib.MachineLearning.IsRLM.mul_norm_sub_sq_le`) and the final estimate is a positive-definite
quadratic form. The smaller constant matters for [ShalevShwartzBenDavid2014, Corollary 13.11],
whose parameters `m ≥ 150 β B² / ε²` and `r = ε / (3 B²)` give an excess of about
`ε / 3 + 0.96 ε` with the factor `48` but `ε / 3 + ε / 10` with `5`.

Smoothness is stated as differentiability of every loss together with a `β`-Lipschitz `fderiv`,
on the whole space: self-boundedness (`norm_sq_le_of_lipschitzWith_hasFDerivAt`) evaluates the
loss off the set the rule minimizes over.

## Main results

* `Cslib.MachineLearning.IsRLM.mul_sub_le_of_lipschitzWith_fderiv`,
  `Cslib.MachineLearning.IsRLM.sub_le_of_lipschitzWith_fderiv`: for smooth losses, the per-sample
  gap is at most `5β / (σ m) (ℓ(A S, z_i) + ℓ(A S⁽ⁱ⁾, z'))`.
* `Cslib.MachineLearning.IsRLM.replaceOneGap_le_of_lipschitzWith_fderiv`: the expected replace-one
  gap is at most `10β / (σ m) 𝔼_S [L_S(A S)]`.
* `Cslib.MachineLearning.IsRLM.replaceOneGap_le_tikhonov_of_lipschitzWith_fderiv`: Tikhonov RLM
  has expected replace-one gap at most `5β / (r m) 𝔼_S [L_S(A S)]`
  [ShalevShwartzBenDavid2014, Corollary 13.7].
* `Cslib.MachineLearning.IsRLM.integral_trueRisk_le_tikhonov_of_lipschitzWith_fderiv`: the
  oracle inequality `𝔼_S [L_D(A S)] ≤ (1 + 5β / (r m)) (L_D(w) + r‖w‖²)`
  [ShalevShwartzBenDavid2014, Corollary 13.10].
* `Cslib.MachineLearning.IsRLM.integral_trueRisk_le_add_of_lipschitzWith_fderiv`: for losses with
  `ℓ(0, z) ≤ 1`, `ε ∈ (0, 1)`, `m ≥ 150 β B² / ε²` and `r = ε / (3 B²)`, Tikhonov RLM satisfies
  `𝔼_S [L_D(A S)] ≤ L_D(w) + ε` for every comparator of norm at most `B`
  [ShalevShwartzBenDavid2014, Corollary 13.11].

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Sections 12.1.3 and 13.3.2–13.4
-/

public section

open MeasureTheory Set

namespace Cslib.MachineLearning

variable {E Z : Type*}

/-- The arithmetic core of the smooth stability bound. With `s = σ m`, `d` the distance between the
two minimizers, `X` and `Y` the two loss changes and `p`, `q` the self-bounds on the two
gradients: if `s d² ≤ X + Y`, each change is at most `p d + β d² / 2` (resp. `q d + β d² / 2`),
`p ≥ 0` and `4β ≤ s`, then `s X ≤ 5/2 (p² + q²)`. -/
private theorem smooth_gap_arith {s β d p q X Y : ℝ} (hβ : 0 ≤ β) (hs : 4 * β ≤ s) (hd : 0 ≤ d)
    (hp : 0 ≤ p) (hgrowth : s * d ^ 2 ≤ X + Y) (hX : X ≤ p * d + β / 2 * d ^ 2)
    (hY : Y ≤ q * d + β / 2 * d ^ 2) : s * X ≤ 5 / 2 * (p ^ 2 + q ^ 2) := by
  rcases hd.eq_or_lt with h0 | hpos
  · subst h0
    have : X ≤ 0 := by simpa using hX
    nlinarith
  -- Dividing the growth inequality by `d > 0` gives `(s - β) d ≤ p + q`, hence `3 s d ≤ 4 (p + q)`.
  have hlin : (s - β) * d ≤ p + q := by
    have : ((s - β) * d) * d ≤ (p + q) * d := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  have ht : 3 * (s * d) ≤ 4 * (p + q) := by nlinarith
  -- `s X ≤ p (s d) + (s d)² / 8`, and `s d ≤ 4 (p + q) / 3`.
  have hsX : s * X ≤ p * (s * d) + (s * d) ^ 2 / 8 := by
    have h1 : s * X ≤ s * (p * d + β / 2 * d ^ 2) := by
      have : 0 ≤ s := by linarith
      exact mul_le_mul_of_nonneg_left hX this
    have h2 : s * (β / 2 * d ^ 2) ≤ (s * d) ^ 2 / 8 := by
      have : 0 ≤ s * d ^ 2 * (s - 4 * β) :=
        mul_nonneg (mul_nonneg (by linarith) (sq_nonneg d)) (by linarith)
      nlinarith
    nlinarith
  have hst : 0 ≤ s * d := by nlinarith
  have h3 : p * (3 * (s * d)) ≤ p * (4 * (p + q)) := mul_le_mul_of_nonneg_left ht hp
  have h4 : (3 * (s * d)) ^ 2 ≤ (4 * (p + q)) ^ 2 := by
    have : 0 ≤ 3 * (s * d) := by linarith
    exact pow_le_pow_left₀ this ht 2
  nlinarith [sq_nonneg (p - q), sq_nonneg p, sq_nonneg q]

section Smooth

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Per-sample stability of RLM for smooth losses**, multiplied form (compare
[ShalevShwartzBenDavid2014, Section 13.3.2]): if `R` is `σ`-strongly convex on `K`, every loss is
convex on `K`, nonnegative and differentiable with a `β`-Lipschitz derivative, and `4β ≤ σ m`, then
`σ m (ℓ(A S⁽ⁱ⁾, z_i) - ℓ(A S, z_i)) ≤ 5β (ℓ(A S, z_i) + ℓ(A S⁽ⁱ⁾, z'))`. -/
theorem IsRLM.mul_sub_le_of_lipschitzWith_fderiv {ℓ : E → Z → ℝ} {R : E → ℝ} {K : Set E} {m : ℕ}
    {A : (Fin m → Z) → E} (hA : IsRLM ℓ R K A) {σ : ℝ} (hR : StrongConvexOn K σ R)
    (hconv : ∀ z, ConvexOn ℝ K fun w => ℓ w z) (hdiff : ∀ z, Differentiable ℝ fun w => ℓ w z)
    {β : NNReal} (hsmooth : ∀ z, LipschitzWith β (fderiv ℝ fun w => ℓ w z))
    (hnonneg : ∀ w z, 0 ≤ ℓ w z) (hβ : 4 * (β : ℝ) ≤ σ * m) (S : Fin m → Z) (i : Fin m)
    (z' : Z) :
    σ * m * (ℓ (A (Function.update S i z')) (S i) - ℓ (A S) (S i)) ≤
      5 * β * (ℓ (A S) (S i) + ℓ (A (Function.update S i z')) z') := by
  have hgrowth := hA.mul_norm_sub_sq_le hR hconv S i z'
  have hf : ∀ z, ∀ w, HasFDerivAt (fun w => ℓ w z) (fderiv ℝ (fun w => ℓ w z) w) w :=
    fun z w => (hdiff z w).hasFDerivAt
  -- The self-bounds `‖∇ℓ(u, z_i)‖ ≤ √(2β ℓ(u, z_i))` and `‖∇ℓ(v, z')‖ ≤ √(2β ℓ(v, z'))`.
  have hnorm : ∀ z w, ‖fderiv ℝ (fun w => ℓ w z) w‖ ≤ √(2 * β * ℓ w z) := fun z w =>
    Real.le_sqrt_of_sq_le
      (norm_sq_le_of_lipschitzWith_hasFDerivAt (hf z) (hsmooth z) (fun w => hnonneg w z) w)
  -- Smoothness bounds the change of each loss by its gradient term plus `β/2 ‖v - u‖²`.
  have hstep : ∀ z w w', ℓ w' z - ℓ w z ≤ √(2 * β * ℓ w z) * ‖w' - w‖ + β / 2 * ‖w' - w‖ ^ 2 :=
    fun z w w' => by
      have h := image_le_of_lipschitzWith_hasFDerivAt (hf z) (hsmooth z) w w'
      have hdir : fderiv ℝ (fun w => ℓ w z) w (w' - w) ≤ √(2 * β * ℓ w z) * ‖w' - w‖ :=
        calc _ ≤ ‖fderiv ℝ (fun w => ℓ w z) w (w' - w)‖ := Real.le_norm_self _
          _ ≤ ‖fderiv ℝ (fun w => ℓ w z) w‖ * ‖w' - w‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ √(2 * β * ℓ w z) * ‖w' - w‖ := by gcongr; exact hnorm z w
      linarith
  have hX := hstep (S i) (A S) (A (Function.update S i z'))
  have hY := hstep z' (A (Function.update S i z')) (A S)
  rw [norm_sub_rev] at hY
  have h := smooth_gap_arith (s := σ * m) β.2 hβ (norm_nonneg _) (Real.sqrt_nonneg _) hgrowth hX
    hY
  rw [Real.sq_sqrt (by have := hnonneg (A S) (S i); positivity),
    Real.sq_sqrt (by have := hnonneg (A (Function.update S i z')) z'; positivity)] at h
  linarith

/-- **Per-sample stability of RLM for smooth losses** (compare [ShalevShwartzBenDavid2014,
Section 13.3.2]): under the hypotheses of
`Cslib.MachineLearning.IsRLM.mul_sub_le_of_lipschitzWith_fderiv` with `σ > 0`,
`ℓ(A S⁽ⁱ⁾, z_i) - ℓ(A S, z_i) ≤ 5β / (σ m) (ℓ(A S, z_i) + ℓ(A S⁽ⁱ⁾, z'))`. -/
theorem IsRLM.sub_le_of_lipschitzWith_fderiv {ℓ : E → Z → ℝ} {R : E → ℝ} {K : Set E} {m : ℕ}
    {A : (Fin m → Z) → E} (hA : IsRLM ℓ R K A) {σ : ℝ} (hσ : 0 < σ) (hR : StrongConvexOn K σ R)
    (hconv : ∀ z, ConvexOn ℝ K fun w => ℓ w z) (hdiff : ∀ z, Differentiable ℝ fun w => ℓ w z)
    {β : NNReal} (hsmooth : ∀ z, LipschitzWith β (fderiv ℝ fun w => ℓ w z))
    (hnonneg : ∀ w z, 0 ≤ ℓ w z) (hβ : 4 * (β : ℝ) ≤ σ * m) (S : Fin m → Z) (i : Fin m)
    (z' : Z) :
    ℓ (A (Function.update S i z')) (S i) - ℓ (A S) (S i) ≤
      5 * β / (σ * m) * (ℓ (A S) (S i) + ℓ (A (Function.update S i z')) z') := by
  have hm : (0 : ℝ) < m := by exact_mod_cast i.pos
  have h := hA.mul_sub_le_of_lipschitzWith_fderiv hR hconv hdiff hsmooth hnonneg hβ S i z'
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

variable [MeasurableSpace Z]

/-- **Expected stability of RLM for smooth losses** (compare [ShalevShwartzBenDavid2014,
Corollary 13.7]): if `R` is `σ`-strongly convex on `K` with `σ > 0`, every loss is convex on `K`,
nonnegative and differentiable with a `β`-Lipschitz derivative, and `4β ≤ σ m`, then for i.i.d.
examples from `D` whose losses at the outputs are integrable, the expected replace-one gap is at
most `10β / (σ m) 𝔼_S [L_S(A S)]`. -/
theorem IsRLM.replaceOneGap_le_of_lipschitzWith_fderiv {ℓ : E → Z → ℝ} {R : E → ℝ} {K : Set E}
    {m : ℕ} {A : (Fin m → Z) → E} (hA : IsRLM ℓ R K A) {σ : ℝ} (hσ : 0 < σ)
    (hR : StrongConvexOn K σ R) (hconv : ∀ z, ConvexOn ℝ K fun w => ℓ w z)
    (hdiff : ∀ z, Differentiable ℝ fun w => ℓ w z) {β : NNReal}
    (hsmooth : ∀ z, LipschitzWith β (fderiv ℝ fun w => ℓ w z)) (hnonneg : ∀ w z, 0 ≤ ℓ w z)
    (hβ : 4 * (β : ℝ) ≤ σ * m) (D : Measure Z) [IsProbabilityMeasure D]
    (hint' : ∀ i, Integrable (fun S => ℓ (A S) (S i)) (Measure.pi fun _ : Fin m => D)) :
    replaceOneGap ℓ D A ≤
      10 * β / (σ * m) * ∫ S, empiricalRisk ℓ S (A S) ∂(Measure.pi fun _ : Fin m => D) := by
  rw [replaceOneGap_def, integral_empiricalRisk_comp ℓ _ A hint', Finset.mul_expect]
  refine Finset.expect_le_expect fun i _ => ?_
  set μ := Measure.pi fun _ : Fin m => D
  have hm : (0 : ℝ) < m := by exact_mod_cast i.pos
  have hc : 0 ≤ 5 * (β : ℝ) / (σ * m) := by positivity
  -- Both `ℓ(A S, z_i)` and `ℓ(A S⁽ⁱ⁾, z')` have expectation `𝔼 [ℓ(A S, z_i)]`.
  have hold_int : Integrable (fun p : (Fin m → Z) × Z => ℓ (A p.1) (p.1 i)) (μ.prod D) :=
    (hint' i).comp_fst D
  have hnew_int : Integrable (fun p : (Fin m → Z) × Z => ℓ (A (Function.update p.1 i p.2)) p.2)
      (μ.prod D) := by
    simpa only [Function.update_self] using
      integrable_update_eval (g := fun p => ℓ (A p.1) (p.1 i)) i hold_int
  have hold : ∫ p, ℓ (A p.1) (p.1 i) ∂(μ.prod D) = ∫ S, ℓ (A S) (S i) ∂μ := by
    rw [integral_fun_fst (fun S => ℓ (A S) (S i)), probReal_univ, one_smul]
  have hnew : ∫ p, ℓ (A (Function.update p.1 i p.2)) p.2 ∂(μ.prod D) = ∫ S, ℓ (A S) (S i) ∂μ := by
    rw [← hold]
    simpa only [Function.update_self] using integral_update_eval D i fun p => ℓ (A p.1) (p.1 i)
  have hrhs_int : Integrable (fun p : (Fin m → Z) × Z => 5 * β / (σ * m) *
      (ℓ (A p.1) (p.1 i) + ℓ (A (Function.update p.1 i p.2)) p.2)) (μ.prod D) :=
    (hold_int.add hnew_int).const_mul _
  have hrhs : ∫ p, 5 * β / (σ * m) *
      (ℓ (A p.1) (p.1 i) + ℓ (A (Function.update p.1 i p.2)) p.2) ∂(μ.prod D) =
        10 * β / (σ * m) * ∫ S, ℓ (A S) (S i) ∂μ := by
    rw [integral_const_mul, integral_add hold_int hnew_int, hold, hnew]
    ring
  rw [← hrhs]
  by_cases hgap : Integrable (fun p : (Fin m → Z) × Z =>
      ℓ (A (Function.update p.1 i p.2)) (p.1 i) - ℓ (A p.1) (p.1 i)) (μ.prod D)
  · exact integral_mono hgap hrhs_int fun p =>
      hA.sub_le_of_lipschitzWith_fderiv hσ hR hconv hdiff hsmooth hnonneg hβ p.1 i p.2
  · rw [integral_undef hgap]
    exact integral_nonneg fun p => mul_nonneg hc (add_nonneg (hnonneg _ _) (hnonneg _ _))

end Smooth

section Tikhonov

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace Z]

/-- **Stability of Tikhonov RLM for smooth losses** [ShalevShwartzBenDavid2014, Corollary 13.7]:
for the regularizer `r‖w‖²` on a convex set `K`, losses that are convex on `K`, nonnegative and
differentiable with a `β`-Lipschitz derivative, and `2β ≤ r m` (the source's `r ≥ 2β / m`), the
expected replace-one gap under `D` is at most `5β / (r m) 𝔼_S [L_S(A S)]`. The source's factor is
`48β / (r m)`. -/
theorem IsRLM.replaceOneGap_le_tikhonov_of_lipschitzWith_fderiv {ℓ : E → Z → ℝ} {K : Set E}
    {m : ℕ} {r : ℝ} {A : (Fin m → Z) → E} (hA : IsRLM ℓ (fun w => r * ‖w‖ ^ 2) K A)
    (hK : Convex ℝ K) (hr : 0 < r) (hconv : ∀ z, ConvexOn ℝ K fun w => ℓ w z)
    (hdiff : ∀ z, Differentiable ℝ fun w => ℓ w z) {β : NNReal}
    (hsmooth : ∀ z, LipschitzWith β (fderiv ℝ fun w => ℓ w z)) (hnonneg : ∀ w z, 0 ≤ ℓ w z)
    (hβ : 2 * (β : ℝ) ≤ r * m) (D : Measure Z) [IsProbabilityMeasure D]
    (hint' : ∀ i, Integrable (fun S => ℓ (A S) (S i)) (Measure.pi fun _ : Fin m => D)) :
    replaceOneGap ℓ D A ≤
      5 * β / (r * m) * ∫ S, empiricalRisk ℓ S (A S) ∂(Measure.pi fun _ : Fin m => D) := by
  have h := hA.replaceOneGap_le_of_lipschitzWith_fderiv (by positivity)
    (strongConvexOn_mul_norm_sq hK r) hconv hdiff hsmooth hnonneg (by linarith) D hint'
  convert h using 2
  ring

/-- **The oracle inequality for Tikhonov RLM with smooth losses** [ShalevShwartzBenDavid2014,
Corollary 13.10]: under the hypotheses of
`Cslib.MachineLearning.IsRLM.replaceOneGap_le_tikhonov_of_lipschitzWith_fderiv`, for `m > 0`
i.i.d. examples from `D` and every `w ∈ K` with `D`-integrable loss,
`𝔼_S [L_D(A S)] ≤ (1 + 5β / (r m)) 𝔼_S [L_S(A S)] ≤ (1 + 5β / (r m)) (L_D(w) + r‖w‖²)`. The source
states both inequalities with `48β / (r m)` in place of `5β / (r m)`; they follow, since the
expected empirical risk is nonnegative. -/
theorem IsRLM.integral_trueRisk_le_tikhonov_of_lipschitzWith_fderiv {ℓ : E → Z → ℝ}
    {K : Set E} {m : ℕ} {r : ℝ} {A : (Fin m → Z) → E} (hA : IsRLM ℓ (fun w => r * ‖w‖ ^ 2) K A)
    (hK : Convex ℝ K) (hr : 0 < r) (hconv : ∀ z, ConvexOn ℝ K fun w => ℓ w z)
    (hdiff : ∀ z, Differentiable ℝ fun w => ℓ w z) {β : NNReal}
    (hsmooth : ∀ z, LipschitzWith β (fderiv ℝ fun w => ℓ w z)) (hnonneg : ∀ w z, 0 ≤ ℓ w z)
    (hβ : 2 * (β : ℝ) ≤ r * m) (D : Measure Z) [IsProbabilityMeasure D] (hm : 0 < m)
    (hint : Integrable (fun p : (Fin m → Z) × Z => ℓ (A p.1) p.2)
      ((Measure.pi fun _ : Fin m => D).prod D))
    (hint' : ∀ i, Integrable (fun S => ℓ (A S) (S i)) (Measure.pi fun _ : Fin m => D))
    {w : E} (hw : w ∈ K) (hwint : Integrable (ℓ w) D) :
    ∫ S, trueRisk ℓ D (A S) ∂(Measure.pi fun _ : Fin m => D) ≤
        (1 + 5 * β / (r * m)) * ∫ S, empiricalRisk ℓ S (A S) ∂(Measure.pi fun _ : Fin m => D) ∧
      (1 + 5 * β / (r * m)) * ∫ S, empiricalRisk ℓ S (A S) ∂(Measure.pi fun _ : Fin m => D) ≤
        (1 + 5 * β / (r * m)) * (trueRisk ℓ D w + r * ‖w‖ ^ 2) := by
  have hgap := hA.replaceOneGap_le_tikhonov_of_lipschitzWith_fderiv hK hr hconv hdiff hsmooth
    hnonneg hβ D hint'
  have h1 := integral_trueRisk_le_of_replaceOneGap_le D hm hint hint' hgap
  have h2 := hA.integral_empiricalRisk_le (fun _ _ => by positivity) D hm hint' hw hwint
  refine ⟨by linarith, mul_le_mul_of_nonneg_left h2 (by positivity)⟩

/-- **Convex-smooth-bounded problems** [ShalevShwartzBenDavid2014, Corollary 13.11]: for losses
that are convex on a convex set `K ∋ 0`, nonnegative, differentiable with a `β`-Lipschitz
derivative and satisfy `ℓ(0, z) ≤ 1`, `ε ∈ (0, 1)`, `B > 0`, `m ≥ 150 β B² / ε²` (with `m > 0`)
and `r = ε / (3 B²)`, Tikhonov RLM satisfies `𝔼_S [L_D(A S)] ≤ L_D(w) + ε` for every `w ∈ K` with
`‖w‖ ≤ B` and integrable loss. The source states this against `min_{w ∈ H} L_D(w)`; the form here
holds for every comparator. The parameters do not close with the source's factor `48β / (r m)`
from Corollary 13.10, which leaves an excess of about `ε / 3 + 0.96 ε`; the proof uses the factor
`5β / (r m)` of `Cslib.MachineLearning.IsRLM.replaceOneGap_le_tikhonov_of_lipschitzWith_fderiv`,
which leaves `ε / 3 + ε / 10`. -/
theorem IsRLM.integral_trueRisk_le_add_of_lipschitzWith_fderiv {ℓ : E → Z → ℝ} {K : Set E}
    {m : ℕ} {r : ℝ} {A : (Fin m → Z) → E} (hA : IsRLM ℓ (fun w => r * ‖w‖ ^ 2) K A)
    (hK : Convex ℝ K) (h0 : (0 : E) ∈ K) (hconv : ∀ z, ConvexOn ℝ K fun w => ℓ w z)
    (hdiff : ∀ z, Differentiable ℝ fun w => ℓ w z) {β : NNReal}
    (hsmooth : ∀ z, LipschitzWith β (fderiv ℝ fun w => ℓ w z)) (hnonneg : ∀ w z, 0 ≤ ℓ w z)
    (hle : ∀ z, ℓ 0 z ≤ 1) {ε B : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hB : 0 < B) (hm : 0 < m)
    (hmε : 150 * β * B ^ 2 / ε ^ 2 ≤ m) (hr : r = ε / (3 * B ^ 2)) (D : Measure Z)
    [IsProbabilityMeasure D]
    (hint : Integrable (fun p : (Fin m → Z) × Z => ℓ (A p.1) p.2)
      ((Measure.pi fun _ : Fin m => D).prod D))
    (hint' : ∀ i, Integrable (fun S => ℓ (A S) (S i)) (Measure.pi fun _ : Fin m => D))
    {w : E} (hw : w ∈ K) (hwB : ‖w‖ ≤ B) (hwint : Integrable (ℓ w) D) :
    ∫ S, trueRisk ℓ D (A S) ∂(Measure.pi fun _ : Fin m => D) ≤ trueRisk ℓ D w + ε := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hr0 : 0 < r := by rw [hr]; positivity
  have hB2 : B ^ 2 ≠ 0 := by positivity
  -- `r m ≥ 50 β / ε`, so `2β ≤ r m` and `5β / (r m) ≤ ε / 10`.
  have hrm : 50 * (β : ℝ) ≤ ε * (r * m) := by
    have h1 : 150 * (β : ℝ) * B ^ 2 ≤ ε ^ 2 * m := by
      rw [div_le_iff₀ (by positivity)] at hmε
      linarith
    have h2 : ε * (r * m) * (3 * B ^ 2) = ε ^ 2 * m := by
      rw [hr]
      field_simp
    nlinarith [pow_pos hB 2]
  have hβ : 2 * (β : ℝ) ≤ r * m := by
    have : 0 ≤ (1 - ε) * (r * m) := mul_nonneg (by linarith) (by positivity)
    nlinarith [β.2]
  have hc : 5 * (β : ℝ) / (r * m) ≤ ε / 10 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set μ := Measure.pi fun _ : Fin m => D
  have hgap := hA.replaceOneGap_le_tikhonov_of_lipschitzWith_fderiv hK hr0 hconv hdiff hsmooth
    hnonneg hβ D hint'
  have h1 := integral_trueRisk_le_of_replaceOneGap_le D hm hint hint' hgap
  have h2 := hA.integral_empiricalRisk_le (fun _ _ => by positivity) D hm hint' hw hwint
  -- `L_S(A S) ≤ L_S(0) ≤ 1` pointwise, so `𝔼_S [L_S(A S)] ≤ 1`.
  have hfit : ∫ S, empiricalRisk ℓ S (A S) ∂μ ≤ 1 := by
    have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    calc ∫ S, empiricalRisk ℓ S (A S) ∂μ ≤ ∫ _, (1 : ℝ) ∂μ :=
          integral_mono (integrable_empiricalRisk_comp ℓ _ A hint') (integrable_const _)
            fun S => by
              have h := hA.le S h0
              have hR : 0 ≤ r * ‖A S‖ ^ 2 := by positivity
              have hL0 : empiricalRisk ℓ S 0 ≤ 1 := by
                rw [empiricalRisk_def]
                exact Finset.expect_le Finset.univ_nonempty fun j _ => hle (S j)
              norm_num at h
              linarith
      _ = 1 := by rw [integral_const, probReal_univ, one_smul]
  have hfit0 : 0 ≤ ∫ S, empiricalRisk ℓ S (A S) ∂μ :=
    integral_nonneg fun S => by
      rw [empiricalRisk_def]
      exact Finset.expect_nonneg fun j _ => hnonneg _ _
  have hrw : r * ‖w‖ ^ 2 ≤ ε / 3 := by
    calc r * ‖w‖ ^ 2 ≤ r * B ^ 2 := by gcongr
      _ = ε / 3 := by rw [hr]; field_simp
  have hcE : 5 * (β : ℝ) / (r * m) * ∫ S, empiricalRisk ℓ S (A S) ∂μ ≤ ε / 10 := by
    calc 5 * (β : ℝ) / (r * m) * ∫ S, empiricalRisk ℓ S (A S) ∂μ ≤ ε / 10 * 1 :=
          mul_le_mul hc hfit hfit0 (by positivity)
      _ = ε / 10 := mul_one _
  linarith

end Tikhonov

end Cslib.MachineLearning
