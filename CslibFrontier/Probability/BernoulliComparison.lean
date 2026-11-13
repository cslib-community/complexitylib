/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.BinaryKL
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Comparing bounded i.i.d. means with Bernoulli means

Maurer's reduction [Maurer2004]: for a convex `φ` on `[0, 1]` and i.i.d. random variables
`X₁, …, Xₙ` with values in `[0, 1]` and mean `p`, `𝔼 φ ((X₁ + ⋯ + Xₙ) / n)` is at most the same
expectation for Bernoulli trials with success probability `p`,
`∑ₖ C(n, k) p ^ k (1 - p) ^ (n - k) φ (k / n)`. Pointwise, `x ∈ [0, 1]ⁿ` is a convex combination
of the vertices of the cube, the vertex `T` weighted by `∏_{i ∈ T} xᵢ ∏_{i ∉ T} (1 - xᵢ)`, with
barycenter `x`, so Jensen's inequality bounds `φ` of the mean; independence turns the expected
weights into binomial probabilities.

With `φ = exp (n binaryKL · p)` every binomial term is at most `1`, so
`𝔼 exp (n binaryKL (mean ‖ p)) ≤ n + 1`, the exponential moment behind the PAC-Bayes-kl bound.
[Seeger2002, Appendix A] proves it for Bernoulli trials; the comparison extends it to `[0, 1]`.
[Maurer2004, Theorem 1] sharpens it to `2√n` for `n ≥ 8` using Stirling's formula, which is not
formalized here.

## Main results

* `Cslib.Probability.map_sum_div_card_le_of_convexOn`: the pointwise comparison.
* `Cslib.Probability.lintegral_ofReal_comp_sum_div_le`: the comparison in expectation.
* `Cslib.Probability.lintegral_exp_mul_binaryKL_sum_div_le`: the exponential moment of the binary
  relative entropy of an empirical mean.

## References

* [A. Maurer, *A note on the PAC Bayesian theorem*][Maurer2004]
* [M. Seeger, *PAC-Bayesian generalisation error bounds for Gaussian process
  classification*][Seeger2002]
-/

public section

namespace Cslib.Probability

open MeasureTheory Finset Set
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Expanding `∏ i, (f i + g i)` as a sum over the sets of indices where `f` is chosen. -/
private theorem prod_add_eq_sum_prod_ite (f g : ι → ℝ) :
    ∏ i, (f i + g i) = ∑ T : Finset ι, ∏ i, if i ∈ T then f i else g i := by
  rw [Fintype.prod_add]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_ite]
  congr 1 <;> congr 1 <;> ext <;> simp

private theorem sum_prod_ite_eq_one (x : ι → ℝ) :
    ∑ T : Finset ι, ∏ i, (if i ∈ T then x i else 1 - x i) = 1 := by
  rw [← prod_add_eq_sum_prod_ite]
  simp

private theorem sum_ite_mem_prod_ite (x : ι → ℝ) (j : ι) :
    ∑ T : Finset ι, (if j ∈ T then ∏ i, (if i ∈ T then x i else 1 - x i) else 0) = x j := by
  have h := prod_add_eq_sum_prod_ite x fun i => if i = j then 0 else 1 - x i
  rw [Finset.prod_eq_single j (fun i _ hij => by simp [hij]) (by simp)] at h
  simp only [ite_true, add_zero] at h
  rw [h]
  refine Finset.sum_congr rfl fun T _ => ?_
  split_ifs with hj
  · refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs with hi hij <;> first | rfl | exact absurd (hij ▸ hj) hi
  · exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])).symm

private theorem sum_prod_ite_mul_card (x : ι → ℝ) :
    ∑ T : Finset ι, (∏ i, (if i ∈ T then x i else 1 - x i)) * (#T : ℝ) = ∑ j, x j := by
  calc ∑ T : Finset ι, (∏ i, (if i ∈ T then x i else 1 - x i)) * (#T : ℝ)
      = ∑ T : Finset ι, ∑ j, (if j ∈ T then ∏ i, (if i ∈ T then x i else 1 - x i) else 0) := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = ∑ j, x j := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => sum_ite_mem_prod_ite x j

/-- **Maurer's pointwise comparison**: for `φ` convex on `[0, 1]` and `x ∈ [0, 1]^ι`, `φ` of the
mean of `x` is at most the average of `φ (#T / card ι)` over the vertices `T` of the cube, the
vertex `T` weighted by `∏_{i ∈ T} xᵢ ∏_{i ∉ T} (1 - xᵢ)`. -/
theorem map_sum_div_card_le_of_convexOn {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Icc 0 1) φ) {x : ι → ℝ}
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    φ ((∑ i, x i) / Fintype.card ι) ≤
      ∑ T : Finset ι, (∏ i, if i ∈ T then x i else 1 - x i) * φ (#T / Fintype.card ι) := by
  have hw (T : Finset ι) : 0 ≤ ∏ i, (if i ∈ T then x i else 1 - x i) :=
    Finset.prod_nonneg fun i _ => by split_ifs; exacts [(hx i).1, sub_nonneg.2 (hx i).2]
  have hmem (T : Finset ι) : (#T / Fintype.card ι : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, div_le_one_of_le₀ (by exact_mod_cast Finset.card_le_univ T) (by positivity)⟩
  have h := hφ.map_sum_le (t := Finset.univ) (w := fun T => ∏ i, if i ∈ T then x i else 1 - x i)
    (p := fun T : Finset ι => (#T / Fintype.card ι : ℝ)) (fun T _ => hw T)
    (sum_prod_ite_eq_one x) (fun T _ => hmem T)
  simp only [smul_eq_mul] at h
  refine le_of_eq_of_le ?_ h
  congr 1
  simp_rw [mul_div_assoc', ← Finset.sum_div, sum_prod_ite_mul_card]

section Expectation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}

/-- Under independence, the expected weight of the vertex `T` is the probability
`p ^ #T (1 - p) ^ (card ι - #T)` of `T` for Bernoulli trials with success probability `p = 𝔼 X`. -/
private theorem integral_prod_ite (hX : Integrable X μ) (T : Finset ι) :
    ∫ ω, ∏ i, (if i ∈ T then X (ω i) else 1 - X (ω i)) ∂Measure.pi (fun _ : ι => μ) =
      (∫ ω, X ω ∂μ) ^ #T * (1 - ∫ ω, X ω ∂μ) ^ (Fintype.card ι - #T) := by
  rw [integral_fintype_prod_eq_prod (fun i (z : Ω) => if i ∈ T then X z else 1 - X z)]
  have h (i : ι) : ∫ z, (if i ∈ T then X z else 1 - X z) ∂μ =
      if i ∈ T then ∫ z, X z ∂μ else 1 - ∫ z, X z ∂μ := by
    split_ifs
    · rfl
    · rw [integral_sub (integrable_const 1) hX]
      simp
  simp_rw [h]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.filter_mem_eq_inter,
    Finset.univ_inter]
  congr 2
  rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_sdiff,
    Finset.card_univ]
  simp

omit [DecidableEq ι] in
/-- **Maurer's comparison** [Maurer2004, Lemma 3]: for `φ ≥ 0` convex on `[0, 1]` and i.i.d.
`X (ω i)`, `i ∈ ι`, with values in `[0, 1]` and mean `p`, `𝔼 φ (mean)` is at most the expectation
`∑ₖ C(n, k) p ^ k (1 - p) ^ (n - k) φ (k / n)` for `n = card ι` Bernoulli trials. -/
theorem lintegral_ofReal_comp_sum_div_le {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Icc 0 1) φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (hXm : Measurable X) (hX : ∀ ω, X ω ∈ Icc (0 : ℝ) 1) :
    ∫⁻ ω, ENNReal.ofReal (φ ((∑ i, X (ω i)) / Fintype.card ι)) ∂Measure.pi (fun _ : ι => μ) ≤
      ENNReal.ofReal (∑ k ∈ range (Fintype.card ι + 1), (Fintype.card ι).choose k *
        ((∫ ω, X ω ∂μ) ^ k * (1 - ∫ ω, X ω ∂μ) ^ (Fintype.card ι - k) *
          φ (k / Fintype.card ι))) := by
  classical
  have hXi : Integrable X μ := Integrable.of_mem_Icc 0 1 hXm.aemeasurable (ae_of_all _ hX)
  set w : Finset ι → (ι → Ω) → ℝ := fun T ω => ∏ i, if i ∈ T then X (ω i) else 1 - X (ω i)
  have hw0 (T : Finset ι) (ω : ι → Ω) : 0 ≤ w T ω :=
    Finset.prod_nonneg fun i _ => by
      split_ifs; exacts [(hX _).1, sub_nonneg.2 (hX _).2]
  have hw1 (T : Finset ι) (ω : ι → Ω) : w T ω ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => by split_ifs; exacts [(hX _).1, sub_nonneg.2 (hX _).2])
      fun i _ => by split_ifs; exacts [(hX _).2, sub_le_self _ (hX _).1]
  have hwm (T : Finset ι) : Measurable (w T) :=
    Finset.measurable_prod _ fun i _ => by
      split_ifs
      · exact hXm.comp (measurable_pi_apply i)
      · exact measurable_const.sub (hXm.comp (measurable_pi_apply i))
  have hwi (T : Finset ι) : Integrable (fun ω => w T ω * φ (#T / Fintype.card ι))
      (Measure.pi fun _ : ι => μ) :=
    (Integrable.of_mem_Icc 0 1 (hwm T).aemeasurable
      (ae_of_all _ fun ω => ⟨hw0 T ω, hw1 T ω⟩)).mul_const _
  have hpt (ω : ι → Ω) := map_sum_div_card_le_of_convexOn hφ fun i => hX (ω i)
  calc ∫⁻ ω, ENNReal.ofReal (φ ((∑ i, X (ω i)) / Fintype.card ι)) ∂Measure.pi (fun _ : ι => μ)
      ≤ ∫⁻ ω, ENNReal.ofReal (∑ T : Finset ι, w T ω * φ (#T / Fintype.card ι))
          ∂Measure.pi (fun _ : ι => μ) :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (∫ ω, ∑ T : Finset ι, w T ω * φ (#T / Fintype.card ι)
          ∂Measure.pi (fun _ : ι => μ)) :=
        (ofReal_integral_eq_lintegral_ofReal (integrable_finsetSum _ fun T _ => hwi T)
          (ae_of_all _ fun ω => Finset.sum_nonneg fun T _ =>
            mul_nonneg (hw0 T ω) (hφ0 _))).symm
    _ = _ := by
        congr 1
        rw [integral_finsetSum _ fun T _ => hwi T]
        simp_rw [integral_mul_const, w, integral_prod_ite hXi]
        rw [← Finset.powerset_univ]
        rw [Finset.sum_powerset_apply_card
          (f := fun k => (∫ ω, X ω ∂μ) ^ k * (1 - ∫ ω, X ω ∂μ) ^ (Fintype.card ι - k) *
            φ (k / Fintype.card ι)), Finset.card_univ]
        simp_rw [nsmul_eq_mul]

omit [DecidableEq ι] in
/-- **The exponential moment of the binary relative entropy** [Seeger2002, Appendix A]
[Maurer2004, Lemma 3]: for i.i.d.
`X (ω i)`, `i ∈ ι`, with values in `[0, 1]` and mean `p`, and `n = card ι`,
`𝔼 exp (n binaryKL (mean ‖ p)) ≤ n + 1`. -/
theorem lintegral_exp_mul_binaryKL_sum_div_le (hXm : Measurable X)
    (hX : ∀ ω, X ω ∈ Icc (0 : ℝ) 1) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (Fintype.card ι *
        binaryKL ((∑ i, X (ω i)) / Fintype.card ι) (∫ ω, X ω ∂μ)))
      ∂Measure.pi (fun _ : ι => μ) ≤ ENNReal.ofReal (Fintype.card ι + 1) := by
  have hXi : Integrable X μ := Integrable.of_mem_Icc 0 1 hXm.aemeasurable (ae_of_all _ hX)
  have hp : (∫ ω, X ω ∂μ) ∈ Icc (0 : ℝ) 1 :=
    ⟨integral_nonneg fun ω => (hX ω).1, by
      simpa using integral_mono hXi (integrable_const 1) fun ω => (hX ω).2⟩
  refine (lintegral_ofReal_comp_sum_div_le (convexOn_exp_mul_binaryKL hp (Nat.cast_nonneg _))
    (fun _ => (Real.exp_pos _).le) hXm hX).trans (ENNReal.ofReal_le_ofReal ?_)
  calc ∑ k ∈ range (Fintype.card ι + 1), ((Fintype.card ι).choose k : ℝ) *
        ((∫ ω, X ω ∂μ) ^ k * (1 - ∫ ω, X ω ∂μ) ^ (Fintype.card ι - k) *
          Real.exp (Fintype.card ι * binaryKL (k / Fintype.card ι) (∫ ω, X ω ∂μ)))
      ≤ ∑ k ∈ range (Fintype.card ι + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun k hk => by
          rw [← mul_assoc, ← mul_assoc]
          exact choose_mul_pow_mul_exp_binaryKL_le_one hp
            (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
    _ = Fintype.card ι + 1 := by simp

end Expectation

end Cslib.Probability
