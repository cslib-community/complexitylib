/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.MeasureTheory.Integral.Pi

/-!
# True and empirical risk of a loss

A *learning problem* in the sense of [ShalevShwartzBenDavid2014, Section 3.2.2] consists of a set
`W` of hypotheses (or models), a domain `Z` of examples and a *loss* `ℓ : W → Z → ℝ`, where
`ℓ w z` is the loss of the hypothesis `w` on the example `z`. Classification is the case
`Z = X × Y` with the 0-1 loss, but the examples need not be labelled points. Given a probability
distribution `D` on `Z`, the *true risk* of `w` is its expected loss
`L_D(w) = ∫ ℓ w z ∂D` [ShalevShwartzBenDavid2014, (3.3)], and on a sample `S = (z₁, …, z_m)` its
*empirical risk* is the average loss `L_S(w) = (1 / m) ∑ i, ℓ w (S i)`
[ShalevShwartzBenDavid2014, (3.4)].

The source requires nonnegative losses; nothing here does. The true risk is a Bochner integral,
so it takes the junk value `0` when `ℓ w` is not integrable, and the results that integrate assume
integrability. The empirical risk on the empty sample is `0`.

Convexity enters through the curried losses `fun w => ℓ w z`: if each is convex on a convex set
`K`, so is `L_S` and, for integrable losses, `L_D`. These are the objectives of regularized loss
minimization and of stochastic gradient descent.

## Main definitions

* `Cslib.MachineLearning.trueRisk`: the true risk `L_D(w)`.
* `Cslib.MachineLearning.empiricalRisk`: the empirical risk `L_S(w)`.

## Main results

* `Cslib.MachineLearning.trueRisk_def`, `Cslib.MachineLearning.empiricalRisk_def`: the defining
  equations; the definitions are not exposed.
* `Cslib.MachineLearning.empiricalRisk_eq_sum_div`: the empirical risk as a sum divided by `m`.
* `Cslib.MachineLearning.empiricalRisk_update`: replacing one example changes the empirical risk
  by the change in its loss divided by `m`.
* `Cslib.MachineLearning.integral_empiricalRisk_comp`: for a hypothesis `A S` chosen from the
  sample, the expected empirical risk is the average over `i` of the expected loss of `A S` on
  `S i`.
* `Cslib.MachineLearning.integral_empiricalRisk`: for a fixed hypothesis, the empirical risk on
  `m > 0` i.i.d. examples is an unbiased estimate of the true risk.
* `Cslib.MachineLearning.convexOn_empiricalRisk`, `Cslib.MachineLearning.convexOn_trueRisk`:
  convex losses have convex risks.
* `Cslib.MachineLearning.continuousOn_empiricalRisk`,
  `Cslib.MachineLearning.integrable_empiricalRisk_comp`,
  `Cslib.MachineLearning.measurable_empiricalRisk`: continuity, integrability and measurability of
  the empirical risk follow from those of the losses.
* `Cslib.MachineLearning.trueRisk_mem_Icc`, `Cslib.MachineLearning.empiricalRisk_mem_Icc`: losses
  in `[0, 1]` have risks in `[0, 1]`.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Section 3.2.2
-/

public section

open MeasureTheory Finset
open scoped BigOperators

namespace Cslib.MachineLearning

variable {W Z : Type*}

/-! ### Definitions -/

/-- The **true risk** `L_D(w) = ∫ ℓ w z ∂D` of a hypothesis `w` under a distribution `D` on
examples: the expected loss [ShalevShwartzBenDavid2014, (3.3)]. It is `0` when `ℓ w` is not
`D`-integrable. -/
noncomputable def trueRisk [MeasurableSpace Z] (ℓ : W → Z → ℝ) (D : Measure Z) (w : W) : ℝ :=
  ∫ z, ℓ w z ∂D

theorem trueRisk_def [MeasurableSpace Z] (ℓ : W → Z → ℝ) (D : Measure Z) (w : W) :
    trueRisk ℓ D w = ∫ z, ℓ w z ∂D := by
  rw [trueRisk]

/-- The **empirical risk** `L_S(w) = (1 / m) ∑ i, ℓ w (S i)` of a hypothesis `w` on a sample `S`
of `m` examples: the average loss [ShalevShwartzBenDavid2014, (3.4)]. It is `0` on the empty
sample. -/
noncomputable def empiricalRisk (ℓ : W → Z → ℝ) {m : ℕ} (S : Fin m → Z) (w : W) : ℝ :=
  𝔼 i, ℓ w (S i)

theorem empiricalRisk_def (ℓ : W → Z → ℝ) {m : ℕ} (S : Fin m → Z) (w : W) :
    empiricalRisk ℓ S w = 𝔼 i, ℓ w (S i) := by
  rw [empiricalRisk]

/-! ### The empirical risk -/

/-- The empirical risk is the total loss divided by the sample size. -/
theorem empiricalRisk_eq_sum_div (ℓ : W → Z → ℝ) {m : ℕ} (S : Fin m → Z) (w : W) :
    empiricalRisk ℓ S w = (∑ i, ℓ w (S i)) / m := by
  rw [empiricalRisk_def, Fintype.expect_eq_sum_div_card, Fintype.card_fin]

/-- Replacing the `i`-th example of `S` by `z` changes the empirical risk by
`(ℓ w z - ℓ w (S i)) / m`. -/
theorem empiricalRisk_update (ℓ : W → Z → ℝ) {m : ℕ} (S : Fin m → Z)
    (i : Fin m) (z : Z) (w : W) :
    empiricalRisk ℓ (Function.update S i z) w =
      empiricalRisk ℓ S w + (ℓ w z - ℓ w (S i)) / m := by
  rw [empiricalRisk_eq_sum_div, empiricalRisk_eq_sum_div, ← add_div]
  congr 1
  have h : (fun j => ℓ w (Function.update S i z j)) =
      Function.update (fun j => ℓ w (S j)) i (ℓ w z) :=
    funext fun j => Function.apply_update (fun _ => ℓ w) S i z j
  rw [h, Finset.sum_update_of_mem (mem_univ i), ← Finset.add_sum_erase _ _ (mem_univ i),
    Finset.sdiff_singleton_eq_erase]
  ring

/-- If every loss `fun w => ℓ w (S i)` is convex on `K`, the empirical risk on `S` is convex on
`K`. -/
theorem convexOn_empiricalRisk [AddCommGroup W] [Module ℝ W] {K : Set W} {ℓ : W → Z → ℝ} {m : ℕ}
    {S : Fin m → Z} (hK : Convex ℝ K) (hℓ : ∀ i, ConvexOn ℝ K fun w => ℓ w (S i)) :
    ConvexOn ℝ K (empiricalRisk ℓ S) := by
  refine ⟨hK, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [empiricalRisk_def, smul_eq_mul]
  rw [Finset.mul_expect, Finset.mul_expect, ← Finset.expect_add_distrib]
  exact Finset.expect_le_expect fun i _ => (hℓ i).2 hx hy ha hb hab

/-- If every loss `fun w => ℓ w (S i)` is continuous on `K`, so is the empirical risk on `S`. -/
theorem continuousOn_empiricalRisk [TopologicalSpace W] {K : Set W} {ℓ : W → Z → ℝ} {m : ℕ}
    {S : Fin m → Z} (hℓ : ∀ i, ContinuousOn (fun w => ℓ w (S i)) K) :
    ContinuousOn (empiricalRisk ℓ S) K := by
  simp only [funext (empiricalRisk_eq_sum_div ℓ S)]
  exact (continuousOn_finsetSum _ fun i _ => hℓ i).div_const _

/-- A loss with values in `[0, 1]` has empirical risk in `[0, 1]` on every sample. -/
theorem empiricalRisk_mem_Icc (ℓ : W → Z → ℝ) {m : ℕ} (S : Fin m → Z) {w : W}
    (hℓ : ∀ z, ℓ w z ∈ Set.Icc (0 : ℝ) 1) : empiricalRisk ℓ S w ∈ Set.Icc (0 : ℝ) 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [empiricalRisk_eq_sum_div]
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  rw [empiricalRisk_eq_sum_div]
  refine ⟨div_nonneg (Finset.sum_nonneg fun k _ => (hℓ (S k)).1) hmR.le, ?_⟩
  rw [div_le_one hmR]
  calc ∑ k, ℓ w (S k) ≤ ∑ _k : Fin m, (1 : ℝ) := Finset.sum_le_sum fun k _ => (hℓ (S k)).2
    _ = m := by simp

/-! ### Expected risks -/

variable [MeasurableSpace Z]

/-- For a hypothesis `A S` chosen from the sample, the empirical risk of `A S` is integrable when
its loss on each example is. -/
theorem integrable_empiricalRisk_comp (ℓ : W → Z → ℝ) {m : ℕ} (μ : Measure (Fin m → Z))
    (A : (Fin m → Z) → W) (hint : ∀ i, Integrable (fun S => ℓ (A S) (S i)) μ) :
    Integrable (fun S => empiricalRisk ℓ S (A S)) μ := by
  simp only [empiricalRisk_eq_sum_div]
  exact (integrable_finsetSum _ fun i _ => hint i).div_const _

/-- For a hypothesis `A S` chosen from the sample `S` (under any sample distribution `μ`), the
expected empirical risk of `A S` is the average over `i` of the expected loss of `A S` on the
`i`-th example. -/
theorem integral_empiricalRisk_comp (ℓ : W → Z → ℝ) {m : ℕ} (μ : Measure (Fin m → Z))
    (A : (Fin m → Z) → W) (hint : ∀ i, Integrable (fun S => ℓ (A S) (S i)) μ) :
    ∫ S, empiricalRisk ℓ S (A S) ∂μ = 𝔼 i, ∫ S, ℓ (A S) (S i) ∂μ := by
  simp only [empiricalRisk_eq_sum_div, Fintype.expect_eq_sum_div_card, Fintype.card_fin]
  rw [integral_div, integral_finsetSum _ fun i _ => hint i]

/-- **Unbiasedness of the empirical risk**: for a fixed hypothesis `w` with `D`-integrable loss,
the expected empirical risk on `m > 0` independent examples from a probability distribution `D`
is the true risk. -/
theorem integral_empiricalRisk (ℓ : W → Z → ℝ) (D : Measure Z) [IsProbabilityMeasure D] {m : ℕ}
    (hm : 0 < m) (w : W) (hint : Integrable (ℓ w) D) :
    ∫ S, empiricalRisk ℓ S w ∂(Measure.pi fun _ : Fin m => D) = trueRisk ℓ D w := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have h := integral_empiricalRisk_comp ℓ (Measure.pi fun _ : Fin m => D) (fun _ => w)
    fun i => integrable_comp_eval (i := i) hint
  rw [h, trueRisk_def]
  calc 𝔼 i, ∫ S, ℓ w (S i) ∂(Measure.pi fun _ : Fin m => D) = 𝔼 _i : Fin m, ∫ z, ℓ w z ∂D :=
        Finset.expect_congr rfl fun i _ =>
          integral_comp_eval (μ := fun _ : Fin m => D) (i := i) hint.aestronglyMeasurable
    _ = ∫ z, ℓ w z ∂D := Finset.expect_const univ_nonempty _

/-- If every loss `fun w => ℓ w z` is convex on `K` and `ℓ w` is `D`-integrable for every
`w ∈ K`, the true risk is convex on `K`. -/
theorem convexOn_trueRisk [AddCommGroup W] [Module ℝ W] {K : Set W} {ℓ : W → Z → ℝ}
    {D : Measure Z} (hK : Convex ℝ K) (hℓ : ∀ z, ConvexOn ℝ K fun w => ℓ w z)
    (hint : ∀ w ∈ K, Integrable (ℓ w) D) : ConvexOn ℝ K (trueRisk ℓ D) := by
  rw [show trueRisk ℓ D = fun w => ∫ z, ℓ w z ∂D from funext (trueRisk_def ℓ D)]
  exact integral_convexOn_of_integrand_ae (f := fun z w => ℓ w z) hK
    (Filter.Eventually.of_forall hℓ) hint

/-- The empirical risk of `w` is measurable in the sample when the loss `ℓ w` is measurable. -/
theorem measurable_empiricalRisk {ℓ : W → Z → ℝ} (m : ℕ) {w : W} (hℓ : Measurable (ℓ w)) :
    Measurable fun S : Fin m → Z => empiricalRisk ℓ S w := by
  simp only [empiricalRisk_eq_sum_div]
  exact (Finset.measurable_sum _ fun k _ => hℓ.comp (measurable_pi_apply k)).div_const _

/-- A loss with values in `[0, 1]` has true risk in `[0, 1]` under a probability distribution. -/
theorem trueRisk_mem_Icc (ℓ : W → Z → ℝ) (D : Measure Z) [IsProbabilityMeasure D] {w : W}
    (hℓ : ∀ z, ℓ w z ∈ Set.Icc (0 : ℝ) 1) : trueRisk ℓ D w ∈ Set.Icc (0 : ℝ) 1 := by
  rw [trueRisk_def]
  refine ⟨integral_nonneg fun z => (hℓ z).1, ?_⟩
  calc ∫ z, ℓ w z ∂D ≤ ∫ _, (1 : ℝ) ∂D :=
        integral_mono_of_nonneg (ae_of_all _ fun z => (hℓ z).1) (integrable_const 1)
          (ae_of_all _ fun z => (hℓ z).2)
    _ = 1 := by simp

end Cslib.MachineLearning
