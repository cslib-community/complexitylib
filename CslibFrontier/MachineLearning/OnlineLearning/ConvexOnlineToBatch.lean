/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.LossMinimization.Basic
import CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Online-to-batch conversion for convex losses

Run an online learner on an i.i.d. sample `S = (z₀, …, z_{T-1})` from `D`. In round `t` it plays a
point `w t S` of a convex set `K` and then suffers the loss `ℓ (w t S) (S t)`. Since the learner
picks `w t S` before seeing `S t`, the online loss `ℓ (w t S) (S t)` is an unbiased estimate of the
true risk `L_D (w t S)`. By Jensen's inequality the average point `w̄ S = (1 / T) ∑ t, w t S`
then has expected true risk at most the expected average online loss; with a regret bound
`∑ t, (ℓ (w t S) (S t) - ℓ u (S t)) ≤ R` against `u ∈ K` this gives
`𝔼_S L_D (w̄ S) ≤ L_D u + R / T`. This is the in-expectation form of the conversion of
[CesaBianchiConconiGentile2004] and the argument of [ShalevShwartzBenDavid2014, Theorem 14.8]
(locator unverified).

The only property of the learner that is used is that `w t S` does not depend on `S t`
(`hfresh`), which holds when `w t S` depends only on the examples before round `t`. Without it the
bound fails: for the absolute loss `|w - z|` on `ℝ`, playing the current example has online loss
`0`, while every point has positive true risk under a nondegenerate `D`. The conditional step is
`MeasureTheory.integral_apply_eval_eq_integral_integral`: it integrates out `S t` under the
product measure, with no conditional expectations. Integrability comes from a single integrable
`b` that dominates `|ℓ w z|` for all `w ∈ K`.

The bounds are in expectation. High-probability versions (via martingale concentration), the
faster rates for strongly convex losses, and running time are not treated here.

## Main results

* `Cslib.MachineLearning.OnlineLearning.integral_trueRisk_average_le`: the expected true risk of
  the average point is at most the average expected online loss.
* `Cslib.MachineLearning.OnlineLearning.integral_trueRisk_average_le_add`: with a regret bound
  `R` against `u ∈ K`, the expected true risk of the average point is at most `L_D u + R / T`.

## References

* [N. Cesa-Bianchi, A. Conconi, C. Gentile, *On the generalization ability of on-line learning
  algorithms*][CesaBianchiConconiGentile2004]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Chapter 14
-/

public section

open MeasureTheory Finset

namespace Cslib.MachineLearning.OnlineLearning

variable {Z E : Type*} [MeasurableSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {D : Measure Z} [IsProbabilityMeasure D] {K : Set E} {ℓ : E → Z → ℝ} {b : Z → ℝ} {T : ℕ}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E]
  [IsProbabilityMeasure D] in
/-- A loss dominated on `K` by an integrable `b` is integrable at every point of `K`. -/
private theorem integrable_loss (hℓ : Measurable (Function.uncurry ℓ)) (hb : Integrable b D)
    (hbound : ∀ w ∈ K, ∀ z, |ℓ w z| ≤ b z) {w : E} (hw : w ∈ K) : Integrable (ℓ w) D :=
  hb.mono' (hℓ.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hbound w hw z)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
/-- The true risk of a measurable choice `v S ∈ K` is integrable in the sample. -/
private theorem integrable_trueRisk_comp (hℓ : Measurable (Function.uncurry ℓ))
    (hb : Integrable b D) (hbound : ∀ w ∈ K, ∀ z, |ℓ w z| ≤ b z) {v : (Fin T → Z) → E}
    (hv : Measurable v) (hvK : ∀ S, v S ∈ K) :
    Integrable (fun S => trueRisk ℓ D (v S)) (Measure.pi fun _ => D) := by
  simp only [trueRisk_def]
  have hm : Measurable fun p : (Fin T → Z) × Z => ℓ (v p.1) p.2 :=
    hℓ.comp ((hv.comp measurable_fst).prodMk measurable_snd)
  exact Integrable.of_bound hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    (∫ z, b z ∂D) (Filter.Eventually.of_forall fun S =>
      norm_integral_le_of_norm_le hb (Filter.Eventually.of_forall fun z => by
        simpa [Real.norm_eq_abs] using hbound _ (hvK S) z))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
/-- The loss of a measurable choice `v S ∈ K` on the example `S t` is integrable. -/
private theorem integrable_loss_eval (hℓ : Measurable (Function.uncurry ℓ))
    (hb : Integrable b D) (hbound : ∀ w ∈ K, ∀ z, |ℓ w z| ≤ b z) {v : (Fin T → Z) → E}
    (hv : Measurable v) (hvK : ∀ S, v S ∈ K) (t : Fin T) :
    Integrable (fun S => ℓ (v S) (S t)) (Measure.pi fun _ => D) :=
  ((measurePreserving_eval _ t).integrable_comp_of_integrable hb).mono'
    (hℓ.comp (hv.prodMk (measurable_pi_apply t))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun S => by simpa [Real.norm_eq_abs] using hbound _ (hvK S) _)

/-- **Online-to-batch conversion for convex losses.** Let `ℓ · z` be convex on a convex set `K`
and dominated there by an integrable `b`, and let `w t S ∈ K` be measurable in the sample `S` and
independent of the example `S t`. Then the expected true risk of the average
`(1 / T) ∑ t, w t S` is at most the average over `t` of the expected online loss
`ℓ (w t S) (S t)`. -/
theorem integral_trueRisk_average_le (hT : 0 < T) (hK : Convex ℝ K)
    (hℓ : Measurable (Function.uncurry ℓ)) (hconv : ∀ z, ConvexOn ℝ K fun w => ℓ w z)
    (hb : Integrable b D) (hbound : ∀ w ∈ K, ∀ z, |ℓ w z| ≤ b z)
    {w : Fin T → (Fin T → Z) → E} (hwK : ∀ t S, w t S ∈ K) (hwm : ∀ t, Measurable (w t))
    (hfresh : ∀ t S z, w t (Function.update S t z) = w t S) :
    ∫ S, trueRisk ℓ D ((T : ℝ)⁻¹ • ∑ t, w t S) ∂Measure.pi (fun _ => D) ≤
      (T : ℝ)⁻¹ * ∑ t, ∫ S, ℓ (w t S) (S t) ∂Measure.pi (fun _ => D) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hsum1 : ∑ _t : Fin T, (T : ℝ)⁻¹ = 1 := by simp [hTr.ne']
  have hwbarK : ∀ S, (T : ℝ)⁻¹ • ∑ t, w t S ∈ K := fun S => by
    rw [Finset.smul_sum]
    exact hK.sum_mem (fun _ _ => by positivity) hsum1 fun t _ => hwK t S
  have hwbarm : Measurable fun S => (T : ℝ)⁻¹ • ∑ t, w t S :=
    (Finset.measurable_sum Finset.univ fun t _ => hwm t).const_smul _
  -- Jensen's inequality for each sample.
  have hjensen : ∀ S, trueRisk ℓ D ((T : ℝ)⁻¹ • ∑ t, w t S) ≤
      (T : ℝ)⁻¹ * ∑ t, trueRisk ℓ D (w t S) := fun S => by
    have h := (convexOn_trueRisk hK hconv fun v hv => integrable_loss hℓ hb hbound hv).map_sum_le
      (t := Finset.univ) (w := fun _ => (T : ℝ)⁻¹) (p := fun t => w t S)
      (fun _ _ => by positivity) hsum1 fun t _ => hwK t S
    simpa only [Finset.smul_sum, Finset.mul_sum, smul_eq_mul] using h
  -- The online loss is an unbiased estimate of the true risk of the current point.
  have hfresh' : ∀ t, ∫ S, ℓ (w t S) (S t) ∂Measure.pi (fun _ => D) =
      ∫ S, trueRisk ℓ D (w t S) ∂Measure.pi (fun _ => D) := fun t => by
    simp only [trueRisk_def]
    exact integral_apply_eval_eq_integral_integral (fun _ => D) (Φ := fun S z => ℓ (w t S) z)
      (fun S z => by simp only [hfresh]) (integrable_loss_eval hℓ hb hbound (hwm t) (hwK t) t)
  calc ∫ S, trueRisk ℓ D ((T : ℝ)⁻¹ • ∑ t, w t S) ∂Measure.pi (fun _ => D)
      ≤ ∫ S, (T : ℝ)⁻¹ * ∑ t, trueRisk ℓ D (w t S) ∂Measure.pi (fun _ => D) :=
        integral_mono (integrable_trueRisk_comp hℓ hb hbound hwbarm hwbarK)
          ((integrable_finsetSum _ fun t _ =>
            integrable_trueRisk_comp hℓ hb hbound (hwm t) (hwK t)).const_mul _) hjensen
    _ = (T : ℝ)⁻¹ * ∑ t, ∫ S, ℓ (w t S) (S t) ∂Measure.pi (fun _ => D) := by
        rw [integral_const_mul, integral_finsetSum _ fun t _ =>
          integrable_trueRisk_comp hℓ hb hbound (hwm t) (hwK t)]
        simp only [hfresh']

/-- **Online-to-batch conversion for convex losses, regret form** (in expectation;
[CesaBianchiConconiGentile2004]). Under the hypotheses of
`integral_trueRisk_average_le`, if the learner's regret against `u ∈ K` is at most `R` on every
sample, then the expected true risk of the average point is at most `L_D u + R / T`. -/
theorem integral_trueRisk_average_le_add (hT : 0 < T) (hK : Convex ℝ K)
    (hℓ : Measurable (Function.uncurry ℓ)) (hconv : ∀ z, ConvexOn ℝ K fun w => ℓ w z)
    (hb : Integrable b D) (hbound : ∀ w ∈ K, ∀ z, |ℓ w z| ≤ b z)
    {w : Fin T → (Fin T → Z) → E} (hwK : ∀ t S, w t S ∈ K) (hwm : ∀ t, Measurable (w t))
    (hfresh : ∀ t S z, w t (Function.update S t z) = w t S) {u : E} (hu : u ∈ K) {R : ℝ}
    (hR : ∀ S, ∑ t, (ℓ (w t S) (S t) - ℓ u (S t)) ≤ R) :
    ∫ S, trueRisk ℓ D ((T : ℝ)⁻¹ • ∑ t, w t S) ∂Measure.pi (fun _ => D) ≤
      trueRisk ℓ D u + R / T := by
  refine (integral_trueRisk_average_le hT hK hℓ hconv hb hbound hwK hwm hfresh).trans ?_
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hintW : ∀ t : Fin T, Integrable (fun S : Fin T → Z => ℓ (w t S) (S t))
      (Measure.pi fun _ => D) := fun t => integrable_loss_eval hℓ hb hbound (hwm t) (hwK t) t
  have hintU : ∀ t : Fin T, Integrable (fun S : Fin T → Z => ℓ u (S t))
      (Measure.pi fun _ => D) := fun t =>
    integrable_loss_eval hℓ hb hbound measurable_const (fun _ => hu) t
  have hu_eval : ∀ t : Fin T, ∫ S, ℓ u (S t) ∂Measure.pi (fun _ => D) = trueRisk ℓ D u :=
    fun t => by
      rw [trueRisk_def]
      exact integral_comp_eval (integrable_loss hℓ hb hbound hu).aestronglyMeasurable
  have h1 : ∫ S, ∑ t, ℓ (w t S) (S t) ∂Measure.pi (fun _ => D) ≤
      ∫ S, (R + ∑ t, ℓ u (S t)) ∂Measure.pi (fun _ => D) :=
    integral_mono (integrable_finsetSum _ fun t _ => hintW t)
      ((integrable_const R).add (integrable_finsetSum _ fun t _ => hintU t))
      fun S => by have := hR S; rw [Finset.sum_sub_distrib] at this; linarith
  rw [integral_finsetSum _ fun t _ => hintW t,
    integral_add (integrable_const R) (integrable_finsetSum _ fun t _ => hintU t),
    integral_finsetSum _ fun t _ => hintU t] at h1
  simp only [hu_eval, integral_const, probReal_univ, smul_eq_mul, one_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  calc (T : ℝ)⁻¹ * ∑ t, ∫ S, ℓ (w t S) (S t) ∂Measure.pi (fun _ => D)
      ≤ (T : ℝ)⁻¹ * (R + T * trueRisk ℓ D u) := by gcongr
    _ = trueRisk ℓ D u + R / T := by field_simp; ring

end Cslib.MachineLearning.OnlineLearning
