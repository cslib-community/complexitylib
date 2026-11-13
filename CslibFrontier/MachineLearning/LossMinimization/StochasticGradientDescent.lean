/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.LossMinimization.Basic
public import CslibFrontier.MachineLearning.OnlineLearning.OnlineGradientDescent
import CslibFrontier.Foundations.Analysis.Convex.FirstOrder
import CslibFrontier.MachineLearning.OnlineLearning.ConvexOnlineToBatch

/-!
# Stochastic gradient descent for convex Lipschitz losses

*Projected stochastic gradient descent* minimizes the true risk `L_D(w) = ∫ ℓ w z ∂D` of a convex
loss over a convex set `K` from an i.i.d. sample `S = (z₀, …, z_{T-1})`. In step `t` it takes a
subgradient `g x (S t)` of the loss `ℓ · (S t)` at the current point `x` and moves against it:

  `x 0 = x₀`, `x (t + 1) = proj (x t - η t • g (x t) (S t))`,

which is online gradient descent (`OCO.ogd`) on the losses `ℓ · (S t)`. Since `x t` depends only
on `S 0, …, S (t - 1)`, the online-to-batch conversion
(`OnlineLearning.integral_trueRisk_average_le_add`) turns the regret bound of online gradient
descent into a bound on the expected true risk of the average iterate. With step size
`B / (ρ √T)`, subgradients of norm at most `ρ` on `K` and a comparator `u ∈ K` with
`‖x₀ - u‖ ≤ B`, this is
`𝔼_S L_D ((1 / T) ∑ t < T, x t) ≤ L_D u + B ρ / √T`
[ShalevShwartzBenDavid2014, Theorem 14.8, Corollary 14.12] (locators unverified).

`K` may be the whole space with `proj = id`, as in the source's unconstrained analysis; the only
integrability hypothesis is that `ℓ x₀` is `D`-integrable. Measurability of `proj`, `ℓ` and `g`
makes the iterates measurable functions of the sample. For `K = Set.univ` the projection is the
identity; the metric projection onto a nonempty complete convex set is Lipschitz
(`lipschitzWith_metricProjection`), hence measurable.

The bound is in expectation. High-probability bounds, the `log T / T` rates for strongly convex
losses, and running time are not treated here.

## Main definitions

* `Cslib.MachineLearning.sgd`: the iterates of projected stochastic gradient descent on a sample.

## Main results

* `Cslib.MachineLearning.sgd_def`: `sgd` is online gradient descent on the sample's losses.
* `Cslib.MachineLearning.measurable_sgd`, `Cslib.MachineLearning.sgd_update`: each iterate is a
  measurable function of the sample, and iterate `t` does not depend on example `t`.
* `Cslib.MachineLearning.integral_trueRisk_sgd_average_le`: the expected true risk of the average
  of the first `T` iterates is at most `L_D u + B ρ / √T`.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Sections 14.3 and 14.5 (locators unverified)
-/

public section

open MeasureTheory Finset Real Cslib.MachineLearning.OnlineLearning.OCO
open scoped RealInnerProductSpace

namespace Cslib.MachineLearning

variable {Z E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The iterates of **projected stochastic gradient descent** with projection `proj`, step sizes
`η`, subgradient oracle `g` and starting point `x₀` on the sample `S`:
`x (t + 1) = proj (x t - η t • g (x t) (S t))` for `t < T`. After the sample is exhausted the
subgradients are `0`. -/
noncomputable def sgd {T : ℕ} (proj : E → E) (η : ℕ → ℝ) (g : E → Z → E) (x₀ : E)
    (S : Fin T → Z) : ℕ → E :=
  ogd proj η (fun t x => if h : t < T then g x (S ⟨t, h⟩) else 0) x₀

theorem sgd_def {T : ℕ} (proj : E → E) (η : ℕ → ℝ) (g : E → Z → E) (x₀ : E) (S : Fin T → Z) :
    sgd proj η g x₀ S = ogd proj η (fun t x => if h : t < T then g x (S ⟨t, h⟩) else 0) x₀ := by
  rw [sgd]

theorem sgd_mem {T : ℕ} {K : Set E} {proj : E → E} (hP : IsPythagoreanProjection K proj)
    (η : ℕ → ℝ) (g : E → Z → E) {x₀ : E} (hx₀ : x₀ ∈ K) (S : Fin T → Z) (t : ℕ) :
    sgd proj η g x₀ S t ∈ K := by
  rw [sgd_def]
  exact ogd_mem hP hx₀ t

/-- Iterate `t` of stochastic gradient descent depends only on the examples before `t`. -/
theorem sgd_congr {T : ℕ} (proj : E → E) (η : ℕ → ℝ) (g : E → Z → E) (x₀ : E)
    {S S' : Fin T → Z} (t : ℕ) (hS : ∀ i : Fin T, (i : ℕ) < t → S i = S' i) :
    sgd proj η g x₀ S t = sgd proj η g x₀ S' t := by
  induction t with
  | zero => simp [sgd_def]
  | succ t ih =>
    have ih' := ih fun i hi => hS i (by omega)
    simp only [sgd_def] at ih' ⊢
    rw [ogd_succ, ogd_succ, ih']
    by_cases h : t < T
    · simp only [h, dite_true, hS ⟨t, h⟩ (by simp)]
    · simp only [h, dite_false]

/-- Iterate `t` of stochastic gradient descent does not depend on example `t`. -/
theorem sgd_update {T : ℕ} (proj : E → E) (η : ℕ → ℝ) (g : E → Z → E) (x₀ : E)
    (S : Fin T → Z) (t : Fin T) (z : Z) :
    sgd proj η g x₀ (Function.update S t z) t = sgd proj η g x₀ S t :=
  sgd_congr proj η g x₀ t fun _ hi => Function.update_of_ne (Fin.ne_of_lt hi) _ _

variable [MeasurableSpace Z] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Each iterate of stochastic gradient descent is a measurable function of the sample. -/
theorem measurable_sgd {T : ℕ} {proj : E → E} (hproj : Measurable proj) (η : ℕ → ℝ)
    {g : E → Z → E} (hg : Measurable (Function.uncurry g)) (x₀ : E) (t : ℕ) :
    Measurable fun S : Fin T → Z => sgd proj η g x₀ S t := by
  simp only [sgd_def]
  induction t with
  | zero => simp only [ogd_zero]; exact measurable_const
  | succ t ih =>
    simp only [ogd_succ]
    refine hproj.comp (ih.sub (Measurable.const_smul ?_ _))
    by_cases h : t < T
    · simp only [h, dite_true]
      exact hg.comp (ih.prodMk (measurable_pi_apply _))
    · simp only [h, dite_false]
      exact measurable_const

/-- **Stochastic gradient descent for convex Lipschitz losses**
[ShalevShwartzBenDavid2014, Theorem 14.8, Corollary 14.12] (locators unverified). Let `g x z` be
a subgradient of the loss `ℓ · z` at `x ∈ K` relative to the convex set `K`, of norm at most `ρ`,
and let `ℓ x₀` be `D`-integrable. For a comparator `u ∈ K` with `‖x₀ - u‖ ≤ B`, projected SGD with
step size `B / (ρ √T)` on `T` i.i.d. examples from `D` satisfies
`𝔼_S L_D ((1 / T) ∑ t < T, x t) ≤ L_D u + B ρ / √T`. -/
theorem integral_trueRisk_sgd_average_le {T : ℕ} (hT : 0 < T) {D : Measure Z}
    [IsProbabilityMeasure D] {K : Set E} (hK : Convex ℝ K) {proj : E → E}
    (hP : IsPythagoreanProjection K proj) (hproj : Measurable proj) {ℓ : E → Z → ℝ}
    (hℓ : Measurable (Function.uncurry ℓ)) {g : E → Z → E} (hgm : Measurable (Function.uncurry g))
    (hsub : ∀ z, ∀ x ∈ K, ∀ y ∈ K, ℓ x z + ⟪g x z, y - x⟫ ≤ ℓ y z)
    {ρ : ℝ} (hρ : 0 < ρ) (hgρ : ∀ z, ∀ x ∈ K, ‖g x z‖ ≤ ρ)
    {x₀ u : E} (hx₀ : x₀ ∈ K) (hint : Integrable (ℓ x₀) D) (hu : u ∈ K) {B : ℝ} (hB : 0 < B)
    (hx₀u : ‖x₀ - u‖ ≤ B) :
    ∫ S : Fin T → Z, trueRisk ℓ D ((T : ℝ)⁻¹ • ∑ t : Fin T,
        sgd proj (fun _ => B / (ρ * √(T : ℝ))) g x₀ S t) ∂Measure.pi (fun _ => D) ≤
      trueRisk ℓ D u + B * ρ / √(T : ℝ) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hs : 0 < √(T : ℝ) := sqrt_pos.mpr hTr
  set c := B / (ρ * √(T : ℝ)) with hcdef
  have hc : 0 < c := div_pos hB (mul_pos hρ hs)
  -- The iterates and the comparator lie in a ball around `x₀`, on which `ℓ` is dominated.
  set r := ρ * (T * c) + B with hr
  set K' := K ∩ Metric.closedBall x₀ r
  have hK' : Convex ℝ K' := hK.inter (convex_closedBall x₀ r)
  have hiter : ∀ (S : Fin T → Z) (t : Fin T), sgd proj (fun _ => c) g x₀ S t ∈ K' := by
    intro S t
    refine ⟨sgd_mem hP _ g hx₀ S t, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sgd_def]
    have hG : ∀ s, ∀ x ∈ K, ‖(fun t x => if h : t < T then g x (S ⟨t, h⟩) else 0) s x‖ ≤ ρ :=
      fun s x hx => by by_cases h : s < T <;> simp [h, hgρ _ x hx, hρ.le]
    refine (norm_ogd_sub_le hP hx₀ hG (fun _ => hc.le) t).trans ?_
    simp only [sum_const, card_range, nsmul_eq_mul]
    have : (t : ℝ) ≤ T := by exact_mod_cast t.2.le
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hc.le) hρ.le
    linarith [hr]
  have hu' : u ∈ K' := by
    refine ⟨hu, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    have : 0 ≤ ρ * (T * c) := by positivity
    linarith [hr]
  have hbound : ∀ w ∈ K', ∀ z, |ℓ w z| ≤ |ℓ x₀ z| + ρ * r := fun w hw z => by
    have hx₀' : x₀ ∈ K := hx₀
    have hl := abs_sub_le_of_forall_add_inner_le (f := fun x => ℓ x z) (g := fun x => g x z)
      (hsub z) (hgρ z) hw.1 hx₀'
    have hd : ‖w - x₀‖ ≤ r := by rw [← dist_eq_norm]; exact hw.2
    have := mul_le_mul_of_nonneg_left hd hρ.le
    calc |ℓ w z| = |(ℓ w z - ℓ x₀ z) + ℓ x₀ z| := by rw [sub_add_cancel]
      _ ≤ |ℓ w z - ℓ x₀ z| + |ℓ x₀ z| := abs_add_le _ _
      _ ≤ |ℓ x₀ z| + ρ * r := by linarith
  have hb : Integrable (fun z => |ℓ x₀ z| + ρ * r) D := hint.abs.add (integrable_const _)
  have hconv : ∀ z, ConvexOn ℝ K' fun w => ℓ w z := fun z =>
    convexOn_of_forall_add_inner_le hK' fun x hx y hy => hsub z x hx.1 y hy.1
  -- The regret of online gradient descent on each sample.
  have hreg : ∀ S : Fin T → Z, ∑ t : Fin T,
      (ℓ (sgd proj (fun _ => c) g x₀ S t) (S t) - ℓ u (S t)) ≤ ρ * B * √(T : ℝ) := by
    intro S
    have h := ogd_regret_le_fixed_of_norm_sub_le (K := K) (proj := proj) (x₀ := x₀) (u := u)
      (grad := fun t x => if h : t < T then g x (S ⟨t, h⟩) else 0)
      (f := fun t x => if h : t < T then ℓ x (S ⟨t, h⟩) else 0) hP hx₀ hB hρ
      (fun t x hx => by by_cases h : t < T <;> simp [h, hgρ _ x hx, hρ.le])
      (fun t x hx y hy => by by_cases h : t < T <;> simp [h, hsub _ x hx y hy]) hu hx₀u hT
    rw [← Fin.sum_univ_eq_sum_range] at h
    simpa [sgd_def, c] using h
  refine (OnlineLearning.integral_trueRisk_average_le_add hT hK' hℓ hconv hb hbound
    (w := fun t S => sgd proj (fun _ => c) g x₀ S t) (fun t S => hiter S t)
    (fun t => measurable_sgd hproj _ hgm x₀ t) (fun t S z => sgd_update proj _ g x₀ S t z) hu'
    hreg).trans_eq ?_
  congr 1
  rw [div_eq_div_iff hTr.ne' hs.ne']
  linear_combination (ρ * B) * mul_self_sqrt hTr.le

end Cslib.MachineLearning
