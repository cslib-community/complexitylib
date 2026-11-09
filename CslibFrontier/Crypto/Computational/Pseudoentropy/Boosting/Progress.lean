/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Pseudoentropy.Boosting.Potential
public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Expect

/-!
# Progress of hard-core boosting

We average the scalar potential inequalities over a finite source. A predictor with weighted
correlation at least `γ` decreases the average potential by `γδ / 2` when the weight density is
at least `δ`. Moving the threshold costs slightly less than `δ + γδ / 2` under the loop guards.
Together these give progress of at least `γδ² / 8` per iteration after charging for the shift.

The statements allow any finite source distribution. The write-up uses a uniform source.
Margins and votes are real-valued in this analysis; integer vote counts and their efficient
representation are separate implementation obligations.

## Main definitions

* `Cslib.Crypto.Pseudoentropy.Boosting.density`: source-averaged soft weight.
* `Cslib.Crypto.Pseudoentropy.Boosting.averagePotential`: source-averaged scalar potential.

## Main results

* `Cslib.Crypto.Pseudoentropy.Boosting.step_progress`: amortized progress of one valid round.
* `Cslib.Crypto.Pseudoentropy.Boosting.dense_margin_of_iterations`: a dense-set guarantee at
  the finite clock boundary, including equality.
* `Cslib.Crypto.Pseudoentropy.Boosting.clock_sufficient`: a polynomial clock from inverse bounds.

## References

The hard-core boosting argument of [Holenstein, Section 2.2, Figure 2, Claims 2.7 and
2.10–2.13, and Lemma 2.14][Holenstein2005]. Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, with arbitrary finite sources and soft dense sets.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.Boosting

open Cslib.Probability.PMF

variable {α : Type*} [Fintype α]

/-- The total mass of the soft weights under the source distribution. -/
def density (source : PMF α) (rate : ℝ) (margin : α → ℝ) : ℝ :=
  ∑ x, (source x).toReal * weight rate (margin x)

/-- The expected potential of an example drawn from the source. -/
noncomputable def averagePotential (source : PMF α) (rate : ℝ) (margin : α → ℝ) : ℝ :=
  ∑ x, (source x).toReal * potential rate (margin x)

/-- Soft weights have density between zero and one. -/
theorem density_mem_Icc (source : PMF α) (rate : ℝ) (margin : α → ℝ) :
    density source rate margin ∈ Set.Icc 0 1 := by
  exact ⟨Finset.sum_nonneg (fun x _ =>
    mul_nonneg ENNReal.toReal_nonneg (weight_mem_Icc rate (margin x)).1),
    sum_mul_le source _ 1 (fun x => (weight_mem_Icc rate (margin x)).2)⟩

/-- Decreasing every margin cannot decrease the density. -/
theorem density_antitone (source : PMF α) {rate : ℝ} (hrate : 0 ≤ rate)
    {margin margin' : α → ℝ} (hmargin : ∀ x, margin' x ≤ margin x) :
    density source rate margin ≤ density source rate margin' :=
  Finset.sum_le_sum (fun x _ =>
    mul_le_mul_of_nonneg_left (weight_antitone hrate (hmargin x)) ENNReal.toReal_nonneg)

/-- Increasing the threshold restores the density present before the preceding vote.
Together with the no-shift guard, this proves the density invariant of Claim 2.7. -/
theorem density_vote_shift_ge (source : PMF α) {rate : ℝ} (hrate : 0 ≤ rate)
    (margin step : α → ℝ) (hstep : ∀ x, step x ≤ 1) :
    density source rate margin ≤ density source rate (fun x => margin x + step x - 1) :=
  density_antitone source hrate (fun x => by linarith [hstep x])

/-- Before any votes, all examples have full weight. -/
@[simp] theorem density_zero (source : PMF α) (rate : ℝ) :
    density source rate (fun _ => 0) = 1 := by
  simp [density, weight, sum_toReal]

/-- The initial average potential is the area of the triangular weight curve. -/
@[simp] theorem averagePotential_zero (source : PMF α) (rate : ℝ) :
    averagePotential source rate (fun _ => 0) = 1 / (2 * rate) := by
  simp [averagePotential, potential, ← Finset.sum_mul, sum_toReal]

/-- Bounded signed votes cost at most their negative weighted correlation plus `rate / 2`. -/
theorem averagePotential_add_le (source : PMF α) {rate : ℝ} (hrate : 0 < rate)
    (margin step : α → ℝ) (hstep : ∀ x, |step x| ≤ 1) :
    averagePotential source rate (fun x => margin x + step x) ≤
      averagePotential source rate margin -
        (∑ x, (source x).toReal * (weight rate (margin x) * step x)) + rate / 2 := by
  have hpoint (x : α) : potential rate (margin x + step x) ≤
      potential rate (margin x) - weight rate (margin x) * step x + rate / 2 := by
    have hsq : step x ^ 2 ≤ 1 := by
      obtain ⟨hlower, hupper⟩ := abs_le.mp (hstep x)
      nlinarith
    have h := potential_le_quadratic hrate (margin x) (margin x + step x)
    simp only [add_sub_cancel_left] at h
    linarith [mul_le_mul_of_nonneg_left hsq hrate.le]
  simpa only [one_mul, mul_sub, Finset.sum_sub_distrib, averagePotential, add_comm] using
    sum_le_affine source (a := rate / 2) (b := 1)
      (bound := fun x => potential rate (margin x) - weight rate (margin x) * step x)
      (fun x => by simpa only [one_mul, add_comm] using hpoint x)

/-- A predictor with correlation `γ` on a `δ`-dense measure gives the decrease in Claim 2.10.
The correlation hypothesis is unnormalized, so it remains meaningful without division by density. -/
theorem add_predictor_progress (source : PMF α) {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ)
    (margin step : α → ℝ) (hstep : ∀ x, |step x| ≤ 1)
    (hdensity : δ ≤ density source (γ * δ) margin)
    (hcorrelation : γ * density source (γ * δ) margin ≤
      ∑ x, (source x).toReal * (weight (γ * δ) (margin x) * step x)) :
    averagePotential source (γ * δ) (fun x => margin x + step x) ≤
      averagePotential source (γ * δ) margin - γ * δ / 2 := by
  have h := averagePotential_add_le source (mul_pos hγ hδ) margin step hstep
  linarith [mul_le_mul_of_nonneg_left hdensity hγ.le]

/-- Moving the threshold by one has no quadratic cost on examples already below it. -/
theorem averagePotential_shift_le (source : PMF α) {rate : ℝ} (hrate : 0 < rate)
    (margin : α → ℝ) :
    averagePotential source rate (fun x => margin x - 1) ≤
      averagePotential source rate margin + density source rate margin +
        (1 - (source.toOuterMeasure {x | margin x ≤ 0}).toReal) * rate / 2 := by
  classical
  let below (x : α) : ℝ := if margin x ≤ 0 then 1 else 0
  have hbelow : (∑ x, (source x).toReal * below x) =
      (source.toOuterMeasure {x | margin x ≤ 0}).toReal := by
    rw [PMF.toOuterMeasure_apply_fintype, ENNReal.toReal_sum]
    · simp [below, Set.indicator_apply, apply_ite]
    · intro x _
      by_cases hx : margin x ≤ 0 <;> simp [hx, source.apply_ne_top]
  have hpoint (x : α) : potential rate (margin x - 1) ≤
      potential rate (margin x) + weight rate (margin x) + (1 - below x) * rate / 2 := by
    by_cases hx : margin x ≤ 0
    · simp [below, hx, potential_sub_one_of_nonpos rate hx, weight_of_nonpos hrate.le hx]
    · simpa [below, hx] using potential_sub_one_le hrate (margin x)
  simpa only [mul_add, mul_div_assoc, ← mul_assoc, mul_sub, mul_one, Finset.sum_add_distrib,
    ← Finset.sum_mul, Finset.sum_sub_distrib, sum_toReal, hbelow, averagePotential, density] using
    Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
      mul_le_mul_of_nonneg_left (hpoint x)
        (show (0 : ℝ) ≤ (source x).toReal from ENNReal.toReal_nonneg))

/-- The threshold guard and the failure of the stopping test give the cost in Claim 2.11. -/
theorem shift_progress (source : PMF α) {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ)
    (margin : α → ℝ)
    (hguard : density source (γ * δ) margin ≤ δ * (1 + γ * δ / 16))
    (hbelow : 3 * δ / 8 ≤ (source.toOuterMeasure {x | margin x ≤ 0}).toReal) :
    averagePotential source (γ * δ) (fun x => margin x - 1) ≤
      averagePotential source (γ * δ) margin + δ + γ * δ / 2 - γ * δ ^ 2 / 8 := by
  have h := averagePotential_shift_le source (mul_pos hγ hδ) margin
  nlinarith [mul_le_mul_of_nonneg_right hbelow (mul_pos hγ hδ).le]

/-- One loop iteration decreases the potential after charging `δ` for an optional threshold
increase. The guard allows either decision when the estimates' tolerance intervals overlap. -/
theorem step_progress (source : PMF α) {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (margin step : α → ℝ) (hstep : ∀ x, |step x| ≤ 1) (shift : Bool)
    (hguard : shift = true → density source (γ * δ) margin ≤ δ * (1 + γ * δ / 16))
    (hbelow : shift = true → 3 * δ / 8 ≤
      (source.toOuterMeasure {x | margin x ≤ 0}).toReal)
    (hdensity : δ ≤ density source (γ * δ) (fun x => margin x - if shift then 1 else 0))
    (hcorrelation : γ * density source (γ * δ) (fun x => margin x - if shift then 1 else 0) ≤
      ∑ x, (source x).toReal *
        (weight (γ * δ) (margin x - if shift then 1 else 0) * step x)) :
    averagePotential source (γ * δ) (fun x => margin x - (if shift then 1 else 0) + step x) ≤
      averagePotential source (γ * δ) margin + (if shift then δ else 0) - γ * δ ^ 2 / 8 := by
  have h := add_predictor_progress source hγ hδ _ step hstep hdensity hcorrelation
  cases shift
  · simp only [Bool.false_eq_true, ite_false, sub_zero, add_zero] at h ⊢
    nlinarith [mul_nonneg (mul_pos hγ hδ).le (sub_nonneg.mpr hδone)]
  · have hshift := shift_progress source hγ hδ margin (hguard rfl) (hbelow rfl)
    simp only [↓reduceIte] at h ⊢
    linarith

/-- A low potential forces a large signed margin on every dense soft set. This form of
Claim 2.13 uses soft sets and arbitrary finite sources, avoiding any rounding of set sizes. -/
theorem dense_margin_lower_bound (source : PMF α) {rate : ℝ} (hrate : 0 < rate)
    (margin : α → ℝ) (threshold : ℝ) (softSet : α → ℝ)
    (hsoftSet : ∀ x, softSet x ∈ Set.Icc 0 1) :
    (∑ x, (source x).toReal * softSet x) * (1 / (2 * rate) + threshold) ≤
      (∑ x, (source x).toReal * (softSet x * margin x)) +
        averagePotential source rate (fun x => margin x - threshold) := by
  have hpoint (x : α) : softSet x * (1 / (2 * rate) + threshold) ≤
      softSet x * margin x + potential rate (margin x - threshold) := by
    have hlower := mul_le_mul_of_nonneg_left
      (potential_lower_bound hrate (margin x - threshold)) (hsoftSet x).1
    have hupper := mul_le_mul_of_nonneg_right (hsoftSet x).2
      (potential_nonneg hrate (margin x - threshold))
    nlinarith
  simpa only [averagePotential, mul_add, Finset.sum_add_distrib,
    ← mul_assoc, ← Finset.sum_mul] using
    Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
      mul_le_mul_of_nonneg_left (hpoint x)
        (show (0 : ℝ) ≤ (source x).toReal from ENNReal.toReal_nonneg))

/-- Once the accumulated decrease pays for the initial potential, every `δ`-dense soft set
has average signed margin at least that decrease. At `steps` rounds with decrease `γδ² / 8`,
this gives average correctness at least `1 / 2 + γδ² / 16`, sufficient for the stopping test.
Unlike a strict negativity argument, this includes an exact equality at the clock boundary. -/
theorem dense_margin_of_budget (source : PMF α) {rate δ threshold budget : ℝ}
    (hrate : 0 < rate) (hthreshold : 0 ≤ threshold) (margin softSet : α → ℝ)
    (hsoftSet : ∀ x, softSet x ∈ Set.Icc 0 1)
    (hdensity : δ ≤ ∑ x, (source x).toReal * softSet x)
    (hbudget : 1 / (2 * rate) ≤ budget)
    (hprogress : averagePotential source rate (fun x => margin x - threshold) ≤
      1 / (2 * rate) + δ * threshold - budget) :
    (∑ x, (source x).toReal * softSet x) * budget ≤
      ∑ x, (source x).toReal * (softSet x * margin x) := by
  have hlower := dense_margin_lower_bound source hrate margin threshold softSet hsoftSet
  have hmass := sum_mul_le source softSet 1 (fun x => (hsoftSet x).2)
  nlinarith [mul_nonneg (sub_nonneg.mpr hmass) (sub_nonneg.mpr hbudget),
    mul_le_mul_of_nonneg_right hdensity hthreshold]

/-- A clocked sequence of valid progress steps has a positive average margin on every dense
soft set. The hypotheses describe the analysis of a run; they do not assume that its choices
or stopping tests have already been implemented efficiently.

The clock condition is `steps * γ² * δ³ ≥ 4`. For positive integer inverse bounds, a sufficient
clock is `4 * inverseGamma² * inverseDelta³` when `γ ≥ 1 / inverseGamma` and `δ ≥ 1 / inverseDelta`.
At the clock boundary the average correctness over the predictors is at least
`1 / 2 + γδ² / 16`, once signed vote counts are divided by the number of steps. -/
theorem dense_margin_of_iterations (source : PMF α) {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ)
    (margin : ℕ → α → ℝ) (threshold : ℕ → ℝ) (steps : ℕ)
    (hmargin : margin 0 = fun _ => 0) (hthreshold : threshold 0 = 0)
    (hthreshold_nonneg : 0 ≤ threshold steps)
    (hstep : ∀ i < steps,
      averagePotential source (γ * δ) (fun x => margin (i + 1) x - threshold (i + 1)) ≤
        averagePotential source (γ * δ) (fun x => margin i x - threshold i) +
          δ * (threshold (i + 1) - threshold i) - γ * δ ^ 2 / 8)
    (hclock : 4 ≤ steps * γ ^ 2 * δ ^ 3) (softSet : α → ℝ)
    (hsoftSet : ∀ x, softSet x ∈ Set.Icc 0 1)
    (hdensity : δ ≤ ∑ x, (source x).toReal * softSet x) :
    (∑ x, (source x).toReal * softSet x) * (steps * (γ * δ ^ 2 / 8)) ≤
      ∑ x, (source x).toReal * (softSet x * margin steps x) := by
  have hrate := mul_pos hγ hδ
  have hprogress (i : ℕ) (hi : i ≤ steps) :
      averagePotential source (γ * δ) (fun x => margin i x - threshold i) ≤
        1 / (2 * (γ * δ)) + δ * threshold i - i * (γ * δ ^ 2 / 8) := by
    induction i with
    | zero => simp [hmargin, hthreshold]
    | succ i ih =>
      have hprev := ih (by lia)
      have hnext := hstep i (by lia)
      push_cast
      linarith
  apply dense_margin_of_budget source hrate hthreshold_nonneg (margin steps) softSet
    hsoftSet hdensity ?_ (hprogress steps le_rfl)
  apply (div_le_iff₀ (by positivity : 0 < 2 * (γ * δ))).mpr
  nlinarith

/-- Integer upper bounds on the inverse advantage and density give a polynomial round count. -/
theorem clock_sufficient (inverseGamma inverseDelta : ℕ) {γ δ : ℝ}
    (hγ : 1 ≤ inverseGamma * γ) (hδ : 1 ≤ inverseDelta * δ) :
    4 ≤ (4 * inverseGamma ^ 2 * inverseDelta ^ 3 : ℕ) * γ ^ 2 * δ ^ 3 := by
  have hg : 1 ≤ (inverseGamma * γ) ^ 2 := one_le_pow₀ hγ
  have hd : 1 ≤ (inverseDelta * δ) ^ 3 := one_le_pow₀ hδ
  calc
    (4 : ℝ) ≤ 4 * ((inverseGamma * γ) ^ 2 * (inverseDelta * δ) ^ 3) := by
      linarith [one_le_mul_of_one_le_of_one_le hg hd]
    _ = _ := by push_cast; ring

end Cslib.Crypto.Pseudoentropy.Boosting
