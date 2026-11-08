/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.GameTheory.Mechanism.Myerson
public import Complexity.GameTheory.Mechanism.VirtualValue
public import Mathlib.MeasureTheory.Constructions.Pi
import Complexity.Foundations.MeasureTheory.Integral.IntervalPrimitive
import Complexity.Foundations.MeasureTheory.Integral.PiUpdate
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.Linarith

/-!
# Expected revenue equals expected virtual welfare

Bidders' valuations are independent: bidder `i`'s valuation is drawn from `μ i`, which has density
`f i` on `[0, h i]`, and the profile is drawn from the product `Measure.pi μ`. For an allocation
rule `x` that is measurable and bounded on nonnegative profiles, the expected total Myerson payment
equals the expected virtual welfare `∑ᵢ φᵢ(vᵢ) xᵢ(v)` ([Roughgarden2013CS364A], Lecture 5, §2,
eqs. (5)–(6): "expected revenue = expected virtual welfare").

The proof follows Lecture 5, Steps 1–6. For each bidder `i`, condition on the other valuations
and apply the one-dimensional identity
`HasValueDensity.integral_payment_eq_integral_virtualValue_mul` to the allocation curve
`z ↦ xᵢ(z, v₋ᵢ)`. Then integrate over `v₋ᵢ` (`MeasureTheory.integral_integral_update`) and sum
over bidders.

Consequences for mechanisms (`SingleParameter.Mechanism`) that are truthfully played:

* a DSIC mechanism in which a zero bid pays zero has expected revenue equal to the expected virtual
  welfare of its allocation rule;
* a DSIC and individually rational mechanism has expected revenue *at most* the expected virtual
  welfare of its allocation rule. Individual rationality at valuation `0` forces
  `pᵢ(0, v₋ᵢ) ≤ 0`, and Myerson's payment identity does the rest.

Truthful play is justified by DSIC; the revelation principle (Lecture 5, Step 0) is not
formalized. Measurability and boundedness of the allocation rule are explicit hypotheses.

## Main results

* `SingleParameter.integral_myersonPayment_eq`: for one bidder, expected Myerson payment equals
  expected virtual surplus.
* `SingleParameter.integral_sum_myersonPayment_eq`: expected revenue of Myerson's payments equals
  expected virtual welfare.
* `SingleParameter.Mechanism.IsDSIC.integral_sum_payment_eq`: the same for every normalized DSIC
  mechanism.
* `SingleParameter.Mechanism.IsDSIC.integral_sum_payment_le`: for DSIC and IR mechanisms, expected
  revenue is at most expected virtual welfare.

## References

* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
* [R. B. Myerson, *Optimal auction design*][Myerson1981]
-/

open MeasureTheory Set

public section

namespace Cslib.GameTheory.SingleParameter

variable {ι : Type*} [Fintype ι] {μ : ι → Measure ℝ} {f : ι → ℝ → NNReal} {h : ι → ℝ}

/-- Under independent valuations with densities, almost every profile lies in the box
`∏ᵢ [0, hᵢ]`. -/
theorem ae_mem_box [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i)) :
    ∀ᵐ v ∂Measure.pi μ, ∀ i, v i ∈ Icc 0 (h i) := by
  rw [ae_all_iff]
  exact fun i => (Measure.quasiMeasurePreserving_eval μ i).ae (hμ i).ae_mem

/-- Under independent valuations with densities, almost every profile is nonnegative. -/
theorem ae_nonneg [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i)) :
    ∀ᵐ v ∂Measure.pi μ, 0 ≤ v :=
  (ae_mem_box hμ).mono fun _ hv j => (hv j).1

variable [DecidableEq ι] [∀ i, IsProbabilityMeasure (μ i)] {x : (ι → ℝ) → ι → ℝ} {B : ℝ}

omit [Fintype ι] [∀ i, IsProbabilityMeasure (μ i)] in
theorem measurable_myersonPayment (i : ι) (hx : Measurable fun v => x v i) :
    Measurable fun v => myersonPayment x v i :=
  ((measurable_pi_apply i).mul hx).sub
    (measurable_intervalIntegral (G := fun v z => x (Function.update v i z) i)
      (hx.comp measurable_update') measurable_const (measurable_pi_apply i))

theorem integrable_myersonPayment (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i)) (i : ι)
    (hx : Measurable fun v => x v i) (hB : ∀ v, 0 ≤ v → |x v i| ≤ B) :
    Integrable (fun v => myersonPayment x v i) (Measure.pi μ) := by
  refine Integrable.of_bound (measurable_myersonPayment i hx).aestronglyMeasurable
    (h i * B + B * h i) ?_
  filter_upwards [ae_mem_box hμ] with v hv
  have hv0 : 0 ≤ v := fun j => (hv j).1
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB v hv0)
  have h1 : ‖v i * x v i‖ ≤ h i * B := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hv i).1]
    exact mul_le_mul (hv i).2 (hB v hv0) (abs_nonneg _) ((hv i).1.trans (hv i).2)
  have h2 : ‖∫ z in (0 : ℝ)..v i, x (Function.update v i z) i‖ ≤ B * |v i - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun z hz => by
      rw [uIoc_of_le (hv i).1] at hz
      exact hB _ (update_nonneg hv0 i hz.1.le)
  rw [sub_zero, abs_of_nonneg (hv i).1] at h2
  have h3 : B * v i ≤ B * h i := mul_le_mul_of_nonneg_left (hv i).2 hB0
  exact (norm_sub_le _ _).trans (by linarith)

omit [DecidableEq ι] in
theorem integrable_virtualValue_mul (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i)) (i : ι)
    (hx : Measurable fun v => x v i) (hB : ∀ v, 0 ≤ v → |x v i| ≤ B) :
    Integrable (fun v => virtualValue (μ i) (f i) (v i) * x v i) (Measure.pi μ) := by
  have hφ : Integrable (fun v : ι → ℝ => virtualValue (μ i) (f i) (v i)) (Measure.pi μ) :=
    integrable_comp_eval (hμ i).integrable_virtualValue
  refine Integrable.mono' (hφ.norm.mul_const B)
    (((hμ i).measurable_virtualValue.comp (measurable_pi_apply i)).mul hx).aestronglyMeasurable ?_
  filter_upwards [ae_nonneg hμ] with v hv
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB v hv) (norm_nonneg _)

/-- **Expected payment equals expected virtual surplus**, bidder by bidder
([Roughgarden2013CS364A], Lecture 5, §2, Step 5). -/
theorem integral_myersonPayment_eq (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i)) (i : ι)
    (hx : Measurable fun v => x v i) (hB : ∀ v, 0 ≤ v → |x v i| ≤ B) :
    ∫ v, myersonPayment x v i ∂Measure.pi μ =
      ∫ v, virtualValue (μ i) (f i) (v i) * x v i ∂Measure.pi μ := by
  rw [← integral_integral_update μ (integrable_myersonPayment hμ i hx hB) i,
    ← integral_integral_update μ (integrable_virtualValue_mul hμ i hx hB) i]
  refine integral_congr_ae ?_
  filter_upwards [ae_nonneg hμ] with v hv
  have key := (hμ i).integral_payment_eq_integral_virtualValue_mul
    (g := fun z => x (Function.update v i z) i) (hx.comp (measurable_update v)) (B := B)
    fun z hz => hB _ (update_nonneg hv i hz.1)
  simpa only [myersonPayment, Function.update_self, Function.update_idem] using key

/-- **Expected revenue equals expected virtual welfare** ([Roughgarden2013CS364A], Lecture 5, §2,
eqs. (5)–(6)): under Myerson's payments, for any allocation rule that is measurable and bounded on
nonnegative profiles. -/
theorem integral_sum_myersonPayment_eq (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i))
    (hx : ∀ i, Measurable fun v => x v i) (hB : ∀ v, 0 ≤ v → ∀ i, |x v i| ≤ B) :
    ∫ v, ∑ i, myersonPayment x v i ∂Measure.pi μ =
      ∫ v, ∑ i, virtualValue (μ i) (f i) (v i) * x v i ∂Measure.pi μ := by
  rw [integral_finsetSum _ fun i _ => integrable_myersonPayment hμ i (hx i) fun v hv => hB v hv i,
    integral_finsetSum _ fun i _ => integrable_virtualValue_mul hμ i (hx i) fun v hv => hB v hv i]
  exact Finset.sum_congr rfl fun i _ => integral_myersonPayment_eq hμ i (hx i) fun v hv => hB v hv i

/-- **Expected revenue of a normalized DSIC mechanism**: a DSIC mechanism in which a zero bid
pays zero has expected revenue equal to the expected virtual welfare of its allocation rule
([Roughgarden2013CS364A], Lecture 5, eq. (6)). -/
theorem Mechanism.IsDSIC.integral_sum_payment_eq {M : Mechanism ι} (hM : M.IsDSIC)
    (hN : M.IsNormalized) (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i))
    (hx : ∀ i, Measurable fun v => M.allocation v i)
    (hB : ∀ v, 0 ≤ v → ∀ i, |M.allocation v i| ≤ B) :
    ∫ v, ∑ i, M.payment v i ∂Measure.pi μ =
      ∫ v, ∑ i, virtualValue (μ i) (f i) (v i) * M.allocation v i ∂Measure.pi μ := by
  rw [← integral_sum_myersonPayment_eq hμ hx hB]
  refine integral_congr_ae ?_
  filter_upwards [ae_nonneg hμ] with v hv
  exact Finset.sum_congr rfl fun i _ => hM.payment_eq_myersonPayment hN i hv

omit [Fintype ι] [∀ i, IsProbabilityMeasure (μ i)] in
/-- An individually rational mechanism charges a zero bid at most zero. -/
theorem Mechanism.IsIR.payment_update_zero_nonpos {M : Mechanism ι} (hIR : M.IsIR) (i : ι)
    {b : ι → ℝ} (hb : 0 ≤ b) : M.payment (Function.update b i 0) i ≤ 0 := by
  have := hIR i _ (update_nonneg hb i le_rfl)
  simp only [Mechanism.utility, Function.update_self, zero_mul, zero_sub] at this
  linarith

/-- **Expected revenue of a DSIC, IR mechanism is at most its expected virtual welfare.**
Individual rationality at valuation `0` gives `pᵢ(0, v₋ᵢ) ≤ 0`. Myerson's payment identity then
bounds each payment by Myerson's, and expected Myerson revenue is expected virtual welfare. If the
payments are not integrable, the Bochner integral on the left is `0` and the bound still holds,
because Myerson's payments for the monotone rule `M.allocation` are nonnegative. -/
theorem Mechanism.IsDSIC.integral_sum_payment_le {M : Mechanism ι} (hM : M.IsDSIC)
    (hIR : M.IsIR) (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i))
    (hx : ∀ i, Measurable fun v => M.allocation v i)
    (hB : ∀ v, 0 ≤ v → ∀ i, |M.allocation v i| ≤ B) :
    ∫ v, ∑ i, M.payment v i ∂Measure.pi μ ≤
      ∫ v, ∑ i, virtualValue (μ i) (f i) (v i) * M.allocation v i ∂Measure.pi μ := by
  rw [← integral_sum_myersonPayment_eq hμ hx hB]
  by_cases hint : Integrable (fun v => ∑ i, M.payment v i) (Measure.pi μ)
  · refine integral_mono_ae hint
      (integrable_finsetSum _ fun i _ =>
        integrable_myersonPayment hμ i (hx i) fun v hv => hB v hv i) ?_
    filter_upwards [ae_nonneg hμ] with v hv
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hM.payment_eq i hv]
    linarith [hIR.payment_update_zero_nonpos i hv]
  · rw [integral_undef hint]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_nonneg hμ] with v hv
    exact Finset.sum_nonneg fun i _ => myersonPayment_nonneg hM.isMonotone hv i

end Cslib.GameTheory.SingleParameter
