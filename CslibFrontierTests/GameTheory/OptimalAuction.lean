/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.GameTheory.Mechanism.OptimalAuction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Myerson's optimal auction clients

The uniform distribution on `[0, 1]`: its density, regularity, virtual valuation and reserve price
`1/2`. Concrete payments of the Vickrey auction with reserve price `1/2`. The plain Vickrey auction
is not a virtual-welfare maximizer. Myerson's theorem compares Vickrey with and without reserve for
two i.i.d. uniform bidders, so its hypotheses are satisfiable. The rising density `2v` on `[0, 1]`
fails `IsRegular` for every choice of its value at `0`, which illustrates the endpoint convention.
-/

namespace CslibFrontierTests.GameTheory.OptimalAuction

open MeasureTheory Set Cslib.GameTheory Cslib.GameTheory.SingleParameter
  Cslib.GameTheory.SingleParameter.Vickrey

/-- The uniform distribution on `[0, 1]`. -/
noncomputable abbrev unif : Measure ℝ := volume.restrict (Icc 0 1)

/-- The virtual valuation of the uniform distribution. -/
noncomputable abbrev unifVirtualValue : ℝ → ℝ := virtualValue unif fun _ => 1

instance : IsProbabilityMeasure unif :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]⟩

/-! ### The uniform distribution -/

/-- The uniform distribution has density `1` and is regular, `φ(3/4) = 1/2`, and the reserve price
is `1/2`. -/
example : HasValueDensity unif (fun _ => 1) 1 ∧ IsRegular unif (fun _ => 1) 1 ∧
    unifVirtualValue (3 / 4) = 1 / 2 ∧ reservePrice unifVirtualValue = 1 / 2 := by
  refine ⟨hasValueDensity_uniform, isRegular_uniform, ?_, reservePrice_uniform⟩
  have h : unifVirtualValue (3 / 4) = 2 * (3 / 4) - 1 :=
    virtualValue_uniform ⟨by norm_num, by norm_num⟩
  rw [h]
  norm_num

/-- `0` is not a reserve threshold: `φ(1/4) = -1/2 < 0`. -/
example : ¬ IsReserveThreshold unifVirtualValue 0 := by
  intro h
  have := isReserveThreshold_uniform.2.2 _ (by norm_num) (h.2.1 (1 / 4) (by norm_num))
  norm_num at this

/-! ### Vickrey with reserve price `1/2` -/

theorem unifVirtualValue_monotoneOn : MonotoneOn unifVirtualValue (Ici 0) :=
  (isRegular_uniform.strictMonoOn_Ici hasValueDensity_uniform).monotoneOn

/-- Bids `(0.3, 0.4)` are both below the reserve, so the item is not sold. -/
example : reserveAllocation unifVirtualValue ![(3 / 10 : ℝ), 2 / 5] 0 = 0 ∧
    reserveAllocation unifVirtualValue ![(3 / 10 : ℝ), 2 / 5] 1 = 0 := by
  refine ⟨reserveAllocation_eq_zero_iff.2 fun h => ?_, reserveAllocation_eq_zero_iff.2 fun h => ?_⟩
  · have := isReserveThreshold_uniform.2.2 _ (by norm_num) h.2
    norm_num at this
  · have := isReserveThreshold_uniform.2.2 _ (by norm_num) h.2
    norm_num at this

/-- Bids `(0.6, 0.2)`: bidder `0` wins and pays the reserve price `1/2`. -/
example : reserveAllocation unifVirtualValue ![(3 / 5 : ℝ), 1 / 5] 0 = 1 ∧
    myersonPayment (reserveAllocation unifVirtualValue) ![(3 / 5 : ℝ), 1 / 5] 0 = 1 / 2 := by
  have hw : Wins ![(3 / 5 : ℝ), 1 / 5] 0 := by
    intro j hj
    fin_cases j
    · exact absurd rfl hj
    · norm_num
  have hb : 0 ≤ ![(3 / 5 : ℝ), 1 / 5] := fun i => by fin_cases i <;> norm_num
  have h1 : reserveAllocation unifVirtualValue ![(3 / 5 : ℝ), 1 / 5] 0 = 1 :=
    reserveAllocation_eq_one_iff.2 ⟨hw, isReserveThreshold_uniform.2.1 _ (by norm_num)⟩
  refine ⟨h1, ?_⟩
  rw [myersonPayment_reserveAllocation unifVirtualValue_monotoneOn isReserveThreshold_uniform hb,
    h1, mul_one]
  refine max_eq_left (highestOtherBid_le_iff.2 ⟨by norm_num, fun j hj => ?_⟩)
  fin_cases j
  · exact absurd rfl hj
  · norm_num

/-- Bids `(0.7, 0.9)`: bidder `1` wins and pays the other bid `0.7`. Bidder `0` pays nothing. -/
example : reserveAllocation unifVirtualValue ![(7 / 10 : ℝ), 9 / 10] 1 = 1 ∧
    myersonPayment (reserveAllocation unifVirtualValue) ![(7 / 10 : ℝ), 9 / 10] 1 = 7 / 10 ∧
    myersonPayment (reserveAllocation unifVirtualValue) ![(7 / 10 : ℝ), 9 / 10] 0 = 0 := by
  have hw : Wins ![(7 / 10 : ℝ), 9 / 10] 1 := by
    intro j hj
    fin_cases j
    · norm_num
    · exact absurd rfl hj
  have hb : 0 ≤ ![(7 / 10 : ℝ), 9 / 10] := fun i => by fin_cases i <;> norm_num
  have h1 : reserveAllocation unifVirtualValue ![(7 / 10 : ℝ), 9 / 10] 1 = 1 :=
    reserveAllocation_eq_one_iff.2 ⟨hw, isReserveThreshold_uniform.2.1 _ (by norm_num)⟩
  have h0 : reserveAllocation unifVirtualValue ![(7 / 10 : ℝ), 9 / 10] 0 = 0 :=
    reserveAllocation_eq_zero_iff.2 fun h => absurd (h.1.unique hw) (by decide)
  have hsecond : highestOtherBid ![(7 / 10 : ℝ), 9 / 10] 1 = 7 / 10 := by
    refine le_antisymm (highestOtherBid_le_iff.2 ⟨by norm_num, fun j hj => ?_⟩) ?_
    · fin_cases j
      · norm_num
      · exact absurd rfl hj
    · exact le_of_eq_of_le (by norm_num)
        (le_highestOtherBid (b := ![(7 / 10 : ℝ), 9 / 10]) (i := 1) (j := 0) (by decide))
  refine ⟨h1, ?_, ?_⟩
  · rw [myersonPayment_reserveAllocation unifVirtualValue_monotoneOn isReserveThreshold_uniform hb,
      h1, mul_one, hsecond]
    norm_num
  · rw [myersonPayment_reserveAllocation unifVirtualValue_monotoneOn isReserveThreshold_uniform hb,
      h0, mul_zero]

/-- The plain Vickrey auction does not maximize virtual welfare for uniform bidders: on bids
`(1/4, 0)` it sells to bidder `0`, whose virtual valuation `-1/2` is negative. -/
example : ¬ IsVirtualWelfareMaximizing (fun _ => unifVirtualValue) singleItemFeasible
    (allocation (ι := Fin 2)) := by
  intro h
  have hb : 0 ≤ ![(1 / 4 : ℝ), 0] := fun i => by fin_cases i <;> norm_num
  have hw : Wins ![(1 / 4 : ℝ), 0] 0 := by
    intro j hj
    fin_cases j
    · exact absurd rfl hj
    · norm_num
  have hz : (0 : Fin 2 → ℝ) ∈ singleItemFeasible :=
    ⟨fun _ => Or.inl rfl, by simp only [Pi.zero_apply, Finset.sum_const_zero, zero_le_one]⟩
  have hle := (h _ hb).2 0 hz
  rw [Fin.sum_univ_two, Fin.sum_univ_two, allocation_eq_one_iff.2 hw,
    allocation_eq_zero_iff.2 fun h1 => absurd (h1.unique hw) (by decide)] at hle
  simp only [Pi.zero_apply, mul_zero, mul_one, add_zero] at hle
  have := isReserveThreshold_uniform.2.2 _ (by norm_num) hle
  norm_num at this

/-! ### Optimality -/

/-- **Myerson's theorem for two i.i.d. uniform bidders.** The Vickrey auction without reserve has
expected revenue at most that of the Vickrey auction with reserve price `1/2`. The hypotheses of
`integral_sum_payment_le_reserve`, and so of `integral_sum_payment_le_myerson`, are satisfiable. -/
example : ∫ v, ∑ i, (mechanism (ι := Fin 2)).payment v i ∂Measure.pi (fun _ => unif) ≤
    ∫ v, ∑ i, (myerson (reserveAllocation (ι := Fin 2) unifVirtualValue)).payment v i
      ∂Measure.pi (fun _ => unif) :=
  integral_sum_payment_le_reserve hasValueDensity_uniform isRegular_uniform mechanism_isDSIC
    mechanism_isIR (fun v _ => allocation_mem_singleItemFeasible v) measurable_allocation

/-! ### The endpoint convention of `IsRegular` -/

/-- The rising density `f(v) = 2v`. -/
noncomputable def risingDensity (v : ℝ) : NNReal := Real.toNNReal (2 * v)

/-- The distribution on `[0, 1]` with density `2v`, so `F(v) = v²`. -/
noncomputable def rising : Measure ℝ :=
  (volume.restrict (Icc 0 1)).withDensity fun v => (risingDensity v : ENNReal)

/-- The tail of `rising` is `1 − F(v) = 1 − v²` on `[0, 1]`. -/
theorem rising_real_Ioi {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    rising.real (Ioi v) = 1 - v ^ 2 := by
  have hset : Ioi v ∩ Icc (0 : ℝ) 1 = Ioc v 1 := by
    ext w
    simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨h1, -, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨h1, hv0.trans h1.le, h3⟩
  rw [measureReal_def, rising, withDensity_apply _ measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, hset]
  change (∫⁻ a in Ioc v 1, ENNReal.ofReal (2 * a)).toReal = _
  have hint : IntegrableOn (fun a : ℝ => 2 * a) (Ioc v 1) :=
    (continuous_const.mul continuous_id : Continuous fun a : ℝ => 2 * a).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc v 1)] fun a : ℝ => 2 * a :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun a ha => by
      have := ha.1
      change (0 : ℝ) ≤ 2 * a
      linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
    ← intervalIntegral.integral_of_le hv1, intervalIntegral.integral_const_mul, integral_id,
    ENNReal.toReal_ofReal (by nlinarith)]
  ring

/-- Redefining the density at `0` does not change the distribution. -/
theorem hasValueDensity_rising (c : NNReal) :
    HasValueDensity rising (Function.update risingDensity 0 c) 1 where
  measurable := by
    have : Function.update risingDensity 0 c = fun x => if x = 0 then c else risingDensity x := by
      funext x
      exact Function.update_apply _ _ _ _
    rw [this]
    exact Measurable.ite (measurableSet_singleton 0) measurable_const
      (measurable_const.mul measurable_id).real_toNNReal
  eq_withDensity := by
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_of_ae ((countable_singleton (0 : ℝ)).ae_notMem volume)] with x hx
    rw [Function.update_of_ne hx]
  pos := fun v hv => by
    rw [Function.update_of_ne hv.1.ne']
    exact Real.toNNReal_pos.2 (by linarith [hv.1])

/-- **Endpoint convention.** The density `2v` is regular in the sense of Lecture 5, Definition 3.1:
`φ(v) = (3v² − 1)/(2v)` is strictly increasing on `(0, 1]`. But `φ → −∞` as `v → 0⁺`, so for
every choice `c` of the density at `0` (each a valid density for `rising`, by
`hasValueDensity_rising`), `IsRegular` fails at the endpoint `0`. -/
theorem not_isRegular_rising (c : NNReal) :
    ¬ IsRegular rising (Function.update risingDensity 0 c) 1 := by
  intro hreg
  have hφ : ∀ v : ℝ, 0 < v → v ≤ 1 →
      virtualValue rising (Function.update risingDensity 0 c) v = v - (1 - v ^ 2) / (2 * v) := by
    intro v hv hv1
    rw [virtualValue, rising_real_Ioi hv.le hv1, Function.update_of_ne hv.ne', risingDensity,
      Real.coe_toNNReal _ (by linarith)]
  have hφ0 : virtualValue rising (Function.update risingDensity 0 c) 0 = -(c : ℝ)⁻¹ := by
    rw [virtualValue, rising_real_Ioi le_rfl zero_le_one, Function.update_self]
    ring
  rcases eq_or_ne c 0 with rfl | hc
  · have := hreg ⟨le_rfl, zero_le_one⟩ ⟨by norm_num, by norm_num⟩ (by norm_num : (0 : ℝ) < 1 / 2)
    rw [hφ0, hφ _ (by norm_num) (by norm_num)] at this
    norm_num at this
  · set t : ℝ := (c : ℝ)⁻¹ with ht
    have ht0 : 0 < t := inv_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc))
    set v : ℝ := 1 / (8 * (1 + t)) with hv
    have hv0 : 0 < v := by positivity
    have hv8 : v ≤ 1 / 8 := by
      rw [hv, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h2v : 2 * v * (4 * (1 + t)) = 1 := by
      rw [hv]
      field_simp
      ring
    have hq : (1 - v ^ 2) / (2 * v) = 4 * (1 + t) * (1 - v ^ 2) := by
      rw [div_eq_iff (by positivity)]
      linear_combination -(1 - v ^ 2) * h2v
    have := hreg ⟨le_rfl, zero_le_one⟩ ⟨hv0.le, by linarith⟩ hv0
    rw [hφ0, hφ _ hv0 (by linarith), hq] at this
    have hsq : (0 : ℝ) ≤ 1 / 64 - v ^ 2 := by nlinarith
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + t) hsq]

end CslibFrontierTests.GameTheory.OptimalAuction
