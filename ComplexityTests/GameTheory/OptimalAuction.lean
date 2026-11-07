/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.GameTheory.Mechanism.OptimalAuction

/-!
# Myerson's optimal auction clients

The uniform distribution on `[0, 1]`: its density, regularity, virtual valuation and reserve price
`1/2`. Concrete payments of the Vickrey auction with reserve price `1/2`. The plain Vickrey auction
is not a virtual-welfare maximizer. Myerson's theorem compares Vickrey with and without reserve for
two i.i.d. uniform bidders, so its hypotheses are satisfiable.
-/

namespace ComplexityTests.GameTheory.OptimalAuction

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

end ComplexityTests.GameTheory.OptimalAuction
