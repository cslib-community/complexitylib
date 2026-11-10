/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Computability.LogSpaceDerandomization.ScheduledProductMean
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for coupled product errors

An actual correction edge `0 → 1` and dense edge `1 → 2` have weights `1` in the first
version and `16` in the second. Their usage channels use the same Boolean seed, so their
masks are perfectly correlated. The product-root error has positive fourth power `81 / 2`,
while the source normalizations `u = 1/3`, `f = 1` make the release factor three.
-/

namespace ComplexityTests.ProductError

open Finset Matrix Cslib
open scoped BigOperators

private abbrev full {α : Type*} (_ : α) (_ : Fin 3) : Prop := True
private abbrev mask (σ : Bool) (_ : Fin 3) : Prop := σ = true

private noncomputable def left (w : ℝ) (x z : Fin 3) : ℝ :=
  if x = 0 ∧ z = 1 then w else 0

private noncomputable def right (w : ℝ) (z y : Fin 3) : ℝ :=
  if z = 1 ∧ y = 2 then w + 1 else 0

private noncomputable def score (v _ : ℝ) : ℝ := if v = 0 then 0 else 1
private noncomputable def gate (r : ℝ) : ℝ := if r < 1 then 1 else 0
private noncomputable def Q (v : ℝ) : ℝ := max v 0
private noncomputable def k (v : ℝ) : ℝ := max (v - 1) 0

private theorem gate_nonneg (r : ℝ) : 0 ≤ gate r := by
  unfold gate
  split_ifs <;> norm_num

private theorem gate_le_one (r : ℝ) : gate r ≤ 1 := by
  unfold gate
  split_ifs <;> norm_num

private theorem gate_zero (r : ℝ) (hr : 1 ≤ r) : gate r = 0 := ite_eq_right (not_lt.mpr hr)

private theorem score_one (v r : ℝ) (hv : Q v ≠ 0) (_ : (1 : ℝ) ≠ 0) : score v r = 1 := by
  have hv0 : v ≠ 0 := fun h => hv (by simp [Q, h])
  exact ite_eq_right hv0

private theorem incoming_one (w : ℝ) (z : Fin 3) :
    incomingGate score gate 3 2 1 (left w) univ univ z = 1 := by
  have hcard : #{x : Fin 3 | 1 ≤ auxScore score 3 1 (left w) univ x z} ≤ 1 := by
    refine card_le_one.2 fun x hx x' hx' => ?_
    have hx0 : x = 0 := by
      by_contra h
      norm_num [auxScore, score, left, h] at hx
    have hx'0 : x' = 0 := by
      by_contra h
      norm_num [auxScore, score, left, h] at hx'
    exact hx0.trans hx'0.symm
  have hlt : kthLargest 2 univ (fun x => auxScore score 3 1 (left w) univ x z) < 1 := by
    exact lt_of_not_ge fun h => by
      have := (le_kthLargest_iff (by decide) zero_lt_one).mp h
      omega
  exact ite_eq_left hlt

private theorem row_one (w : ℝ) (z : Fin 3) : rowGate gate 2 1 (right w) univ z = 1 := by
  have hcard : #{y : Fin 3 | 1 ≤ right w z y / 1} ≤ 1 := by
    refine card_le_one.2 fun y hy y' hy' => ?_
    have hy2 : y = 2 := by
      by_contra h
      norm_num [right, h] at hy
    have hy'2 : y' = 2 := by
      by_contra h
      norm_num [right, h] at hy'
    exact hy2.trans hy'2.symm
  have hlt : kthLargest 2 univ (fun y => right w z y / 1) < 1 := by
    exact lt_of_not_ge fun h => by
      have := (le_kthLargest_iff (by decide) zero_lt_one).mp h
      omega
  exact ite_eq_left hlt

private noncomputable def correction (w : ℝ) (σ : Bool) (x z : Fin 3) : ℝ :=
  correctionAtom score gate 3 2 1 (left w) full full mask Q (fun _ => 1)
    (fun _ => 1) (fun _ => 1) ((), σ) x z

private noncomputable def dense (w : ℝ) (σ : Bool) (z y : Fin 3) : ℝ :=
  denseAtom full mask k (fun _ => 1) gate 2 1 (right w) σ z y

private theorem correction_eq (w : ℝ) (σ : Bool) (x z : Fin 3) :
    correction w σ x z = if σ = true then Q (left w x z) else 0 := by
  have hn : correctionNormalizer (ι := Unit) score gate 3 2 1 (left w) full full mask (fun _ => 1)
      (fun _ => 1) x z = 1 := by
    simp [correctionNormalizer, correctionPrep, rowGate, full, mask, incoming_one, filter_eq']
  norm_num [correction, correctionAtom, rowGate, full, mask, incoming_one, hn]

private theorem dense_eq (w : ℝ) (σ : Bool) (z y : Fin 3) :
    dense w σ z y = if σ = true then k (right w z y) else 0 := by
  have hn : atomNormalizer full mask (fun _ => 1) gate 2 1 (right w) z y = 1 := by
    simp [atomNormalizer, atomPrep, full, mask, row_one, filter_eq']
  norm_num [dense, denseAtom, full, mask, row_one, hn]

private noncomputable def sample (w : ℝ) (σ : Bool) (x y : Fin 3) : ℝ :=
  ∑ z ∈ ({z | mask σ z} : Finset (Fin 3)), correction w σ x z * dense w σ z y

private theorem sample_eq (w : ℝ) (σ : Bool) (x y : Fin 3) :
    sample w σ x y = if σ = true ∧ x = 0 ∧ y = 2 then (max w 0) ^ 2 else 0 := by
  fin_cases σ <;> fin_cases x <;> fin_cases y <;>
    norm_num [sample, mask, correction_eq, dense_eq, Q, k, left, right, Fin.sum_univ_three,
      pow_two]

example : sample 1 true 0 2 = 1 ∧ sample 16 true 0 2 = 256 ∧ sample 16 false 0 2 = 0 := by
  norm_num [sample_eq]

private theorem root_sixteen : (16 : ℝ) ^ (4⁻¹ : ℝ) = 2 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num]
  exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)

private theorem root_two_fifty_six : (256 : ℝ) ^ (4⁻¹ : ℝ) = 4 := by
  rw [show (256 : ℝ) = 4 ^ 4 by norm_num]
  exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)

private theorem product_error : rootDistPow 4 3 (1 / 3) (fun (_ : Bool) => full ()) mask
    (sample 1) (sample 16) = 81 / 2 := by
  norm_num [rootDistPow, rowNormPow, full, mask, sample_eq, expect_eq_sum_div_card,
    sum_filter, Fin.sum_univ_three, Fintype.sum_bool, root_two_fifty_six]

private theorem left_error : rootDistPow 4 3 (1 / 3) (fun (_ : Bool) => full ()) mask
    (correction 1) (correction 16) = 1 / 2 := by
  norm_num [rootDistPow, rowNormPow, full, mask, correction_eq, Q, left,
    expect_eq_sum_div_card, sum_filter, Fin.sum_univ_three, Fintype.sum_bool, root_sixteen]

private theorem right_error : rootDistPow 4 3 1 mask mask (dense 1) (dense 16) = 1 / 6 := by
  norm_num [rootDistPow, rowNormPow, mask, dense_eq, k, right, expect_eq_sum_div_card,
    sum_filter, Fin.sum_univ_three, Fintype.sum_bool, root_sixteen]

-- Both caps are discharged from the actual atom gates. The two seed maps are correlated.
private theorem actual_atom_bound :
    rootDistPow 4 3 (1 / 3) (fun (_ : Bool) => full ()) mask (sample 1) (sample 16) ≤
      16384 * (4 * rootDistPow 4 3 (1 / 3) (fun (_ : Bool) => full ()) mask
          (correction 1) (correction 16) +
        192 * rootDistPow 4 3 1 mask mask (dense 1) (dense 16)) := by
  have h := correctionAtom_denseAtom_rootDistPow_le
    (X := fun (_ : Unit) => full ()) (Z := fun (_ : Bool) => full ()) (Zt := mask)
    (Y := fun (_ : Bool) => full ()) (Yt := mask)
    (I := score) (τ := gate) (Q := Q) (hF := fun _ => 1) (ρF := fun _ => 1)
    (k := k) (hB := fun _ => 1) (ρB := gate) (KF := 3) (Kc := 2) (KB := 2)
    (s := 4) (N := 3) (u := 1 / 3) (f := 1) (b := 1)
    (fun σ : Bool => ((), σ)) id (fun _ => left 1) (fun _ => left 16)
    (fun _ => right 1) (fun _ => right 16) (fun _ _ => 1) (fun _ _ => 1)
    (by decide) (by norm_num) (by norm_num) (by norm_num)
    (fun v => le_max_right v 0) (fun v => le_max_right (v - 1) 0)
    (fun _ => zero_le_one) (fun _ => le_rfl) gate_nonneg gate_le_one gate_nonneg gate_le_one
    (fun _ _ => zero_le_one) (fun _ _ => zero_le_one) (fun _ _ => le_rfl)
    (AF := 16) (AB := 1) (by norm_num) (by norm_num)
    (fun _ x z => by fin_cases x <;> fin_cases z <;> norm_num [Q, left])
    (fun _ z y => by fin_cases z <;> fin_cases y <;> norm_num [k, right])
    (by decide) score_one (gF := 1) le_rfl gate_zero (fun _ _ _ => True.intro)
    (by decide) (eB := 1) (gB := 1) zero_le_one
    (fun v hv => max_eq_right (sub_nonpos.mpr hv)) le_rfl gate_zero
  norm_num only [Nat.reduceSub, Nat.reduceMul, pow_succ, pow_zero, one_mul, mul_one,
    one_div_div, div_one, id_eq, Prod.fst, Prod.snd] at h
  exact h

-- The positive left side and unequal source normalizations are evaluated independently.
example : (81 / 2 : ℝ) ≤ 557056 := by
  have h := actual_atom_bound
  rw [product_error, left_error, right_error] at h
  convert h using 1
  norm_num


/-! The scheduled mean uses the same varying, correlated samples. The child hypotheses are
checked numerical root moments, rather than assumed product error. The last child budget is 62. -/

open Cslib.LogSpaceEstimation

private theorem accuracy_large_enough (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    1 ≤ 16 * (2 : ℝ) ^ (-precision 16 1 62 0 1 r) := by
  have hlog := Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) hr.le hr1
  have hp : -4 ≤ -precision 16 1 62 0 1 r := by
    norm_num only [precision, Real.logb_one, Nat.cast_ofNat, Nat.cast_zero, mul_zero, sub_zero,
      zero_add]
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp
  have hbase : (2 : ℝ) ^ (-4 : ℝ) = 1 / 16 := by norm_num
  rw [hbase] at hpow
  linarith

private noncomputable def scheduledPayment : ℝ :=
  (2 : ℝ) ^ (-precision 16 1 64 1 (1 / 2) (1 / 3) - 1 + 1 / 16) * scaleMajorant 1

private theorem scheduled_mean_bound :
    rootDistPow 4 3 (1 / 3) (fun (_ : Bool) => full ()) mask
      (fun _ x y => 2 * conditionalTableMean (fun (_ : Bool) => full ()) mask (sample 1) x y)
      (fun _ x y => 2 * conditionalTableMean (fun (_ : Bool) => full ()) mask (sample 16) x y) ≤
      (2048 * 16384 : ℝ) *
        (4 * (16 * (2 : ℝ) ^ (-Real.logb 2 (1 / 2) / 2) * scheduledPayment) ^ 4 +
          64 * (16 * scheduledPayment) ^ 4) := by
  have h := scheduled_correctionAtom_denseAtom_mean_le
    (X := fun (_ : Unit) => full ()) (Z := fun (_ : Bool) => full ()) (Zt := mask)
    (Y := fun (_ : Bool) => full ()) (Yt := mask)
    (I := score) (τ := gate) (Q := Q) (hF := fun _ => 1) (ρF := fun _ => 1)
    (k := k) (hB := fun _ => 1) (ρB := gate) (KF := 3) (Kc := 2) (KB := 2)
    (N := 3) (u := 1 / 3) (f := 1) (b := 1)
    (fun σ : Bool => ((), σ)) id (fun _ => left 1) (fun _ => left 16)
    (fun _ => right 1) (fun _ => right 16) (fun _ _ => 1) (fun _ _ => 1)
    (by norm_num) (by norm_num) (by norm_num)
    (fun v => le_max_right v 0) (fun v => le_max_right (v - 1) 0)
    (fun _ => zero_le_one) (fun _ => le_rfl) gate_nonneg gate_le_one gate_nonneg gate_le_one
    (fun _ _ => zero_le_one) (fun _ _ => zero_le_one) (fun _ _ => le_rfl)
    (AF := 16) (AB := 1) (by norm_num) (by norm_num)
    (fun _ x z => by fin_cases x <;> fin_cases z <;> norm_num [Q, left])
    (fun _ z y => by fin_cases z <;> fin_cases y <;> norm_num [k, right])
    (by decide) score_one (gF := 1) le_rfl gate_zero (fun _ _ _ => True.intro)
    (by decide) (eB := 1) (gB := 1) zero_le_one
    (fun v hv => max_eq_right (sub_nonpos.mpr hv)) le_rfl gate_zero
    (A := 1) (a := 1 / 2) (c₁ := 1 / 2) (C := 16) (πf := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    64 0 1 1 0 0 (by decide) 1 (by decide) (by decide) (by decide)
    (by norm_num)
  have hleft : rootDistPow 4 3 (1 / 3) (fun (_ : Bool) => full ()) mask
      (correction 1) (correction 16) ≤
      (16 * (2 : ℝ) ^ (-precision 16 1 62 0 1 (1 / 3))) ^ 4 := by
    rw [left_error]
    exact (by norm_num : (1 / 2 : ℝ) ≤ 1).trans
      (one_le_pow₀ (accuracy_large_enough (1 / 3) (by norm_num) (by norm_num)))
  have hright : rootDistPow 4 3 1 mask (fun (_ : Bool) => full ()) (dense 1) (dense 16) ≤
      (16 * (2 : ℝ) ^ (-precision 16 1 62 0 1 1)) ^ 4 := by
    have hbroad : rootDistPow 4 3 1 mask (fun (_ : Bool) => full ())
        (dense 1) (dense 16) = 1 / 6 := by
      norm_num [rootDistPow, rowNormPow, mask, full, dense_eq, k, right,
        expect_eq_sum_div_card, sum_filter, Fin.sum_univ_three, Fintype.sum_bool, root_sixteen]
    rw [hbroad]
    exact (by norm_num : (1 / 6 : ℝ) ≤ 1).trans
      (one_le_pow₀ (accuracy_large_enough 1 (by norm_num) (by norm_num)))
  have hbound := h (by simpa only [show lastBudget 64 0 1 1 = 62 from rfl, Nat.cast_one,
      mul_one, rootDistPow, rowNormPow, correction, full] using hleft)
    (by simpa only [show lastBudget 64 0 1 1 = 62 from rfl, Nat.cast_one,
      mul_one, rootDistPow, rowNormPow, dense, full, id_eq] using hright)
  norm_num only [Nat.cast_one, Nat.cast_zero, mul_one, zero_div, add_zero, div_one,
    id_eq, Prod.fst, Prod.snd] at hbound
  simpa only [rootDistPow, rowNormPow, conditionalTableMean,
    scheduledPayment, sample, correction, dense, full,
    show (2048 * 16384 : ℝ) = 33554432 by norm_num] using hbound

-- The conditional mean error is positive, and differs from the unaveraged product error.
private theorem scheduled_mean_error : rootDistPow 4 3 (1 / 3) (fun (_ : Bool) => full ()) mask
    (fun _ x y => 2 * conditionalTableMean (fun (_ : Bool) => full ()) mask (sample 1) x y)
    (fun _ x y => 2 * conditionalTableMean (fun (_ : Bool) => full ()) mask (sample 16) x y) =
      81 := by
  have hroot : (512 : ℝ) ^ (4⁻¹ : ℝ) = 4 * (2 : ℝ) ^ (4⁻¹ : ℝ) := by
    rw [show (512 : ℝ) = 256 * 2 by norm_num, Real.mul_rpow (by norm_num) (by norm_num),
      root_two_fifty_six]
  have hpow : ((2 : ℝ) ^ (4⁻¹ : ℝ)) ^ 4 = 2 :=
    Real.rpow_inv_natCast_pow (by norm_num) (by decide)
  norm_num [rootDistPow, rowNormPow, conditionalTableMean, full, mask, sample_eq,
    expect_eq_sum_div_card, filter_eq', Fin.sum_univ_three, Fintype.sum_bool, hroot]
  rw [show (1 / 4 : ℝ) = 4⁻¹ by norm_num, hroot,
    show (2 : ℝ) ^ (4⁻¹ : ℝ) - 4 * (2 : ℝ) ^ (4⁻¹ : ℝ) =
      -3 * (2 : ℝ) ^ (4⁻¹ : ℝ) by ring, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _), mul_pow, hpow]
  norm_num

-- The derived scheduled estimate bounds the explicitly positive actual mean error.
example : (81 : ℝ) ≤ (2048 * 16384 : ℝ) *
    (4 * (16 * (2 : ℝ) ^ (-Real.logb 2 (1 / 2) / 2) * scheduledPayment) ^ 4 +
      64 * (16 * scheduledPayment) ^ 4) := by
  have h := scheduled_mean_bound
  rwa [scheduled_mean_error] at h

-- A finer correction child is allowed: endpoint rate 1/2, bin rate 1, parent rate 1/2.
example : binNormCost 4 1 * (2 : ℝ) ^ (Real.logb 2 (1 / (1 / 2)) / 4) *
    (2 : ℝ) ^ (-precision 16 1 (lastBudget 64 0 1 1) 0 (1 / 2) 1) ≤
    (2 : ℝ) ^ (-Real.logb 2 (1 / 2) / 2) *
      ((2 : ℝ) ^ (-precision 16 1 64 1 (1 / 2) (1 / 2) - 1 + 0 / 16 + 1 / 16) *
        scaleMajorant 1) := by
  simpa only [Nat.cast_one, Nat.cast_zero, mul_one, Int.cast_one] using
    scheduled_child_cost_le_of_rate_le (A := 1) (a := 1 / 2) (a' := 1 / 2)
    (b := 1) (c₁ := 1 / 2) (u := 1 / 2) (u' := 1) (by norm_num) 64 0 1 1 0 (by decide) 1
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

-- A negative stage offset is still available; it is not covered by coarse availability.
example : scaleCutoff 1 (-2) < 128 := by
  apply special_correction_available (A := 3) (a := 1) (f := 1 / 4) (u := 1)
    128 1 1 2 (-2) (by decide) (by norm_num) (by decide)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  · have heq : (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by norm_num
    rw [div_one, heq, Real.logb_rpow (by norm_num) (by norm_num)]
    norm_num
  · norm_num [precision]

end ComplexityTests.ProductError
