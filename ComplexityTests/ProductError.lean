/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Foundations.Probability.ProductError
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

end ComplexityTests.ProductError
