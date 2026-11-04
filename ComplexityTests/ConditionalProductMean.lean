/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Foundations.Probability.ConditionalProductMean
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for conditional product means

The source and endpoint use the same two-of-three mask. Estimated factors on a path
`0 → 1 → 2` are coupled: their products are `0` and `32` on the two conditioning draws.
The actual conditional means are `1` and `16`. Source and endpoint densities are `2/3`,
the intermediate density is one, and the coarse coefficient is `b/a = 3/2`.
The resulting integrated fourth-root error is exactly `1/2`.

Further examples identify the true mean of concrete correction and dense atoms through
`TrueSampleMeans`, and check empty slices and an empty environment.
-/

namespace ComplexityTests.ConditionalProductMean

open Finset Matrix Cslib
open scoped BigOperators

private abbrev kept (σ : Fin 3) (_ : Fin 3) : Prop := σ ≠ 2
private abbrev middle (_ _ : Fin 3) : Prop := True

private def F (_ : Fin 3) (x z : Fin 3) : ℝ := if x = 0 ∧ z = 1 then 1 else 0
private def F' (σ x z : Fin 3) : ℝ := if σ = 1 ∧ x = 0 ∧ z = 1 then 8 else 0
private def B (σ z y : Fin 3) : ℝ := if kept σ y ∧ z = 1 ∧ y = 2 then 1 else 0
private def B' (σ z y : Fin 3) : ℝ := if σ = 1 ∧ z = 1 ∧ y = 2 then 4 else 0

private noncomputable def product (A D : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (σ x y : Fin 3) : ℝ := ∑ z, A σ x z * D σ z y

private theorem slice (x y : Fin 3) :
    ({σ | kept σ x ∧ kept σ y} : Finset (Fin 3)) = {0, 1} := by
  change ({σ : Fin 3 | σ ≠ 2 ∧ σ ≠ 2} : Finset (Fin 3)) = {0, 1}
  decide

-- The masks are correlated, so the joint density is `2/3`, not the product `4/9`.
example (x y : Fin 3) : (dens {σ | kept σ x ∧ kept σ y} : ℝ) = 2 / 3 := by
  rw [slice, dens_eq_card_div_card]
  norm_num

private theorem true_mean (x y : Fin 3) :
    conditionalTableMean kept kept (product F B) x y = if x = 0 ∧ y = 2 then 1 else 0 := by
  rw [conditionalTableMean, slice]
  fin_cases x <;> fin_cases y <;>
    norm_num [expect_eq_sum_div_card, product, F, B, kept, Fin.sum_univ_three]

private theorem estimated_mean (x y : Fin 3) :
    conditionalTableMean kept kept (product F' B') x y = if x = 0 ∧ y = 2 then 16 else 0 := by
  rw [conditionalTableMean, slice]
  fin_cases x <;> fin_cases y <;>
    norm_num [expect_eq_sum_div_card, product, F', B', Fin.sum_univ_three]

example : product F' B' 0 0 2 = 0 ∧ product F' B' 1 0 2 = 32 := by
  norm_num [product, F', B', Fin.sum_univ_three]

private theorem root_sixteen : (16 : ℝ) ^ (4⁻¹ : ℝ) = 2 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num]
  exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)

private theorem scaled_gap : |(3 / 2 : ℝ) ^ (4⁻¹ : ℝ) - 24 ^ (4⁻¹ : ℝ)| ^ 4 = 3 / 2 := by
  rw [show (24 : ℝ) = (3 / 2) * 16 by norm_num,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3 / 2) (by norm_num : (0 : ℝ) ≤ 16), root_sixteen]
  rw [show (3 / 2 : ℝ) ^ (4⁻¹ : ℝ) - (3 / 2 : ℝ) ^ (4⁻¹ : ℝ) * 2 =
    -((3 / 2 : ℝ) ^ (4⁻¹ : ℝ)) by ring]
  rw [abs_neg, abs_of_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) _)]
  exact Real.rpow_inv_natCast_pow (by norm_num) (by norm_num)

private theorem mean_error :
    rootDistPow 4 3 (2 / 3) kept kept
        (fun _ x y => (3 / 2) * conditionalTableMean kept kept (product F B) x y)
        (fun _ x y => (3 / 2) * conditionalTableMean kept kept (product F' B') x y) = 1 / 2 := by
  norm_num [rootDistPow, rowNormPow, true_mean, estimated_mean, kept, sum_filter,
    expect_eq_sum_div_card, Fin.sum_univ_three]
  rw [show (1 / 4 : ℝ) = 4⁻¹ by rw [one_div], scaled_gap]
  norm_num

private theorem coarse_bound :
    rootDistPow 4 3 (2 / 3) kept kept
        (fun _ x y => (3 / 2) * conditionalTableMean kept kept (product F B) x y)
        (fun _ x y => (3 / 2) * conditionalTableMean kept kept (product F' B') x y) ≤
      50331648 * (rootDistPow 4 3 (2 / 3) kept middle F F' +
        12 * rootDistPow 4 3 1 middle kept B B') := by
  have hrow : ∀ σ z, middle σ z → #{y ∈ ({y | kept σ y} : Finset (Fin 3)) | B σ z y ≠ 0} ≤ 1 := by
    intro σ z _
    refine card_le_one.2 fun y hy y' hy' => ?_
    have hy2 : y = 2 := by
      by_contra h
      simp [B, h] at hy
    have hy'2 : y' = 2 := by
      by_contra h
      simp [B, h] at hy'
    exact hy2.trans hy'2.symm
  have hcol : ∀ σ z, middle σ z → #{x ∈ ({x | kept σ x} : Finset (Fin 3)) | F' σ x z ≠ 0} ≤ 1 := by
    intro σ z _
    refine card_le_one.2 fun x hx x' hx' => ?_
    have hx0 : x = 0 := by
      by_contra h
      simp [F', h] at hx
    have hx'0 : x' = 0 := by
      by_contra h
      simp [F', h] at hx'
    exact hx0.trans hx'0.symm
  have h := rootDistPow_coarseProductMean_le (s := 4) (N := 3) (u := 2 / 3)
    (X := kept) (Y := kept) (Z := middle) (a := 2 / 3) (b := 1) (f := 1) (πf := 1)
    (F := F) (F' := F') (B := B) (B' := B') (by decide) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ _ _ => by unfold F; split_ifs <;> norm_num)
    (fun _ _ _ => by unfold F'; split_ifs <;> norm_num)
    (fun _ _ _ => by unfold B; split_ifs <;> norm_num)
    (fun _ _ _ => by unfold B'; split_ifs <;> norm_num)
    (CF := 8) (CB := 1) (by norm_num) (by norm_num)
    (fun _ _ _ => by unfold F'; split_ifs <;> norm_num)
    (fun _ _ _ => by unfold B; split_ifs <;> norm_num) hrow hcol
  norm_num [middle] at h
  exact h

-- The theorem applies to this positive error with actual, dependent conditioning masks.
example : (1 / 2 : ℝ) ≤ 50331648 * (rootDistPow 4 3 (2 / 3) kept middle F F' +
    12 * rootDistPow 4 3 1 middle kept B B') := by
  have h := coarse_bound
  rwa [mean_error] at h

/-! ### The actual true-atom mean -/

private abbrev full {α : Type*} (_ : α) (_ : Fin 2) : Prop := True
private abbrev used (σ : Bool) (_ : Fin 2) : Prop := σ = true
private def G (x z : Fin 2) : ℝ := if x = 0 ∧ z = 1 then 1 else 0
private def H (z y : Fin 2) : ℝ := if z = 1 ∧ y = 0 then 1 else 0

private noncomputable def trueAtomProduct (d : (Unit × Unit) × Bool) (x y : Fin 2) : ℝ :=
  ∑ z, correctionAtom (fun _ _ => 0) (fun _ => 1) 8 8 1 G full full full id (fun _ => 1)
    (fun _ => 1) (fun _ => 1) d.1 x z *
      denseAtom full used id (fun _ => 1) (fun _ => 1) 4 1 H d.2 z y

example : conditionalTableMean (fun (_ : (Unit × Unit) × Bool) => full ())
    (fun d => used d.2) trueAtomProduct 0 0 = 1 := by
  rw [conditionalTableMean_eq_expect_product (κ := Unit) (X := fun (_ : Unit) => full ())
    (Y := used) (H := trueAtomProduct)]
  have h := expect_correctionAtom_mul_denseAtom
    (I := fun _ _ => 0) (τ := fun _ => 1) (Q := id) (hF := fun _ => 1) (ρF := fun _ => 1)
    (k := id) (hB := fun _ => 1) (ρB := fun _ => 1) (KF := 8) (Kc := 8) (KB := 4)
    (f := 1) (b := 1) (πf := 1) (G := G) (H := H) (g₀ := fun _ => 1)
    (X := fun (_ : Unit) => full ()) (Z := fun (_ : Unit) => full ()) (Zt := fun _ => full ())
    (Y := fun (_ : Bool) => full ()) (Ya := used) (Yt := used) (x := 0) (y := 0)
    (hSx := ⟨(), by simp⟩) (hZπ := fun _ => by simp [full]) (hπf := by norm_num)
    (hYt := fun _ h => h) (hSy := ⟨true, by decide⟩)
    (hQh := fun _ _ => rfl) (hρF0 := fun _ => zero_le_one) (hρF1 := fun _ => le_rfl)
    (ηF := 1) (hηF := one_pos) (hρFη := fun _ _ => rfl)
    (hτ0 := fun _ => zero_le_one) (hτ1 := fun _ => le_rfl) (τ₀ := 0) (hτ₀ := le_rfl)
    (hττ := fun _ _ => rfl) (e := 0) (hI := fun _ _ _ => rfl)
    (hf := one_pos) (hG0 := fun w => by fin_cases w <;> norm_num [G])
    (MF := 1) (hGM := by norm_num [G, Fin.sum_univ_two]) (cF := 1) (hcF := zero_le_one)
    (hKF := by norm_num) (hpairZ := fun _ _ _ => by simp [full])
    (p := 1) (hp := zero_le_one) (hpairX := fun _ _ => by simp [full])
    (R := 1) (hR := fun z _ => by
      fin_cases z <;> norm_num [G, univ_fin2, filter_insert, filter_singleton])
    (hKc := by norm_num) (hkh := fun _ _ => rfl) (hρB0 := fun _ => zero_le_one)
    (hρB1 := fun _ => le_rfl) (ηB := 1) (hηB := one_pos) (hρBη := fun _ _ => rfl)
    (hb := one_pos) (hH0 := fun z w => by fin_cases z <;> fin_cases w <;> norm_num [H])
    (MB := 1) (hHM := fun z => by fin_cases z <;> norm_num [H, Fin.sum_univ_two])
    (cB := 1) (hcB := zero_le_one) (hKB := by norm_num)
    (hpairY := fun _ _ => by simp [used, full])
  norm_num [used, filter_eq', dens_eq_card_div_card, G, H, Fin.sum_univ_two] at h
  norm_num [trueAtomProduct, used, filter_eq', Fin.sum_univ_two]
  exact h

/-! ### Empty slices remain defined -/

example (T : Fin 3 → Fin 3 → Fin 3 → ℝ) (x y : Fin 3) :
    conditionalTableMean (fun _ _ => False) kept T x y = 0 := by
  simp [conditionalTableMean]

example (T : Empty → Fin 3 → Fin 3 → ℝ) (x y : Fin 3) :
    conditionalTableMean (fun _ _ => True) (fun _ _ => True) T x y = 0 := by
  simp [conditionalTableMean]

end ComplexityTests.ConditionalProductMean
