/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.VOLE.MulCheck
public import CslibFrontier.Probability.LinearCombination
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event

/-!
# Batching VOLE multiplication checks with public random weights

The sender fixes authenticated wire values and masks before a public random vector of weights is
sampled. It may then choose arbitrary randomized affine coefficients depending on those weights.
An independent hidden key is used for the final weighted multiplication check.

For a false vector of multiplication claims, the weighted residual vanishes with probability
`1 / |F|`. Otherwise the acceptance equation is a nonzero quadratic in the hidden key. This yields
the mixture bound `1 / |F| + (1 - 1 / |F|) * (2 / |F|)`.

## Main results

* `voleMulCheck_sum_sub_eq`: the weighted tag identity.
* `voleMulCheck_sum`: honest completeness for every batch and key.
* `toOuterMeasure_voleMulCheck_sum_le`: the two-root bound when the weighted residual is nonzero.
* `toOuterMeasure_voleMulCheck_batch_le`: the mixture bound for an adaptive randomized reply.
* `toOuterMeasure_voleMulCheck_batch_bind_le`: the bound for arbitrary randomized sender state.
* `toOuterMeasure_voleMulCheck_batch_bind_le_three_div`: the simpler `3 / |F|` bound.

This original ideal algebraic batching result uses a vector of independent weights, with one
field element per constraint, and two field elements in the reply. It is not the scalar-challenge
QuickSilver protocol, a zero-knowledge result or a certified efficient implementation.
-/

public section

namespace Cslib.Crypto.Protocols.VOLE

open Probability
open scoped BigOperators ENNReal

variable {ι F : Type} [Fintype ι]

/-- The weighted multiplication check has leading coefficient equal to the weighted residual. -/
theorem voleMulCheck_sum_sub_eq [CommRing F]
    (r x y z v_x v_y v_z : ι → F) (delta : F) :
    ∑ i, r i * ((x i * delta + v_x i) * (y i * delta + v_y i) -
      (z i * delta + v_z i) * delta) =
      (∑ i, r i * (x i * y i - z i)) * delta ^ 2 +
        (∑ i, r i * voleMulCrossTerm (x i) (v_x i) (y i) (v_y i) (v_z i)) * delta +
        ∑ i, r i * voleMulConstTerm (v_x i) (v_y i) := by
  simp_rw [voleMulCheck_sub_eq rfl rfl rfl]
  simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib, ← Finset.sum_mul]

/-- With nonzero weighted residual, arbitrary affine coefficients pass the weighted check for
an independent uniform key with probability at most `2 / |F|`. -/
theorem toOuterMeasure_voleMulCheck_sum_le [Field F] [Fintype F]
    (r x y z v_x v_y v_z : ι → F) (a b : F)
    (hne : ∑ i, r i * (x i * y i - z i) ≠ 0) :
    (PMF.uniformOfFintype F).toOuterMeasure
      {delta | ∑ i, r i * ((x i * delta + v_x i) * (y i * delta + v_y i) -
        (z i * delta + v_z i) * delta) = a * delta + b} ≤
      2 / (Fintype.card F : ℝ≥0∞) := by
  have hkey := toOuterMeasure_voleMulCheck_le
    (x := ∑ i, r i * (x i * y i - z i)) (y := 1) (z := 0) 0 0 0
    (a - ∑ i, r i * voleMulCrossTerm (x i) (v_x i) (y i) (v_y i) (v_z i))
    (b - ∑ i, r i * voleMulConstTerm (v_x i) (v_y i)) (by simpa using hne)
  refine (MeasureTheory.measure_mono ?_).trans hkey
  intro delta hdelta
  rw [Set.mem_ofPred_eq, voleMulCheck_sum_sub_eq] at hdelta
  change (_ * delta + 0) * (1 * delta + 0) - (0 * delta + 0) * delta = _
  linear_combination hdelta

/-- Honest affine coefficients accept every weighted batch of true multiplication constraints,
including the empty batch and every key. -/
theorem voleMulCheck_sum [CommRing F]
    (r x y z v_x v_y v_z : ι → F) (delta : F) (htrue : ∀ i, x i * y i = z i) :
    ∑ i, r i * ((x i * delta + v_x i) * (y i * delta + v_y i) -
      (z i * delta + v_z i) * delta) =
        (∑ i, r i * voleMulCrossTerm (x i) (v_x i) (y i) (v_y i) (v_z i)) * delta +
        ∑ i, r i * voleMulConstTerm (v_x i) (v_y i) := by
  rw [voleMulCheck_sum_sub_eq]
  simp [htrue]

variable [Field F] [Fintype F] [DecidableEq F] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem reply_key_le (r x y z v_x v_y v_z : ι → F) (reply : PMF (F × F))
    (hne : ∑ i, r i * (x i * y i - z i) ≠ 0) :
    (do
      let ab ← reply
      let delta ← PMF.uniformOfFintype F
      return decide (∑ i, r i * ((x i * delta + v_x i) * (y i * delta + v_y i) -
        (z i * delta + v_z i) * delta) = ab.1 * delta + ab.2)).toOuterMeasure {true} ≤
      2 / (Fintype.card F : ℝ≥0∞) := by
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.toOuterMeasure_bind_apply]
  refine PMF.tsum_mul_le_of_forall_le reply fun ab => ?_
  change ((PMF.uniformOfFintype F).map (fun delta => decide _)).toOuterMeasure {true} ≤ _
  rw [PMF.toOuterMeasure_map_apply]
  refine (MeasureTheory.measure_mono ?_).trans
    (toOuterMeasure_voleMulCheck_sum_le r x y z v_x v_y v_z ab.1 ab.2 hne)
  intro delta hdelta
  exact of_decide_eq_true hdelta

/-- A false batch with an arbitrary randomized affine reply depending on the public weight
vector passes with probability at most `1 / |F| + (1 - 1 / |F|) * (2 / |F|)`. Wire values and
masks are fixed before the weights; the receiver key is independent of the weights and reply. -/
theorem toOuterMeasure_voleMulCheck_batch_le
    (x y z v_x v_y v_z : ι → F) (reply : (ι → F) → PMF (F × F))
    (hfalse : ∃ i, x i * y i ≠ z i) :
    (do
      let r ← PMF.uniformOfFintype (ι → F)
      let ab ← reply r
      let delta ← PMF.uniformOfFintype F
      return decide (∑ i, r i * ((x i * delta + v_x i) * (y i * delta + v_y i) -
        (z i * delta + v_z i) * delta) = ab.1 * delta + ab.2)).toOuterMeasure {true} ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ +
        (1 - (Fintype.card F : ℝ≥0∞)⁻¹) * (2 / (Fintype.card F : ℝ≥0∞)) := by
  classical
  let cancel : Set (ι → F) := {r | ∑ i, r i * (x i * y i - z i) = 0}
  let kernel (r : ι → F) : PMF Bool := do
    let ab ← reply r
    let delta ← PMF.uniformOfFintype F
    return decide (∑ i, r i * ((x i * delta + v_x i) * (y i * delta + v_y i) -
      (z i * delta + v_z i) * delta) = ab.1 * delta + ab.2)
  obtain ⟨i, hi⟩ := hfalse
  have hcancel : (PMF.uniformOfFintype (ι → F)).toOuterMeasure cancel =
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
    simpa only [one_div] using toOuterMeasure_uniform_linearComb_eq_zero
      (d := fun j => x j * y j - z j) (i₀ := i) (sub_ne_zero.mpr hi)
  have hcompl := PMF.toOuterMeasure_compl_le_one_sub
    (PMF.uniformOfFintype (ι → F)) cancel hcancel.ge
  change ((PMF.uniformOfFintype (ι → F)).bind kernel).toOuterMeasure {true} ≤ _
  rw [PMF.toOuterMeasure_bind_apply]
  calc
    ∑' r, PMF.uniformOfFintype (ι → F) r * (kernel r).toOuterMeasure {true}
      ≤ ∑' r, PMF.uniformOfFintype (ι → F) r *
          (if r ∈ cancel then 1 else 2 / (Fintype.card F : ℝ≥0∞)) := by
        refine tsum_le_tsum fun r => mul_le_mul_of_nonneg_left ?_ zero_le
        split_ifs with hr
        · exact PMF.toOuterMeasure_le_one _ _
        · exact reply_key_le r x y z v_x v_y v_z (reply r) hr
    _ = (PMF.uniformOfFintype (ι → F)).toOuterMeasure cancel +
        (PMF.uniformOfFintype (ι → F)).toOuterMeasure cancelᶜ *
          (2 / (Fintype.card F : ℝ≥0∞)) := by
        simp only [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right, ← tsum_add]
        apply tsum_congr
        intro r
        by_cases hr : r ∈ cancel <;> simp [hr]
    _ ≤ _ := by
      rw [hcancel]
      gcongr

/-- An arbitrary randomized sender fixes all wire values and masks before the public weights.
Its randomized reply may depend on the entire sender state and those weights, but the hidden
key remains independent. The bad event contains a false constraint; for an empty index type it
is empty. There is no hypothesis on the sender's support or its probability of cheating. -/
theorem toOuterMeasure_voleMulCheck_batch_bind_le {S : Type} (sender : PMF S)
    (x y z v_x v_y v_z : S → ι → F) (reply : S → (ι → F) → PMF (F × F)) :
    (do
      let s ← sender
      let r ← PMF.uniformOfFintype (ι → F)
      let ab ← reply s r
      let delta ← PMF.uniformOfFintype F
      return decide ((∃ i, x s i * y s i ≠ z s i) ∧
        ∑ i, r i * ((x s i * delta + v_x s i) * (y s i * delta + v_y s i) -
          (z s i * delta + v_z s i) * delta) = ab.1 * delta + ab.2)).toOuterMeasure {true} ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ +
        (1 - (Fintype.card F : ℝ≥0∞)⁻¹) * (2 / (Fintype.card F : ℝ≥0∞)) := by
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.toOuterMeasure_bind_apply]
  refine PMF.tsum_mul_le_of_forall_le sender fun s => ?_
  by_cases hfalse : ∃ i, x s i * y s i ≠ z s i
  · simpa only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, hfalse, true_and] using
      toOuterMeasure_voleMulCheck_batch_le (x s) (y s) (z s) (v_x s) (v_y s) (v_z s)
        (reply s) hfalse
  · simp [hfalse]

/-- The simpler `3 / |F|` bound for the same randomized sender and adaptive affine reply. -/
theorem toOuterMeasure_voleMulCheck_batch_bind_le_three_div {S : Type} (sender : PMF S)
    (x y z v_x v_y v_z : S → ι → F) (reply : S → (ι → F) → PMF (F × F)) :
    (do
      let s ← sender
      let r ← PMF.uniformOfFintype (ι → F)
      let ab ← reply s r
      let delta ← PMF.uniformOfFintype F
      return decide ((∃ i, x s i * y s i ≠ z s i) ∧
        ∑ i, r i * ((x s i * delta + v_x s i) * (y s i * delta + v_y s i) -
          (z s i * delta + v_z s i) * delta) = ab.1 * delta + ab.2)).toOuterMeasure {true} ≤
      3 / (Fintype.card F : ℝ≥0∞) := by
  refine (toOuterMeasure_voleMulCheck_batch_bind_le sender x y z v_x v_y v_z reply).trans ?_
  calc
    (Fintype.card F : ℝ≥0∞)⁻¹ +
        (1 - (Fintype.card F : ℝ≥0∞)⁻¹) * (2 / (Fintype.card F : ℝ≥0∞))
      ≤ (Fintype.card F : ℝ≥0∞)⁻¹ + 1 * (2 / (Fintype.card F : ℝ≥0∞)) := by
        gcongr
        exact tsub_le_self
    _ = _ := by
      rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
      ring

end Cslib.Crypto.Protocols.VOLE
