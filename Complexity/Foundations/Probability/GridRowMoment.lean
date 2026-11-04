/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import Complexity.Foundations.Probability.NormalizedAtomRows.MeanTail
public import Complexity.Foundations.Probability.RootMetric.Slices

/-!
# Finite row moments on rounded grid channels

Exact source marginals and a pointwise bound pay a width-dependent fourth row moment.
The proof adapts Samuel Schlesinger's row norm API, keeping the horizon and width explicit.
-/
public section
noncomputable section
open Finset Cslib Cslib.Probability
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]
/-- Exact grid frame mass; all prime and rounding dependence is visible. -/
@[expose] def gridMass (P k : ℕ) : ℝ := ((side P k : ℝ) / P) ^ 4

namespace NormalizedMoments
/-- Exact source payment, including nonempty copy suffixes and D=0: a single frame
marginal is uniform at every padded identifier; injectivity is not needed for one point. -/
lemma source_density_sum (D : ZMod P) (s : Fin J) (ks : ℕ) (ss : List (ZMod P)) :
    (∑ x : ZMod P, (({σ : Environment P J | retainedMask s (side P ks) D ss σ x} :
      Finset _).dens : ℝ)) = (P : ℝ) * ((side P ks : ℝ) / P) ^ 4 := by
  have hd (x : ZMod P) :
      (({σ : Environment P J | retainedMask s (side P ks) D ss σ x} : Finset _).dens : ℝ) =
        ((side P ks : ℝ) / P) ^ 4 := by
    simp only [retainedMask]
    convert density s (side P ks) (side_le P ks) (CopyPadding.identifier D ss x) using 1
    congr 2
    ext σ
    simp
  simp_rw [hd]
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]

end NormalizedMoments
open NormalizedMoments

/-- A bounded vertex array pays only its source marginal, uniformly in field width. -/
lemma grid_vertex_moment_le (D : ZMod P) (s : Fin J) (ks : ℕ) (ss : List (ZMod P))
    (H : Horizon P) (hks : ks ≤ H.maxExponent)
    (F : Environment P J → ZMod P → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ σ x, |F σ x| ≤ B) :
    vertexNormPow 4 P (rate ks) (retainedMask s (side P ks) D ss) F ≤ 16 * B ^ 4 := by
  have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hr := rate_pos ks
  have hd := (affineRetains_rates (P := P) (H := 4) (horizon_admissible H hks)
    (show ((2 : ℝ) ^ ks)⁻¹ ≤ 1 from inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))).2.2.1
  rw [← side_eq_ceil] at hd
  norm_num only [show (2 : ℝ) ^ 4 = 16 by norm_num] at hd
  change gridMass P ks ≤ 16 * rate ks at hd
  have hv : vertexNormPow 4 P (rate ks) (retainedMask s (side P ks) D ss)
      (fun _ _ => 1) ≤ 16 := by
    rw [vertexNormPow_one_eq_sum_dens, NormalizedMoments.source_density_sum]
    change (↑P * rate ks)⁻¹ * (↑P * gridMass P ks) ≤ 16
    calc
      _ ≤ (↑P * rate ks)⁻¹ * (↑P * (16 * rate ks)) := by gcongr
      _ = 16 := by field_simp [hP.ne', hr.ne']
  have hb : vertexNormPow 4 P (rate ks) (retainedMask s (side P ks) D ss) F ≤
      vertexNormPow 4 P (rate ks) (retainedMask s (side P ks) D ss) (fun _ _ => B) := by
    unfold vertexNormPow
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (mul_pos hP hr).le)
    apply expect_le_expect
    intro σ _
    exact sum_le_sum fun x _ => by
      rw [abs_of_nonneg hB]
      exact pow_le_pow_left₀ (abs_nonneg _) (hF σ x) 4
  apply hb.trans
  have he : vertexNormPow 4 P (rate ks) (retainedMask s (side P ks) D ss)
      (fun _ _ => B) = B ^ 4 * vertexNormPow 4 P (rate ks)
        (retainedMask s (side P ks) D ss) (fun _ _ => 1) := by
    simp only [vertexNormPow, abs_of_nonneg hB, abs_one, one_pow, sum_const,
      nsmul_eq_mul, mul_one]
    simp_rw [mul_comm _ (B ^ 4), ← mul_expect]
    ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hv (pow_nonneg hB 4)]

/-- A bounded row pays at most the full width times its source density. The bound applies
before any walk, with arbitrary dependence of the row on its source mask. -/
lemma grid_row_moment_le (D : ZMod P) (s : Fin J) (ks : ℕ) (ss : List (ZMod P))
    (H : Horizon P) (hks : ks ≤ H.maxExponent)
    (Y : Environment P J → ZMod P → Prop) [∀ σ y, Decidable (Y σ y)]
    (F : Environment P J → ZMod P → ZMod P → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ σ x y, |F σ x y| ≤ B) :
    rowNormPow 4 P (rate ks) (retainedMask s (side P ks) D ss) Y F ≤ 16 * P * B ^ 4 := by
  have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hr := rate_pos ks
  have hv := grid_vertex_moment_le D s ks ss H hks (fun _ _ => 1)
    (by norm_num : (0 : ℝ) ≤ 1) (fun _ _ => by norm_num)
  norm_num only [one_pow, mul_one] at hv
  have hb := rowNormPow_le_of_card_le (X := retainedMask s (side P ks) D ss)
    (Y := Y) (Z := F) (by decide : 4 ≠ 0) (mul_pos hP hr).le hB hF
    (K := P) (fun σ x _ => (card_le_card (subset_univ _)).trans_eq (by simp))
  have hm := mul_le_mul_of_nonneg_left hv
    (mul_nonneg (Nat.cast_nonneg P) (pow_nonneg hB 4))
  exact hb.trans (by nlinarith only [hm])

end Matrix.HierarchyParams.H4RankEnvironment
