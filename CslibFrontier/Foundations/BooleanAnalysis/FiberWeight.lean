/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Influence
import CslibFrontier.Foundations.BooleanAnalysis.Monotone
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith

/-!
# Degree-one weight of the fibers of a map from the cube

A map `f : (ι → Bool) → Γ` to a finite alphabet splits the cube into the fibers `f⁻¹(σ)`. The
indicator of a fiber of density `μ` has variance `μ - μ²`, which bounds its degree-one weight
(`BitString.sum_fourierCoeff_singleton_sq_le`). By the Cauchy–Schwarz inequality, over `ι` and
then over the alphabet, the degree-one coefficients of all the fiber indicators have total absolute
value at most `√(|ι| (|Γ| - 1))` (`BitString.sq_sum_sum_abs_fourierCoeff_fiber_le`), since the
densities sum to one and so their squares sum to at least `1 / |Γ|`. For a Boolean `f` this is the
bound `√|ι|` on the degree-one coefficients of `f` read as signs, and in general it bounds how much
a single symbol `f x` can reveal about the bits of a uniformly random `x`.

## Main results

* `Cslib.BitString.expect_boole_sub_sq`: the variance of the indicator of a set of density `μ` is
  `μ - μ²`.
* `Cslib.BitString.sq_sum_sum_abs_fourierCoeff_fiber_le`: the degree-one coefficients of the fiber
  indicators of `f` have total absolute value at most `√(|ι| (|Γ| - 1))`.
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.BitString

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι]

/-- The indicator of a set of density `μ` has variance `μ - μ²`. -/
theorem expect_boole_sub_sq (p : (ι → Bool) → Prop) [DecidablePred p] :
    𝔼 x, ((if p x then 1 else 0 : ℝ) - 𝔼 y, (if p y then 1 else 0 : ℝ)) ^ 2 =
      𝔼 y, (if p y then 1 else 0 : ℝ) - (𝔼 y, (if p y then 1 else 0 : ℝ)) ^ 2 := by
  set μ := 𝔼 y, (if p y then 1 else 0 : ℝ)
  have h (x : ι → Bool) : ((if p x then 1 else 0 : ℝ) - μ) ^ 2 =
      (if p x then 1 else 0 : ℝ) * (1 - 2 * μ) + μ ^ 2 := by
    split_ifs <;> ring
  simp only [h]
  rw [Finset.expect_add_distrib, ← Finset.expect_mul, Fintype.expect_const]
  ring

/-- **The fibers of a map from the cube have little degree-one weight**: the degree-one coefficients
of the indicators of the fibers of `f : (ι → Bool) → Γ` have total absolute value at most
`√(|ι| (|Γ| - 1))`. -/
theorem sq_sum_sum_abs_fourierCoeff_fiber_le [Fintype Γ] [DecidableEq Γ]
    (f : (ι → Bool) → Γ) :
    (∑ σ, ∑ i, |fourierCoeff (fun x => if f x = σ then 1 else 0) {i}|) ^ 2 ≤
      Fintype.card ι * (Fintype.card Γ - 1) := by
  set μ : Γ → ℝ := fun σ => 𝔼 y, (if f y = σ then 1 else 0 : ℝ)
  have hinner (σ : Γ) : (∑ i, |fourierCoeff (fun x => if f x = σ then 1 else 0) {i}|) ^ 2 ≤
      Fintype.card ι * (μ σ - μ σ ^ 2) := by
    refine (sq_sum_le_card_mul_sum_sq (s := univ)).trans ?_
    rw [card_univ]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    simp only [sq_abs]
    refine (sum_fourierCoeff_singleton_sq_le _).trans_eq ?_
    exact expect_boole_sub_sq fun x => f x = σ
  have hμ : ∑ σ, μ σ = 1 := by
    rw [← Finset.expect_sum_comm]
    simp only [Fintype.sum_ite_eq, Fintype.expect_const]
  have hμsq : 1 ≤ Fintype.card Γ * ∑ σ, μ σ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := univ) (f := μ)
    rw [card_univ, hμ, one_pow] at h
    exact h
  calc (∑ σ, ∑ i, |fourierCoeff (fun x => if f x = σ then 1 else 0) {i}|) ^ 2
      ≤ Fintype.card Γ * ∑ σ, (∑ i, |fourierCoeff (fun x => if f x = σ then 1 else 0) {i}|) ^ 2 :=
        by simpa only [card_univ] using sq_sum_le_card_mul_sum_sq (s := univ)
    _ ≤ Fintype.card Γ * ∑ σ, Fintype.card ι * (μ σ - μ σ ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun σ _ => hinner σ) (Nat.cast_nonneg _)
    _ = Fintype.card ι * (Fintype.card Γ * (∑ σ, μ σ) - Fintype.card Γ * ∑ σ, μ σ ^ 2) := by
        rw [← mul_sum, sum_sub_distrib]
        ring
    _ ≤ Fintype.card ι * (Fintype.card Γ - 1) := by
        rw [hμ, mul_one]
        exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)

end Cslib.BitString
