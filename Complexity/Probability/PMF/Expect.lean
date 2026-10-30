/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import Complexity.Init
public import Complexity.Probability.PMF
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Data.Finset.Density
public import Mathlib.Basic.Real.Basic
import Complexity.Foundations.Data.Finset.Expect
import Complexity.Probability.PMF.Map

/-!
# Uniform experiments as averages

An experiment that starts by drawing `a` uniformly from a finite type and then runs `f a` outputs
`b` with probability the average over `a` of the probability that `f a` outputs `b`
(`toReal_uniformOfFintype_bind_apply`). In particular, a Boolean function `g` of a uniform sample
is `true` with probability the density of the set where `g` is `true`
(`toReal_uniformOfFintype_map_apply_true`). These translate experiments written with `PMF.bind`
into the vocabulary of `Finset.expect` (`𝔼`) and `Finset.dens`.

## Main results

* `Cslib.Probability.PMF.sum_le_affine`: average pointwise affine bounds.
* `Cslib.Probability.PMF.sum_map_mul`, `.sum_bind_mul`: average deterministic and random scores.
* `Cslib.Probability.PMF.tsum_map_mul`, `.tsum_bind_mul`: the same laws for extended
  nonnegative scores over arbitrary types.

* `Cslib.Probability.PMF.toReal_uniformOfFintype_bind_apply`: a uniform first stage averages the
  second stages.
* `Cslib.Probability.PMF.toReal_uniformOfFintype_map_apply`: output probabilities are densities.
* `Cslib.Probability.PMF.toReal_uniformOfFintype_map_apply_true`: the probability that a Boolean
  function of a uniform sample is `true` is a density.
-/

@[expose] public section

namespace Cslib.Probability.PMF

open Finset
open scoped BigOperators ENNReal

/-- Expectation of `k : β → ℝ≥0∞` under `p.map g` equals expectation of `k ∘ g` under `p`. -/
theorem tsum_map_mul {α β : Type*} (p : PMF α) (g : α → β) (k : β → ℝ≥0∞) :
    (∑' b, p.map g b * k b) = ∑' a, p a * k (g a) := by
  simp only [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [tsum_comm]
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single (g a)]
  · simp
  · intro b hb
    simp [hb]

/-- Expectation of `k : β → ℝ≥0∞` under `p.bind f` decomposes as an iterated expectation. -/
theorem tsum_bind_mul {α β : Type*} (p : PMF α) (f : α → PMF β) (k : β → ℝ≥0∞) :
    (∑' b, (p.bind f) b * k b) = ∑' a, p a * ∑' b, f a b * k b := by
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact tsum_comm

/-- Averaging a score after a deterministic map averages its composite with that map.
Adapted from the cslib `crypto` branch at `5ff69ca`. -/
theorem sum_map_mul {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : α → β) (score : β → ℝ) :
    ∑ b, ((p.map f) b).toReal * score b = ∑ a, (p a).toReal * score (f a) := by
  classical
  simp only [map_apply_toReal, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul]

/-- Averaging a score after a random choice averages its conditional scores.
Adapted from the cslib `crypto` branch at `5ff69ca`. -/
theorem sum_bind_mul {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (kernel : α → PMF β) (score : β → ℝ) :
    ∑ b, (p.bind kernel b).toReal * score b =
      ∑ a, (p a).toReal * ∑ b, (kernel a b).toReal * score b := by
  simp only [bind_apply_toReal, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- The expectation of an affine score is the affine function of its expectation.
Adapted from the cslib `crypto` branch at `5ff69ca`. -/
theorem sum_affine {α : Type*} [Fintype α] (p : PMF α) (a b : ℝ) (score : α → ℝ) :
    (∑ x, (p x).toReal * (a + b * score x)) =
      a + b * ∑ x, (p x).toReal * score x := by
  simp only [mul_add, mul_left_comm _ b, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_toReal, one_mul, ← Finset.mul_sum]

/-- Pointwise affine bounds survive averaging over a finite distribution. -/
theorem sum_le_affine {α : Type*} [Fintype α] (p : PMF α) {a b : ℝ} {score bound : α → ℝ}
    (h : ∀ x, score x ≤ a + b * bound x) :
    (∑ x, (p x).toReal * score x) ≤ a + b * ∑ x, (p x).toReal * bound x :=
  (sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) ENNReal.toReal_nonneg).trans_eq
    (sum_affine p a b bound)

/-- A uniform upper bound on a score also bounds its expectation. -/
theorem sum_mul_le {α : Type*} [Fintype α] (p : PMF α) (score : α → ℝ) (bound : ℝ)
    (hscore : ∀ a, score a ≤ bound) : ∑ a, (p a).toReal * score a ≤ bound :=
  (Finset.sum_le_sum fun a _ =>
    mul_le_mul_of_nonneg_left (hscore a) ENNReal.toReal_nonneg).trans_eq
    (by rw [← Finset.sum_mul, sum_toReal, one_mul])

variable {α β : Type*} [Fintype α] [Nonempty α]

/-- An experiment whose first stage draws `a` uniformly outputs `b` with probability the average
over `a` of the probability that the second stage `f a` outputs `b`. -/
theorem toReal_uniformOfFintype_bind_apply (f : α → PMF β) (b : β) :
    ((uniformOfFintype α).bind f b).toReal = 𝔼 a, (f a b).toReal := by
  simp only [bind_apply_toReal, uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, inv_mul_eq_div, Fintype.expect_eq_sum_div_card, sum_div]

/-- The mass of an output of a uniform sample is the density of its fiber. -/
theorem toReal_uniformOfFintype_map_apply [DecidableEq β] (f : α → β) (b : β) :
    ((uniformOfFintype α).map f b).toReal = dens {a | f a = b} := by
  rw [← PMF.bind_pure_comp, toReal_uniformOfFintype_bind_apply]
  have h (a : α) : ((Function.comp PMF.pure f a) b).toReal =
      if f a = b then 1 else 0 := by
    simp only [Function.comp_apply, PMF.pure_apply, eq_comm (a := b)]
    split_ifs <;> rfl
  simp only [h]
  exact Fintype.expect_boole _

/-- A Boolean function `g` of a uniform sample is `true` with probability the density of the set
where `g` is `true`. -/
theorem toReal_uniformOfFintype_map_apply_true (g : α → Bool) :
    ((uniformOfFintype α).map g true).toReal = dens {a | g a = true} :=
  toReal_uniformOfFintype_map_apply g true

end Cslib.Probability.PMF
