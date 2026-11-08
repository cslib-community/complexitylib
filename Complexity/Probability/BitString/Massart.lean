/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.BitString.Sign
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Complexity.Probability.BitString.Rademacher
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Massart's finite-class lemma

For finitely many vectors `a j : κ → ℝ` (`j : ι`) of Euclidean norm at most `r`, the expected
maximum of the Rademacher sums `∑ i, a j i * signVal (σ i)` over a uniformly random sign vector
`σ : κ → Bool` is at most `r √(2 log |ι|)` [Massart2000, Lemma 5.2]
[MohriRostamizadehTalwalkar2018, Theorem 3.7].

The proof is the Chernoff argument for maxima. For `t > 0`, Jensen's inequality for `exp`, the
bound of a maximum of nonnegative terms by their sum, and the sub-Gaussian moment generating
function bound of Rademacher sums (`expect_exp_mul_sum_mul_signVal_le`) give
`exp (t 𝔼 max_j Y_j) ≤ |ι| exp (t² r² / 2)`, that is, `𝔼 max_j Y_j ≤ log |ι| / t + t r² / 2`.
Minimizing over `t` gives `r √(2 log |ι|)`.

## Main results

* `Cslib.BitString.expect_sum_mul_signVal_eq_zero`: a Rademacher sum has mean zero.
* `Cslib.BitString.expect_ciSup_sum_mul_signVal_le`: **Massart's lemma**.

## References

* [P. Massart, *Some applications of concentration inequalities to statistics*][Massart2000],
  Lemma 5.2
* [M. Mohri, A. Rostamizadeh, A. Talwalkar, *Foundations of Machine Learning*, 2nd
  ed.][MohriRostamizadehTalwalkar2018], Theorem 3.7
-/

public section

open Finset Real
open scoped BigOperators

namespace Cslib.BitString

/-- A Rademacher sum has mean zero: flipping every sign negates it. -/
theorem expect_sum_mul_signVal_eq_zero {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ → ℝ) :
    𝔼 σ : κ → Bool, ∑ i, a i * signVal (σ i) = 0 := by
  have h : 𝔼 σ : κ → Bool, ∑ i, a i * signVal (σ i) =
      -𝔼 σ : κ → Bool, ∑ i, a i * signVal (σ i) := by
    have hinv : Function.Involutive fun (σ : κ → Bool) i => !σ i :=
      fun σ => funext fun i => Bool.not_not _
    rw [← Finset.expect_neg_distrib]
    exact Fintype.expect_equiv (Function.Involutive.toPerm _ hinv) _ _ fun σ => by
      simp only [Function.Involutive.coe_toPerm, signVal_not, mul_neg, Finset.sum_neg_distrib,
        neg_neg]
  linarith

/-- Jensen's inequality for `exp` and a uniform average. -/
private theorem exp_expect_le {α : Type*} [Fintype α] [Nonempty α] (g : α → ℝ) :
    exp (𝔼 x, g x) ≤ 𝔼 x, exp (g x) := by
  have hcard : (0 : ℝ) < Fintype.card α := Nat.cast_pos.2 Fintype.card_pos
  have h := convexOn_exp.map_sum_le (t := Finset.univ) (w := fun _ => (Fintype.card α : ℝ)⁻¹)
    (p := g) (fun _ _ => by positivity) (by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard.ne'])
    fun _ _ => Set.mem_univ _
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, div_eq_inv_mul,
    div_eq_inv_mul, Finset.mul_sum, Finset.mul_sum]
  simpa only [smul_eq_mul] using h

/-- `exp (t max_j f j) ≤ ∑ j, exp (t f j)` for a finite nonempty family. -/
private theorem exp_mul_ciSup_le_sum {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) (t : ℝ) :
    exp (t * ⨆ j, f j) ≤ ∑ j, exp (t * f j) := by
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := f)
  rw [← hj]
  exact Finset.single_le_sum (f := fun j => exp (t * f j)) (fun _ _ => (exp_pos _).le)
    (Finset.mem_univ j)

/-- If `x ≤ c / t + t d` for every `t > 0`, then `x ≤ 2 √(c d)`: the optimization of a Chernoff
parameter. -/
private theorem le_two_mul_sqrt_of_forall_le {x c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : ∀ t : ℝ, 0 < t → x ≤ c / t + t * d) : x ≤ 2 * √(c * d) := by
  rcases hc.lt_or_eq with hc | rfl
  · rcases hd.lt_or_eq with hd | rfl
    · have hsc := Real.sqrt_pos.2 hc
      have hsd := Real.sqrt_pos.2 hd
      calc x ≤ c / (√c / √d) + √c / √d * d := h (√c / √d) (div_pos hsc hsd)
        _ = 2 * √(c * d) := by
          rw [Real.sqrt_mul hc.le]
          field_simp
          rw [Real.sq_sqrt hc.le, Real.sq_sqrt hd.le]
          ring
    · by_contra hx
      push Not at hx
      rw [mul_zero, Real.sqrt_zero, mul_zero] at hx
      have := h ((c + 1) / x) (by positivity)
      rw [mul_zero, add_zero, div_div_eq_mul_div] at this
      have : x * (c + 1) ≤ c * x := by
        rwa [le_div_iff₀ (by positivity)] at this
      nlinarith
  · by_contra hx
    push Not at hx
    rw [zero_mul, Real.sqrt_zero, mul_zero] at hx
    have := h (x / (2 * d + 1)) (by positivity)
    rw [zero_div, zero_add] at this
    have h1 : x / (2 * d + 1) * d < x := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith

/-- **Massart's lemma** [Massart2000, Lemma 5.2] [MohriRostamizadehTalwalkar2018, Theorem 3.7]:
if the vectors `a j : κ → ℝ`, `j : ι`, have Euclidean norm at most `r`, then the expected maximum
of their correlations with a uniformly random sign vector is at most `r √(2 log |ι|)`.

For empty `ι` the maximum is `0` by the convention `⨆ j ∈ ∅ = 0` for real numbers, and so is the
bound. -/
theorem expect_ciSup_sum_mul_signVal_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (a : ι → κ → ℝ) {r : ℝ} (hr : 0 ≤ r) (ha : ∀ j, ∑ i, a j i ^ 2 ≤ r ^ 2) :
    𝔼 σ : κ → Bool, ⨆ j, ∑ i, a j i * signVal (σ i) ≤
      r * √(2 * Real.log (Fintype.card ι)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have key (t : ℝ) (ht : 0 < t) :
      𝔼 σ : κ → Bool, ⨆ j, ∑ i, a j i * signVal (σ i) ≤
        Real.log (Fintype.card ι) / t + t * (r ^ 2 / 2) := by
    have hexp : exp (t * 𝔼 σ : κ → Bool, ⨆ j, ∑ i, a j i * signVal (σ i)) ≤
        Fintype.card ι * exp (t ^ 2 * r ^ 2 / 2) := by
      rw [Finset.mul_expect]
      calc exp (𝔼 σ : κ → Bool, t * ⨆ j, ∑ i, a j i * signVal (σ i))
          ≤ 𝔼 σ : κ → Bool, exp (t * ⨆ j, ∑ i, a j i * signVal (σ i)) := exp_expect_le _
        _ ≤ 𝔼 σ : κ → Bool, ∑ j, exp (t * ∑ i, a j i * signVal (σ i)) :=
            Finset.expect_le_expect fun σ _ =>
              exp_mul_ciSup_le_sum (fun j => ∑ i, a j i * signVal (σ i)) t
        _ = ∑ j, 𝔼 σ : κ → Bool, exp (t * ∑ i, a j i * signVal (σ i)) := by
            rw [Finset.expect_sum_comm]
        _ ≤ ∑ _j : ι, exp (t ^ 2 * r ^ 2 / 2) := by
            refine Finset.sum_le_sum fun j _ => ?_
            refine (expect_exp_mul_sum_mul_signVal_le (a j) t).trans ?_
            gcongr
            exact ha j
        _ = Fintype.card ι * exp (t ^ 2 * r ^ 2 / 2) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hlog := Real.log_le_log (exp_pos _) hexp
    rw [Real.log_exp, Real.log_mul hN.ne' (exp_pos _).ne', Real.log_exp] at hlog
    rw [div_add' _ _ _ ht.ne', le_div_iff₀ ht]
    nlinarith
  have hlogN : 0 ≤ Real.log (Fintype.card ι) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  calc 𝔼 σ : κ → Bool, ⨆ j, ∑ i, a j i * signVal (σ i)
      ≤ 2 * √(Real.log (Fintype.card ι) * (r ^ 2 / 2)) :=
        le_two_mul_sqrt_of_forall_le hlogN (by positivity) key
    _ = r * √(2 * Real.log (Fintype.card ι)) := by
      rw [show Real.log (Fintype.card ι) * (r ^ 2 / 2) =
          r ^ 2 * (2 * Real.log (Fintype.card ι)) / 2 ^ 2 by ring, Real.sqrt_div' _ (by norm_num),
        Real.sqrt_mul' _ (by positivity), Real.sqrt_sq hr, Real.sqrt_sq (by norm_num)]
      ring

end Cslib.BitString
