/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hoeffding's inequality for the biased binomial distribution

For a Bernoulli trial with parameter `p ∈ [0, 1]`, the centered moment generating function
`(1 - p) exp (-s p) + p exp (s (1 - p))` is bounded above by `exp (s² / 8)` for every `s : ℝ`
(`Cslib.one_sub_mul_exp_add_mul_exp_le`). Raising this bound to the `Q`-th power via the binomial
theorem (`Cslib.sum_choose_mul_pow_mul_exp`) and optimizing the Chernoff parameter at `s = 4 t / Q`
gives one-sided (`Cslib.sum_filter_le_sub_choose_mul_pow_le`,
`Cslib.sum_filter_le_mul_sub_choose_mul_pow_le`) and two-sided
(`Cslib.sum_filter_le_abs_sub_choose_mul_pow_le`) Hoeffding tail bounds for `Bin(Q, p)`, together
with the interval-complement form (`Cslib.sum_filter_notMem_choose_mul_pow_le`) used in Lemma 4.8 of
`[OpenAI2026ETH]` at `p = (r - 1) / (2 r)`. All tail inequalities hold for every `Q : ℕ`, including
`Q = 0`.

For the unbiased case `p = 1 / 2` in counting form on `ι → Bool`, see
`Cslib.BitString.card_filter_le_abs_card_filter_sub_half_le`.

## Main results

* `Cslib.one_sub_mul_exp_add_mul_exp_le`: Hoeffding's lemma for a biased Bernoulli trial.
* `Cslib.sum_choose_mul_pow_eq_one`: binomial probability weights sum to `1`.
* `Cslib.sum_choose_mul_pow_mul_exp`: centered moment generating function of `Bin(Q, p)`.
* `Cslib.sum_filter_le_sub_choose_mul_pow_le`: upper-tail Hoeffding bound for `Bin(Q, p)`.
* `Cslib.sum_filter_le_mul_sub_choose_mul_pow_le`: lower-tail Hoeffding bound for `Bin(Q, p)`.
* `Cslib.sum_filter_le_abs_sub_choose_mul_pow_le`: two-sided Hoeffding bound for `Bin(Q, p)`.
* `Cslib.sum_filter_notMem_choose_mul_pow_le`: tail bound outside a subset covering
  `[Q p - t, Q p + t]`.

## References

* [W. Hoeffding, *Probability Inequalities for Sums of Bounded Random Variables*][Hoeffding1963]
* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Section 4.7, Lemma 4.8,
  pp. 34–35.
-/

@[expose] public section

namespace Cslib

open Finset Real

/-- Auxiliary nonnegativity case `0 ≤ s` of Hoeffding's Bernoulli moment generating function
bound, proved by showing `u ↦ log (1 - p + p exp u) - p u - u² / 8` has nonpositive second
derivative and vanishes to first order at `0`. -/
private theorem one_sub_mul_exp_add_mul_exp_le_of_nonneg {p s : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hs : 0 ≤ s) :
    (1 - p) * exp (-s * p) + p * exp (s * (1 - p)) ≤ exp (s ^ 2 / 8) := by
  rcases eq_or_lt_of_le hp₀ with rfl | hp₀'
  · simp only [sub_zero, one_mul, mul_zero, exp_zero, zero_mul, add_zero]
    exact one_le_exp (by positivity)
  rcases eq_or_lt_of_le hp₁ with rfl | hp₁'
  · simp only [sub_self, zero_mul, mul_zero, one_mul, zero_add, exp_zero]
    exact one_le_exp (by positivity)
  have h1p : 0 < 1 - p := sub_pos.mpr hp₁'
  let g : ℝ → ℝ := fun u => 1 - p + p * exp u
  have hg_pos : ∀ u, 0 < g u := fun u => by dsimp only [g]; positivity
  let φ : ℝ → ℝ := fun u => log (g u) - p * u - u ^ 2 / 8
  let φ' : ℝ → ℝ := fun u => p * exp u / g u - p - u / 4
  have hg_deriv : ∀ u, HasDerivAt g (p * exp u) u := fun u => by
    simpa only [zero_add] using ((hasDerivAt_exp u).const_mul p).const_add (1 - p)
  have hφ_deriv : ∀ u, HasDerivAt φ (φ' u) u := fun u => by
    have hlog : HasDerivAt (fun x : ℝ => log (g x)) (p * exp u / g u) u :=
      (hg_deriv u).log (hg_pos u).ne'
    have hlin : HasDerivAt (fun x : ℝ => p * x) p u := by
      simpa only [mul_one] using (hasDerivAt_id' u).const_mul p
    have hquad : HasDerivAt (fun x : ℝ => x ^ 2 / 8) (u / 4) u := by
      convert (hasDerivAt_pow 2 u).div_const (8 : ℝ) using 1
      ring
    exact (hlog.sub hlin).sub hquad
  have hφ'_deriv : ∀ u, HasDerivAt φ'
      ((p * exp u * g u - p * exp u * (p * exp u)) / g u ^ 2 - 1 / 4) u := fun u => by
    have hquot : HasDerivAt (fun x : ℝ => p * exp x / g x)
        ((p * exp u * g u - p * exp u * (p * exp u)) / g u ^ 2) u :=
      ((hasDerivAt_exp u).const_mul p).div (hg_deriv u) (hg_pos u).ne'
    have hlin : HasDerivAt (fun x : ℝ => x / 4) (1 / 4) u :=
      (hasDerivAt_id' u).div_const (4 : ℝ)
    exact (hquot.sub_const p).sub hlin
  have hφ''_nonpos : ∀ u, deriv φ' u ≤ 0 := fun u => by
    rw [(hφ'_deriv u).deriv]
    have hgu : g u ≠ 0 := (hg_pos u).ne'
    have heq : (p * exp u * g u - p * exp u * (p * exp u)) / g u ^ 2 - 1 / 4 =
        -((1 - p - p * exp u) ^ 2 / (4 * g u ^ 2)) := by
      dsimp only [g] at hgu ⊢
      field_simp
      ring
    rw [heq]
    exact neg_nonpos.mpr (by positivity)
  have hφ'_diff : Differentiable ℝ φ' := fun u => (hφ'_deriv u).differentiableAt
  have hφ'_anti : Antitone φ' := antitone_of_deriv_nonpos hφ'_diff hφ''_nonpos
  have hφ'_zero : φ' 0 = 0 := by
    simp only [φ', g, exp_zero, mul_one, sub_add_cancel]
    ring
  have hφ_diff : Differentiable ℝ φ := fun u => (hφ_deriv u).differentiableAt
  have hφ_anti : AntitoneOn φ (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hφ_diff.continuous.continuousOn
      hφ_diff.differentiableOn fun u hu => ?_
    rw [(hφ_deriv u).deriv, ← hφ'_zero]
    exact hφ'_anti (interior_subset hu)
  have hφ_le : φ s ≤ φ 0 := hφ_anti (le_rfl : (0 : ℝ) ≤ 0) hs hs
  have hφ_zero : φ 0 = 0 := by
    simp only [φ, g, exp_zero, mul_one, sub_add_cancel, log_one, mul_zero, sub_self, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
  rw [hφ_zero] at hφ_le
  have hlog_le : log (g s) ≤ p * s + s ^ 2 / 8 := by
    dsimp only [φ] at hφ_le
    linarith
  have hexp_le : g s ≤ exp (p * s + s ^ 2 / 8) := by
    rw [← exp_log (hg_pos s)]
    exact exp_le_exp.mpr hlog_le
  calc (1 - p) * exp (-s * p) + p * exp (s * (1 - p))
      = exp (-s * p) * g s := by
          dsimp only [g]
          have hs' : s * (1 - p) = -s * p + s := by ring
          rw [hs', exp_add]
          ring
    _ ≤ exp (-s * p) * exp (p * s + s ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left hexp_le (exp_pos _).le
    _ = exp (s ^ 2 / 8) := by
          rw [← exp_add]
          congr 1
          ring

/-- **Hoeffding's lemma for a biased Bernoulli trial** `[Hoeffding1963]`: for `p ∈ [0, 1]` and
`s : ℝ`, the centered moment generating function `(1 - p) exp (-s p) + p exp (s (1 - p))` is at
most `exp (s² / 8)`. -/
theorem one_sub_mul_exp_add_mul_exp_le {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (s : ℝ) :
    (1 - p) * exp (-s * p) + p * exp (s * (1 - p)) ≤ exp (s ^ 2 / 8) := by
  rcases le_or_gt 0 s with hs | hs
  · exact one_sub_mul_exp_add_mul_exp_le_of_nonneg hp₀ hp₁ hs
  · have hsym := one_sub_mul_exp_add_mul_exp_le_of_nonneg (p := 1 - p) (s := -s)
      (sub_nonneg.mpr hp₁) (by linarith) (by linarith)
    refine (le_of_eq ?_).trans (hsym.trans_eq (by congr 1; ring))
    have h1 : - -s * (1 - p) = s * (1 - p) := by ring
    have h2 : -s * (1 - (1 - p)) = -s * p := by ring
    rw [h1, h2]
    ring

/-- The binomial weights `C(Q, k) p^k (1 - p)^(Q - k)` sum to `1`. -/
theorem sum_choose_mul_pow_eq_one (Q : ℕ) (p : ℝ) :
    ∑ k ∈ range (Q + 1), (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) = 1 := by
  calc ∑ k ∈ range (Q + 1), (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k)
      = ∑ k ∈ range (Q + 1), p ^ k * (1 - p) ^ (Q - k) * (Q.choose k : ℝ) :=
          sum_congr rfl fun _ _ => by ring
    _ = (p + (1 - p)) ^ Q := (add_pow p (1 - p) Q).symm
    _ = 1 := by simp only [add_sub_cancel, one_pow]

/-- **The centered binomial moment generating function**: summing
`C(Q, k) p^k (1 - p)^(Q - k) exp (s (k - Q p))` over `0 ≤ k ≤ Q` factors as the `Q`-th power of
the single-trial moment generating function. -/
theorem sum_choose_mul_pow_mul_exp (Q : ℕ) (p s : ℝ) :
    ∑ k ∈ range (Q + 1),
      (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) * exp (s * ((k : ℝ) - Q * p)) =
    ((1 - p) * exp (-s * p) + p * exp (s * (1 - p))) ^ Q := by
  rw [add_comm ((1 - p) * exp (-s * p)), add_pow]
  refine sum_congr rfl fun k hk => ?_
  have hkQ : k ≤ Q := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [mul_pow, mul_pow, ← exp_nat_mul, ← exp_nat_mul]
  calc (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) * exp (s * ((k : ℝ) - Q * p))
      = p ^ k * (1 - p) ^ (Q - k) * (Q.choose k : ℝ) *
          (exp (↑k * (s * (1 - p))) * exp (↑(Q - k) * (-s * p))) := by
        rw [← exp_add, Nat.cast_sub hkQ]
        have hexp : s * ((k : ℝ) - Q * p) =
            (k : ℝ) * (s * (1 - p)) + ((Q : ℝ) - k) * (-s * p) := by ring
        rw [hexp]
        ring
    _ = p ^ k * exp (↑k * (s * (1 - p))) *
          ((1 - p) ^ (Q - k) * exp (↑(Q - k) * (-s * p))) * (Q.choose k : ℝ) := by ring

/-- Every binomial probability weight `C(Q, k) p^k (1 - p)^(Q - k)` is nonnegative for
`p ∈ [0, 1]`. -/
private theorem choose_mul_pow_nonneg (Q k : ℕ) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) := by
  have h1p : 0 ≤ 1 - p := sub_nonneg.mpr hp₁
  positivity

/-- Sub-sums of binomial weights over `range (Q + 1)` are at most `1`. -/
private theorem sum_filter_choose_mul_pow_le_one (Q : ℕ) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (P : ℕ → Prop) [DecidablePred P] :
    ∑ k ∈ range (Q + 1) with P k, (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) ≤ 1 :=
  (sum_le_sum_of_subset_of_nonneg (filter_subset P (range (Q + 1)))
    fun k _ _ => choose_mul_pow_nonneg Q k hp₀ hp₁).trans_eq (sum_choose_mul_pow_eq_one Q p)

/-- **Upper-tail Hoeffding inequality for `Bin(Q, p)`**: for `p ∈ [0, 1]` and `0 ≤ t`, the
binomial probability mass on `k - Q p ≥ t` is at most `exp (-2 t² / Q)`. At `Q = 0` the right-hand
side is `exp 0 = 1`. -/
theorem sum_filter_le_sub_choose_mul_pow_le (Q : ℕ) {p t : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ht : 0 ≤ t) :
    ∑ k ∈ range (Q + 1) with t ≤ ((k : ℕ) : ℝ) - Q * p,
      (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) ≤
    exp (-2 * t ^ 2 / Q) := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · exact (sum_filter_choose_mul_pow_le_one 0 hp₀ hp₁ _).trans_eq
      (by simp only [Nat.cast_zero, div_zero, exp_zero])
  have hQ_pos : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  set s : ℝ := 4 * t / Q
  have hs : 0 ≤ s := by positivity
  set S : ℝ := ∑ k ∈ range (Q + 1) with t ≤ ((k : ℕ) : ℝ) - Q * p,
    (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k)
  have hmarkov : S * exp (s * t) ≤ exp (2 * t ^ 2 / Q) := by
    calc S * exp (s * t)
        = ∑ k ∈ range (Q + 1) with t ≤ ((k : ℕ) : ℝ) - Q * p,
            (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) * exp (s * t) := sum_mul _ _ _
      _ ≤ ∑ k ∈ range (Q + 1) with t ≤ ((k : ℕ) : ℝ) - Q * p,
            (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) * exp (s * ((k : ℝ) - Q * p)) := by
          refine sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
            (exp_le_exp.mpr (mul_le_mul_of_nonneg_left (mem_filter.mp hk).2 hs))
            (choose_mul_pow_nonneg Q k hp₀ hp₁)
      _ ≤ ∑ k ∈ range (Q + 1),
            (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) * exp (s * ((k : ℝ) - Q * p)) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun k _ _ =>
            mul_nonneg (choose_mul_pow_nonneg Q k hp₀ hp₁) (exp_pos _).le
      _ = ((1 - p) * exp (-s * p) + p * exp (s * (1 - p))) ^ Q :=
          sum_choose_mul_pow_mul_exp Q p s
      _ ≤ exp (s ^ 2 / 8) ^ Q :=
          pow_le_pow_left₀ (by have h1p : 0 ≤ 1 - p := sub_nonneg.mpr hp₁; positivity)
            (one_sub_mul_exp_add_mul_exp_le hp₀ hp₁ s) Q
      _ = exp (2 * t ^ 2 / Q) := by
          rw [← exp_nat_mul]
          congr 1
          dsimp only [s]
          field_simp
          ring
  have hexp_st : exp (s * t) = exp (2 * t ^ 2 / Q) * exp (2 * t ^ 2 / Q) := by
    rw [← exp_add]
    congr 1
    dsimp only [s]
    field_simp
    ring
  change S ≤ exp (-2 * t ^ 2 / Q)
  rw [show -2 * t ^ 2 / (Q : ℝ) = -(2 * t ^ 2 / Q) by ring, exp_neg, inv_eq_one_div,
    le_div_iff₀ (exp_pos _)]
  rw [hexp_st] at hmarkov
  nlinarith [hmarkov, exp_pos (2 * t ^ 2 / Q)]

/-- **Lower-tail Hoeffding inequality for `Bin(Q, p)`**: for `p ∈ [0, 1]` and `0 ≤ t`, the
binomial probability mass on `Q p - k ≥ t` is at most `exp (-2 t² / Q)`. -/
theorem sum_filter_le_mul_sub_choose_mul_pow_le (Q : ℕ) {p t : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ht : 0 ≤ t) :
    ∑ k ∈ range (Q + 1) with t ≤ Q * p - ((k : ℕ) : ℝ),
      (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) ≤
    exp (-2 * t ^ 2 / Q) := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · exact (sum_filter_choose_mul_pow_le_one 0 hp₀ hp₁ _).trans_eq
      (by simp only [Nat.cast_zero, div_zero, exp_zero])
  have hQ_pos : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  set s : ℝ := 4 * t / Q
  have hs : 0 ≤ s := by positivity
  set S : ℝ := ∑ k ∈ range (Q + 1) with t ≤ Q * p - ((k : ℕ) : ℝ),
    (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k)
  have hmarkov : S * exp (s * t) ≤ exp (2 * t ^ 2 / Q) := by
    calc S * exp (s * t)
        = ∑ k ∈ range (Q + 1) with t ≤ Q * p - ((k : ℕ) : ℝ),
            (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) * exp (s * t) := sum_mul _ _ _
      _ ≤ ∑ k ∈ range (Q + 1) with t ≤ Q * p - ((k : ℕ) : ℝ),
            (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) * exp ((-s) * ((k : ℝ) - Q * p)) := by
          refine sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_)
            (choose_mul_pow_nonneg Q k hp₀ hp₁)
          have hk' := (mem_filter.mp hk).2
          calc s * t ≤ s * (Q * p - (k : ℝ)) := mul_le_mul_of_nonneg_left hk' hs
            _ = (-s) * ((k : ℝ) - Q * p) := by ring
      _ ≤ ∑ k ∈ range (Q + 1),
            (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) * exp ((-s) * ((k : ℝ) - Q * p)) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun k _ _ =>
            mul_nonneg (choose_mul_pow_nonneg Q k hp₀ hp₁) (exp_pos _).le
      _ = ((1 - p) * exp (-(-s) * p) + p * exp ((-s) * (1 - p))) ^ Q :=
          sum_choose_mul_pow_mul_exp Q p (-s)
      _ ≤ exp ((-s) ^ 2 / 8) ^ Q :=
          pow_le_pow_left₀ (by have h1p : 0 ≤ 1 - p := sub_nonneg.mpr hp₁; positivity)
            (one_sub_mul_exp_add_mul_exp_le hp₀ hp₁ (-s)) Q
      _ = exp (2 * t ^ 2 / Q) := by
          rw [← exp_nat_mul]
          congr 1
          dsimp only [s]
          field_simp
          ring
  have hexp_st : exp (s * t) = exp (2 * t ^ 2 / Q) * exp (2 * t ^ 2 / Q) := by
    rw [← exp_add]
    congr 1
    dsimp only [s]
    field_simp
    ring
  change S ≤ exp (-2 * t ^ 2 / Q)
  rw [show -2 * t ^ 2 / (Q : ℝ) = -(2 * t ^ 2 / Q) by ring, exp_neg, inv_eq_one_div,
    le_div_iff₀ (exp_pos _)]
  rw [hexp_st] at hmarkov
  nlinarith [hmarkov, exp_pos (2 * t ^ 2 / Q)]

/-- **Two-sided Hoeffding inequality for `Bin(Q, p)`** `[Hoeffding1963]`: for `p ∈ [0, 1]` and
`0 ≤ t`, the binomial probability mass on `|k - Q p| ≥ t` is at most `2 exp (-2 t² / Q)`. -/
theorem sum_filter_le_abs_sub_choose_mul_pow_le (Q : ℕ) {p t : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ht : 0 ≤ t) :
    ∑ k ∈ range (Q + 1) with t ≤ |((k : ℕ) : ℝ) - Q * p|,
      (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) ≤
    2 * exp (-2 * t ^ 2 / Q) := by
  let w : ℕ → ℝ := fun k => (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k)
  let A : Finset ℕ := (range (Q + 1)).filter fun k : ℕ => t ≤ (k : ℝ) - Q * p
  let B : Finset ℕ := (range (Q + 1)).filter fun k : ℕ => t ≤ Q * p - (k : ℝ)
  let C : Finset ℕ := (range (Q + 1)).filter fun k : ℕ => t ≤ |(k : ℝ) - Q * p|
  have hsub : C ⊆ A ∪ B := by
    intro k hk
    simp only [C, A, B, mem_filter, mem_union] at hk ⊢
    rcases le_abs.mp hk.2 with h | h
    · exact Or.inl ⟨hk.1, h⟩
    · exact Or.inr ⟨hk.1, by linarith⟩
  have hunion : ∑ k ∈ A ∪ B, w k ≤ ∑ k ∈ A, w k + ∑ k ∈ B, w k := by
    have h := sum_union_inter (s₁ := A) (s₂ := B) (f := w)
    have hinter : 0 ≤ ∑ k ∈ A ∩ B, w k :=
      sum_nonneg fun k _ => choose_mul_pow_nonneg Q k hp₀ hp₁
    linarith
  calc ∑ k ∈ C, w k
      ≤ ∑ k ∈ A ∪ B, w k :=
        sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => choose_mul_pow_nonneg Q k hp₀ hp₁
    _ ≤ ∑ k ∈ A, w k + ∑ k ∈ B, w k := hunion
    _ ≤ exp (-2 * t ^ 2 / Q) + exp (-2 * t ^ 2 / Q) :=
        add_le_add (sum_filter_le_sub_choose_mul_pow_le Q hp₀ hp₁ ht)
          (sum_filter_le_mul_sub_choose_mul_pow_le Q hp₀ hp₁ ht)
    _ = 2 * exp (-2 * t ^ 2 / Q) := by ring

/-- **Interval-complement Hoeffding bound for `Bin(Q, p)`**: if `I` contains every integer
`0 ≤ k ≤ Q` within `t` of the mean `Q p`, then the binomial mass outside `I` is at most
`2 exp (-2 t² / Q)`. -/
theorem sum_filter_notMem_choose_mul_pow_le (Q : ℕ) (I : Finset ℕ) {p t : ℝ} (hp₀ : 0 ≤ p)
    (hp₁ : p ≤ 1) (ht : 0 ≤ t)
    (hI : ∀ k ∈ range (Q + 1), |(k : ℝ) - Q * p| ≤ t → k ∈ I) :
    ∑ k ∈ range (Q + 1) with k ∉ I,
      (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) ≤
    2 * exp (-2 * t ^ 2 / Q) := by
  refine (sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ =>
    choose_mul_pow_nonneg Q k hp₀ hp₁).trans (sum_filter_le_abs_sub_choose_mul_pow_le Q hp₀ hp₁ ht)
  intro k hk
  simp only [mem_filter] at hk ⊢
  refine ⟨hk.1, ?_⟩
  rcases le_or_gt (|(k : ℝ) - Q * p|) t with hle | hgt
  · exact False.elim (hk.2 (hI k hk.1 hle))
  · exact hgt.le

end Cslib
