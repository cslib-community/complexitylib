/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Product
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.Exp
import CslibFrontier.Probability.BoundedDifferences
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Concentration for independent finite samples

The finite-PMF form of Hoeffding's inequality exposes ordinary sums and event probabilities.
Its proof specializes McDiarmid's bounded-differences inequality
(`CslibFrontier.Probability.BoundedDifferences`) to sums of bounded coordinate scores via linearity
of expectation (`sum_pi_mul_sum`). No measurable-space choices appear in the client-facing
statements.

## Main results

* `Cslib.Probability.PMF.pi_sum_le_mean_sub`: lower-tail concentration of bounded scores.
* `Cslib.Probability.PMF.pi_sum_ge_mean_add`: the corresponding upper-tail bound.
* `Cslib.Probability.PMF.pi_sum_abs_sub_mean_ge`: the two-sided bound.
* `Cslib.Probability.PMF.pi_abs_sum_div_sub_sum_mul_ge_le`: the two-sided bound for the
  empirical average of a `[-1, 1]`-valued function at independent samples of any distribution.
* `Cslib.Probability.PMF.uniform_abs_sum_div_sub_expect_ge_le`: its special case at independent
  uniform points.

## References

* [W. Hoeffding, *Probability inequalities for sums of bounded random variables*][Hoeffding1963].
* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Section 3.3 and Proposition 1.
  These bounded-score estimates support repetition in entropy extraction; they do not assert
  the full smoothed conditional-entropy statement of that proposition.

Adapted from Probability/Concentration.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing Mathlib's sub-Gaussian estimates.

-/

@[expose] public section

namespace Cslib.Probability.PMF

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]

omit [Fintype ι] [∀ i, Fintype (α i)] in
open Classical in
/-- Clamp each coordinate score to `0` outside the support of `p i`, so that it lies in
`[0, bound]` everywhere while preserving the score and its mean on the support of `pi p`. -/
private noncomputable def clampScore (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    (i : ι) (a : α i) : ℝ :=
  if a ∈ (p i).support then score i a else 0

omit [∀ i, Fintype (α i)] in
open Classical in
private theorem hasBoundedDifferences_clampScore (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc 0 bound) :
    HasBoundedDifferences (fun outcome => ∑ i, clampScore p score i (outcome i))
      (fun _ => bound) := by
  have hmem (i : ι) (a : α i) : clampScore p score i a ∈ Set.Icc 0 bound := by
    dsimp only [clampScore]
    split_ifs with ha
    · exact hscore i a ha
    · exact ⟨le_rfl, hbound⟩
  exact hasBoundedDifferences_sum fun i a b =>
    abs_sub_le_iff.mpr ⟨by linarith [(hmem i a).2, (hmem i b).1],
      by linarith [(hmem i b).2, (hmem i a).1]⟩

omit [∀ i, Fintype (α i)] in
private theorem sum_clampScore_eq_of_mem_support [∀ i, Finite (α i)]
    (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    {outcome : ∀ i, α i} (houtcome : outcome ∈ (pi p).support) :
    ∑ i, clampScore p score i (outcome i) = ∑ i, score i (outcome i) :=
  Finset.sum_congr rfl fun i _ => ite_eq_left ((mem_support_pi_iff p outcome).mp houtcome i)

private theorem sum_pi_mul_sum_clampScore_eq [DecidableEq ι]
    (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ) :
    ∑ y, (pi p y).toReal * ∑ i, clampScore p score i (y i) =
      ∑ i, ∑ a, (p i a).toReal * score i a := by
  rw [sum_pi_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  dsimp only [clampScore]
  split_ifs with ha
  · rfl
  · rw [((p i).apply_eq_zero_iff a).mpr ha, ENNReal.toReal_zero, zero_mul, zero_mul]

omit [Fintype ι] [∀ i, Fintype (α i)] in
private theorem toOuterMeasure_congr_on_support {β : Type*} (q : PMF β) {s t : Set β}
    (h : ∀ outcome ∈ q.support, outcome ∈ s ↔ outcome ∈ t) :
    q.toOuterMeasure s = q.toOuterMeasure t := by
  classical
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  refine tsum_congr fun outcome => ?_
  by_cases ho : outcome ∈ q.support
  · simp only [Set.indicator_apply, h outcome ho]
  · simp [Set.indicator_apply, (q.apply_eq_zero_iff outcome).mpr ho]

private theorem toOuterMeasure_pi_clampScore_eq [DecidableEq ι]
    (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ) (P : ℝ → ℝ → Prop) :
    (pi p).toOuterMeasure
      {outcome | P (∑ i, score i (outcome i)) (∑ i, ∑ a, (p i a).toReal * score i a)} =
    (pi p).toOuterMeasure
      {x | P (∑ i, clampScore p score i (x i))
        (∑ y, (pi p y).toReal * ∑ i, clampScore p score i (y i))} :=
  toOuterMeasure_congr_on_support (pi p) fun outcome ho => by
    simp only [Set.mem_ofPred_eq, sum_clampScore_eq_of_mem_support p score ho,
      sum_pi_mul_sum_clampScore_eq]

omit [∀ i, Fintype (α i)] in
private theorem sum_const_sq_eq (bound : ℝ) :
    (∑ _i : ι, bound ^ 2) = Fintype.card ι * bound ^ 2 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The sum of independent bounded scores falls below its mean only with exponentially small
probability. The scores and their means are finite sums; all probabilities are ordinary PMFs. -/
theorem pi_sum_le_mean_sub (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    {bound ε : ℝ} (hbound : 0 ≤ bound)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc 0 bound) (hε : 0 ≤ ε) :
    ((pi p).toOuterMeasure {outcome |
      ∑ i, score i (outcome i) ≤ (∑ i, ∑ a, (p i a).toReal * score i a) - ε}).toReal ≤
        Real.exp (-2 * ε ^ 2 / (Fintype.card ι * bound ^ 2)) := by
  classical
  rw [toOuterMeasure_pi_clampScore_eq p score (fun s m => s ≤ m - ε), ← sum_const_sq_eq]
  exact (hasBoundedDifferences_clampScore p score hbound hscore).pi_le_mean_sub p hε

/-- The upper-tail counterpart of `pi_sum_le_mean_sub`, obtained by clamping scores outside the
support and applying `HasBoundedDifferences.pi_ge_mean_add`. -/
theorem pi_sum_ge_mean_add (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    {bound ε : ℝ} (hbound : 0 ≤ bound)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc 0 bound) (hε : 0 ≤ ε) :
    ((pi p).toOuterMeasure {outcome |
      (∑ i, ∑ a, (p i a).toReal * score i a) + ε ≤ ∑ i, score i (outcome i)}).toReal ≤
        Real.exp (-2 * ε ^ 2 / (Fintype.card ι * bound ^ 2)) := by
  classical
  rw [toOuterMeasure_pi_clampScore_eq p score (fun s m => m + ε ≤ s), ← sum_const_sq_eq]
  exact (hasBoundedDifferences_clampScore p score hbound hscore).pi_ge_mean_add p hε

/-- The two-sided finite Hoeffding bound, with an explicit factor of two for the two tails. -/
theorem pi_sum_abs_sub_mean_ge (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    {bound ε : ℝ} (hbound : 0 ≤ bound)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc 0 bound) (hε : 0 ≤ ε) :
    ((pi p).toOuterMeasure {outcome |
      ε ≤ |(∑ i, score i (outcome i)) - ∑ i, ∑ a, (p i a).toReal * score i a|}).toReal ≤
        2 * Real.exp (-2 * ε ^ 2 / (Fintype.card ι * bound ^ 2)) := by
  linarith [toOuterMeasure_abs_sub_ge_toReal_le (pi p)
    (fun outcome => ∑ i, score i (outcome i)) (∑ i, ∑ a, (p i a).toReal * score i a) ε,
    pi_sum_ge_mean_add p score hbound hscore hε, pi_sum_le_mean_sub p score hbound hscore hε]

section Average

open Finset
open scoped BigOperators

/-- **Hoeffding's inequality for an empirical average** under any distribution: the average of a
function with values in `[-1, 1]` at `m` independent samples of `p` is off from its mean by at
least `γ` with probability at most `2 exp (-m γ² / 2)`. -/
theorem pi_abs_sum_div_sub_sum_mul_ge_le {m : ℕ} {α : Type*} [Fintype α] (p : PMF α)
    (s : α → ℝ) (hs : ∀ a, |s a| ≤ 1) {γ : ℝ} (hγ : 0 ≤ γ) :
    (pi fun _ : Fin m => p).toOuterMeasure
      {ω | γ ≤ |(∑ j, s (ω j)) / m - ∑ a, (p a).toReal * s a|} ≤
        ENNReal.ofReal (2 * Real.exp (-(m * γ ^ 2) / 2)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- without samples, the bound is at least one
    refine (PMF.toOuterMeasure_le_one _ _).trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [CharP.cast_eq_zero, zero_mul, neg_zero, zero_div, Real.exp_zero, mul_one]
    norm_num
  rw [ENNReal.le_ofReal_iff_toReal_le (toOuterMeasure_ne_top _ _) (by positivity)]
  set μ := ∑ a, (p a).toReal * s a
  have h := pi_sum_abs_sub_mean_ge (fun _ : Fin m => p)
    (fun _ a => 1 + s a) (bound := 2) (ε := m * γ) (by norm_num)
    (fun _ a _ => ⟨by linarith [(abs_le.1 (hs a)).1], by linarith [(abs_le.1 (hs a)).2]⟩)
    (by positivity)
  have hmean : ∑ a, (p a).toReal * (1 + s a) = 1 + μ := by
    simp only [mul_add, mul_one, sum_add_distrib, PMF.sum_toReal, μ]
  simp only [hmean, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hevent : {ω : Fin m → α | γ ≤ |(∑ j, s (ω j)) / m - μ|} =
      {ω | m * γ ≤ |∑ j, (1 + s (ω j)) - m * (1 + μ)|} := by
    ext ω
    have hsum : ∑ j, (1 + s (ω j)) - m * (1 + μ) = m * ((∑ j, s (ω j)) / m - μ) := by
      simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      field_simp
      ring
    simp only [Set.mem_ofPred_eq, hsum, abs_mul, abs_of_pos hmR]
    exact (mul_le_mul_iff_right₀ hmR).symm
  rw [hevent]
  refine h.trans_eq ?_
  congr 2
  field_simp

/-- **Hoeffding's inequality for an empirical average**: the average of a function with values in
`[-1, 1]` at `m` independent uniform points is off from its mean by at least `γ` with
probability at most `2 exp (-m γ² / 2)`. This is `pi_abs_sum_div_sub_sum_mul_ge_le` for the
uniform distribution. -/
theorem uniform_abs_sum_div_sub_expect_ge_le {m : ℕ} {α : Type*} [Fintype α] [Nonempty α]
    (s : α → ℝ) (hs : ∀ a, |s a| ≤ 1) {γ : ℝ} (hγ : 0 ≤ γ) :
    (PMF.uniformOfFintype (Fin m → α)).toOuterMeasure
      {ω | γ ≤ |(∑ j, s (ω j)) / m - 𝔼 a, s a|} ≤
        ENNReal.ofReal (2 * Real.exp (-(m * γ ^ 2) / 2)) := by
  have h := pi_abs_sum_div_sub_sum_mul_ge_le (m := m) (PMF.uniformOfFintype α) s hs hγ
  have hmean : ∑ a, ((PMF.uniformOfFintype α) a).toReal * s a = 𝔼 a, s a := by
    simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      expect_eq_sum_div_card, card_univ, inv_mul_eq_div, ← sum_div]
  rwa [pi_uniformOfFintype, hmean] at h

end Average

end Cslib.Probability.PMF
