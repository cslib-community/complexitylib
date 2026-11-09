/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.IID
public import Cslib.Probability.StatisticalDistance
public import Mathlib.Analysis.SpecialFunctions.Exp
import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Probability.StatisticalDistance.Event
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Statistical distance of independent repetitions

`k` independent draws from two distributions at statistical distance `δ` are at distance at least
`1 - 2 exp (-k δ² / 2)` (`one_sub_two_mul_exp_le_dist_iid`). This is the lower half of the
Direct Product Lemma of Sahai and Vadhan [SahaiVadhan2003, Lemma 3.4]; the upper half,
`dist (iid μ k) (iid ν k) ≤ k δ`, is `Cslib.Probability.PMF.dist_iid_le`.

The distinguisher counts the coordinates that fall in the event `S` on which `μ` is more likely
than `ν`. Each coordinate lands in `S` with probability `p` under `μ` and `q = p - δ` under `ν`, so
the count concentrates near `k p` under `μ` and near `k q` under `ν`. Hoeffding's inequality
(`Cslib.Probability.PMF.pi_sum_ge_mean_add`, `Cslib.Probability.PMF.pi_sum_le_mean_sub`) bounds
the probability that the count crosses the midpoint threshold, under either distribution, by
`exp (-k δ² / 2)`.

## Main results

* `Cslib.Probability.PMF.one_sub_two_mul_exp_le_dist_iid`: the direct-product lower bound.

## References

* [A. Sahai, S. Vadhan, *A complete problem for statistical zero knowledge*][SahaiVadhan2003]
* [W. Hoeffding, *Probability inequalities for sums of bounded random variables*][Hoeffding1963]
-/

public section

namespace Cslib.Probability.PMF

variable {α : Type*} [Fintype α]

/-- **Direct product lower bound** [SahaiVadhan2003, Lemma 3.4]: `k` independent draws from `μ` and
from `ν` are at statistical distance at least `1 - 2 exp (-k δ² / 2)`, where `δ = dist μ ν`.
Together with `dist_iid_le` this is the Direct Product Lemma. -/
theorem one_sub_two_mul_exp_le_dist_iid (μ ν : PMF α) (k : ℕ) :
    1 - 2 * Real.exp (-(k * dist μ ν ^ 2) / 2) ≤ dist (iid μ k) (iid ν k) := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, zero_mul, neg_zero, zero_div, Real.exp_zero]
    linarith [dist_nonneg (x := iid μ 0) (y := iid ν 0)]
  set d := dist μ ν with hd
  -- The event on which `μ` is more likely than `ν`, and its probabilities.
  set S : Set α := {a | (ν a).toReal < (μ a).toReal} with hS
  set p := (μ.toOuterMeasure S).toReal with hp
  set q := (ν.toOuterMeasure S).toReal with hq
  have hpq : p - q = d := by
    rw [hp, hq, toOuterMeasure_apply_toReal, toOuterMeasure_apply_toReal, hd,
      dist_eq_sum_filter_lt, ← Finset.sum_sub_distrib, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hS, Set.mem_ofPred_eq]
    split_ifs <;> ring
  -- The count of coordinates in `S`.
  let score : Fin k → α → ℝ := fun _ a => if a ∈ S then 1 else 0
  have hscore (r : PMF α) : ∀ i a, a ∈ r.support → score i a ∈ Set.Icc (0 : ℝ) 1 :=
    fun i a _ => by by_cases ha : a ∈ S <;> simp [score, ha]
  have hmean (r : PMF α) :
      ∑ i : Fin k, ∑ a, (r a).toReal * score i a = k * (r.toOuterMeasure S).toReal := by
    rw [toOuterMeasure_apply_toReal]
    simp only [score, mul_ite, mul_one, mul_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  set ε : ℝ := k * d / 2 with hε
  have hε0 : 0 ≤ ε := by positivity
  have hkR : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hexp : -2 * ε ^ 2 / ((Fintype.card (Fin k) : ℝ) * 1 ^ 2) = -(k * d ^ 2) / 2 := by
    rw [Fintype.card_fin, hε]
    field_simp
  -- Under `ν`, the count reaches the midpoint only with exponentially small probability.
  set E : Set (Fin k → α) := {x | k * q + ε ≤ ∑ i, score i (x i)} with hE
  have hν : ((iid ν k).toOuterMeasure E).toReal ≤ Real.exp (-(k * d ^ 2) / 2) := by
    have h := pi_sum_ge_mean_add (fun _ : Fin k => ν) score zero_le_one (hscore ν) hε0
    rw [hmean, hexp] at h
    rwa [iid_eq_pi]
  -- Under `μ`, the count stays above the midpoint except with exponentially small probability.
  have hμ : 1 - Real.exp (-(k * d ^ 2) / 2) ≤ ((iid μ k).toOuterMeasure E).toReal := by
    have h := pi_sum_le_mean_sub (fun _ : Fin k => μ) score zero_le_one (hscore μ) hε0
    rw [hmean, hexp, ← hp, ← iid_eq_pi] at h
    have hsub : Eᶜ ⊆ {x : Fin k → α | ∑ i, score i (x i) ≤ k * p - ε} := by
      intro x hx
      simp only [hE, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx
      simp only [Set.mem_ofPred_eq]
      have : k * q + ε = k * p - ε := by
        rw [hε, ← hpq]
        ring
      linarith
    have hmono : ((iid μ k).toOuterMeasure Eᶜ).toReal ≤
        ((iid μ k).toOuterMeasure {x : Fin k → α | ∑ i, score i (x i) ≤ k * p - ε}).toReal :=
      toOuterMeasure_toReal_mono (iid μ k) hsub
    have hc := toOuterMeasure_toReal_add_compl (iid μ k) E
    linarith
  have hdist := abs_toOuterMeasure_toReal_sub_le_dist (iid μ k) (iid ν k) E
  linarith [le_abs_self (((iid μ k).toOuterMeasure E).toReal -
    ((iid ν k).toOuterMeasure E).toReal)]

end Cslib.Probability.PMF
