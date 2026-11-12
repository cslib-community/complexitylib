/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.OptimalStopping.Prophet
public import Mathlib.Analysis.SpecialFunctions.Exponential
import CslibFrontier.Probability.PMF.TailQuantile
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import CslibFrontier.Probability.PMF.Bool

/-!
# The i.i.d. prophet inequality with one randomized threshold

When the `n` values are i.i.d., a single threshold does better than half the prophet's expected
reward. Each value `X ~ μ` comes with an independent tie-breaking coin (`withCoin`). The rule
`tieRule τ` accepts the first value above `τ`, or equal to `τ` when its coin shows `true`.
`one_sub_pow_mul_expectedMax_le` proves that if this rule accepts each value with probability
`1/n`, it collects at least `1 - (1 - 1/n)ⁿ ≥ 1 - 1/e` of `E[max]`
(`ofReal_one_sub_exp_mul_expectedMax_le`). Such a threshold and coin exist for every law
(`exists_tieAccept_eq`, from `PMF.exists_tail_quantile`). The coin fills the atom at `τ`, and it is
needed for the constant `1 - (1 - 1/n)ⁿ`: the library's optimal-stopping tests exhibit two
i.i.d. values on which every deterministic time-invariant rule falls short of `1 - (1 - 1/2)²`.

The proof writes `A = E[X; accept]`.
* The prophet's side is `E[max] ≤ τ + n E[(X - τ)⁺] = n A` (`expectedMax_replicate_le`), because
  the rule accepts every value above `τ` and only values of at least `τ`.
* The gambler collects `A ∑_{i<n} (1 - 1/n)ⁱ`, since each value is reached with probability
  `(1 - 1/n)ⁱ`.
* The geometric sum `∑_{i<n} (1 - 1/n)ⁱ = n (1 - (1 - 1/n)ⁿ)` finishes the proof.

A randomized rule is a mixture of deterministic ones, so the optimal deterministic gambler does
at least as well (`tieExpectedReward_le_valueFrom`). Hence `optimalRule` collects at least
`1 - (1 - 1/n)ⁿ` of `E[max]` on i.i.d. values
(`one_sub_pow_mul_expectedMax_le_expectedReward_optimalRule`). The constant `1 - 1/e` is not
optimal for adaptive rules. The tight i.i.d. constant `≈ 0.745` and its matching threshold
policies are not formalized here.

## Main definitions

* `Cslib.Probability.OptimalStopping.Prophet.withCoin`: a value with an independent coin.
* `Cslib.Probability.OptimalStopping.Prophet.tieRule`: one threshold with randomized ties.
* `Cslib.Probability.OptimalStopping.Prophet.tieExpectedReward`: its expected reward.

## Main results

* `Cslib.Probability.OptimalStopping.Prophet.one_sub_pow_mul_expectedMax_le`: the
  `1 - (1 - 1/n)ⁿ` bound when the rule accepts each value with probability `1/n`.
* `Cslib.Probability.OptimalStopping.Prophet.exists_one_sub_pow_mul_expectedMax_le`: such a rule
  exists for every law, with both the `1 - (1 - 1/n)ⁿ` and `1 - 1/e` bounds.
* `Cslib.Probability.OptimalStopping.Prophet.tieExpectedReward_le_valueFrom` and
  `one_sub_pow_mul_expectedMax_le_expectedReward_optimalRule`: the same bounds for the optimal
  deterministic gambler.

## References

The single-threshold `1 - 1/e` guarantee is classical. It reappears, for random arrival orders,
in the prophet-secretary literature, which also treats the optimal i.i.d. constant.

* [S. Ehsani, M. Hajiaghayi, T. Kesselheim, S. Singla, *Prophet secretary for combinatorial
  auctions and matroids*][EhsaniHajiaghayiKesselheimSingla2018]
* [J. Correa, P. Foncea, R. Hoeksma, T. Oosterwijk, T. Vredeveld, *Posted price mechanisms and
  optimal threshold strategies for random arrivals*][CorreaFonceaHoeksmaOosterwijkVredeveld2021]
-/

public section

namespace Cslib.Probability.OptimalStopping.Prophet

open scoped ENNReal NNReal
open Set

/-- A value drawn from `μ` together with an independent tie-breaking coin. -/
noncomputable def withCoin (coin : PMF Bool) (μ : PMF ℝ≥0) : PMF (ℝ≥0 × Bool) := do
  let x ← μ
  let b ← coin
  return (x, b)

/-- Accept a value above `τ`, and a value equal to `τ` when the coin shows `true`. -/
@[expose] noncomputable def tieAccept (τ : ℝ≥0) (o : ℝ≥0 × Bool) : Bool :=
  decide (τ < o.1) || (decide (o.1 = τ) && o.2)

/-- The single-threshold rule with randomized tie-breaking. -/
@[expose] noncomputable def tieRule (τ : ℝ≥0) : List (ℝ≥0 × Bool) → Bool
  | [] => false
  | o :: _ => tieAccept τ o

/-- The gambler collects the value, not the coin, at which it stops. -/
@[expose] def coinReward : List (ℝ≥0 × Bool) → List (ℝ≥0 × Bool) → ℝ≥0∞
  | [], _ => 0
  | o :: _, _ => o.1

/-- The expected reward of `tieRule τ` on independent values with laws `laws`, each with an
independent coin. -/
noncomputable def tieExpectedReward (τ : ℝ≥0) (coin : PMF Bool) (laws : List (PMF ℝ≥0)) :
    ℝ≥0∞ :=
  ∑' os, jointLaw (laws.map (withCoin coin)) os * payoff (tieRule τ) coinReward [] os

theorem tieExpectedReward_eq (τ : ℝ≥0) (coin : PMF Bool) (laws : List (PMF ℝ≥0)) :
    tieExpectedReward τ coin laws =
      ∑' os, jointLaw (laws.map (withCoin coin)) os * payoff (tieRule τ) coinReward [] os := by
  unfold tieExpectedReward; rfl

private noncomputable def tiePayoff (τ : ℝ≥0) : List (ℝ≥0 × Bool) → ℝ≥0∞
  | [] => 0
  | o :: os => if tieAccept τ o then (o.1 : ℝ≥0∞) else tiePayoff τ os

private theorem payoff_tieRule (τ : ℝ≥0) :
    ∀ past os, payoff (tieRule τ) coinReward past os = tiePayoff τ os
  | _, [] => rfl
  | past, o :: os => by
      rw [payoff_cons, tiePayoff]
      change (if tieAccept τ o = true then (o.1 : ℝ≥0∞) else _) = _
      rw [payoff_tieRule τ (o :: past) os]

/-- An expectation under `withCoin coin μ` averages over the value and the independent coin. -/
theorem tsum_withCoin_mul (coin : PMF Bool) (μ : PMF ℝ≥0) (f : ℝ≥0 × Bool → ℝ≥0∞) :
    ∑' o, withCoin coin μ o * f o =
      ∑' x, μ x * (coin true * f (x, true) + coin false * f (x, false)) := by
  change ∑' o, (μ.bind fun x => coin.bind fun b => PMF.pure (x, b)) o * f o = _
  rw [Cslib.Probability.PMF.tsum_bind_mul]
  refine tsum_congr fun x => ?_
  rw [Cslib.Probability.PMF.tsum_bind_mul, tsum_fintype, Fintype.sum_bool]
  simp only [tsum_pure_mul]

private theorem tsum_withCoin_mul_fst (coin : PMF Bool) (μ : PMF ℝ≥0) (g : ℝ≥0 → ℝ≥0∞) :
    ∑' o, withCoin coin μ o * g o.1 = ∑' x, μ x * g x := by
  rw [tsum_withCoin_mul]
  refine tsum_congr fun x => ?_
  rw [← add_mul, PMF.apply_true_add_apply_false, one_mul]

private theorem toOuterMeasure_eq_tsum_bool {α : Type*} (p : PMF α) (a : α → Bool) :
    p.toOuterMeasure {o | a o = true} = ∑' o, p o * (if a o then 1 else 0) := by
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun o => ?_
  by_cases h : a o = true <;> simp [h]

/-- The probability that `tieAccept τ` accepts a value is `P(X > τ) + P(coin) P(X = τ)`. -/
theorem toOuterMeasure_tieAccept (τ : ℝ≥0) (coin : PMF Bool) (μ : PMF ℝ≥0) :
    (withCoin coin μ).toOuterMeasure {o | tieAccept τ o = true} =
      μ.toOuterMeasure (Ioi τ) + coin true * μ τ := by
  rw [toOuterMeasure_eq_tsum_bool, tsum_withCoin_mul, PMF.toOuterMeasure_apply]
  have hτ : coin true * μ τ = ∑' x, μ x * (if x = τ then coin true else 0) := by
    rw [tsum_eq_single τ fun x hx => by simp [hx]]
    simp [mul_comm]
  rw [hτ, ← tsum_add]
  refine tsum_congr fun x => ?_
  have hcoin := PMF.apply_true_add_apply_false coin
  rcases lt_trichotomy τ x with h | h | h
  · simp [tieAccept, h, h.ne', hcoin]
  · subst h
    simp [tieAccept]
  · simp [tieAccept, h.ne, not_lt.mpr h.le]

private theorem accept_value_eq (τ : ℝ≥0) (o : ℝ≥0 × Bool) :
    (if tieAccept τ o then (o.1 : ℝ≥0∞) else 0) =
      τ * (if tieAccept τ o then 1 else 0) + ((o.1 - τ : ℝ≥0) : ℝ≥0∞) := by
  by_cases h : tieAccept τ o = true
  · have hle : τ ≤ o.1 := by
      simp only [tieAccept, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
      rcases h with h | ⟨h, -⟩
      · exact h.le
      · exact h.ge
    simp only [h, ↓reduceIte, mul_one]
    rw [← ENNReal.coe_add, add_tsub_cancel_of_le hle]
  · have hle : o.1 ≤ τ := by
      simp only [tieAccept, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, not_or,
        not_and] at h
      exact not_lt.mp h.1
    have h' : tieAccept τ o = false := by simpa using h
    simp [h', tsub_eq_zero_of_le hle]

private theorem geom_step (A R : ℝ≥0∞) (n : ℕ) :
    A + R * (A * ∑ i ∈ Finset.range n, R ^ i) = A * ∑ i ∈ Finset.range (n + 1), R ^ i := by
  rw [Finset.sum_range_succ', mul_add, pow_zero, mul_one, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, add_comm A]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem tsum_tiePayoff_replicate (τ : ℝ≥0) (ν : PMF (ℝ≥0 × Bool)) : ∀ n : ℕ,
    ∑' os, jointLaw (List.replicate n ν) os * tiePayoff τ os =
      (∑' o, ν o * (if tieAccept τ o then (o.1 : ℝ≥0∞) else 0)) *
        ∑ i ∈ Finset.range n, (∑' o, ν o * (if tieAccept τ o then 0 else 1)) ^ i
  | 0 => by simp [tiePayoff]
  | n + 1 => by
      rw [List.replicate_succ, tsum_jointLaw_cons_mul, ← geom_step,
        ← tsum_tiePayoff_replicate τ ν n, ← ENNReal.tsum_mul_right, ← tsum_add]
      refine tsum_congr fun o => ?_
      by_cases h : tieAccept τ o = true
      · simp only [tiePayoff, h, ↓reduceIte, tsum_pmf_mul_const, mul_zero, zero_mul, add_zero]
      · have h' : tieAccept τ o = false := by simpa using h
        simp only [tiePayoff, h', Bool.false_eq_true, ↓reduceIte, mul_one, zero_add, mul_zero]

private theorem geom_identity {p r : ℝ≥0∞} (h : p + r = 1) : ∀ n : ℕ,
    p * ∑ i ∈ Finset.range n, r ^ i + r ^ n = 1
  | 0 => by simp
  | n + 1 => by
      calc p * ∑ i ∈ Finset.range (n + 1), r ^ i + r ^ (n + 1)
          = p * ∑ i ∈ Finset.range n, r ^ i + r ^ n * (p + r) := by
            rw [Finset.sum_range_succ, pow_succ]; ring
        _ = 1 := by rw [h, mul_one, geom_identity h n]

/-- **The i.i.d. prophet inequality with one randomized threshold.** If `tieRule τ`, with a
tie-breaking coin, accepts each of `n` i.i.d. values with probability `1/n`, it collects at
least `1 - (1 - 1/n)ⁿ` of the prophet's expected reward. -/
theorem one_sub_pow_mul_expectedMax_le {n : ℕ} (μ : PMF ℝ≥0) (τ : ℝ≥0) (coin : PMF Bool)
    (hacc : (withCoin coin μ).toOuterMeasure {o | tieAccept τ o = true} = (n : ℝ≥0∞)⁻¹) :
    (1 - (1 - (n : ℝ≥0∞)⁻¹) ^ n) * expectedMax (List.replicate n μ) ≤
      tieExpectedReward τ coin (List.replicate n μ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set ν := withCoin coin μ with hν
  set p := ∑' o, ν o * (if tieAccept τ o then (1 : ℝ≥0∞) else 0) with hp_def
  set r := ∑' o, ν o * (if tieAccept τ o then (0 : ℝ≥0∞) else 1) with hr_def
  set A := ∑' o, ν o * (if tieAccept τ o then (o.1 : ℝ≥0∞) else 0) with hA_def
  set B := ∑' x, μ x * ((x - τ : ℝ≥0) : ℝ≥0∞) with hB_def
  have hp : p = (n : ℝ≥0∞)⁻¹ := by rw [← hacc, toOuterMeasure_eq_tsum_bool]
  have hpr : p + r = 1 := by
    rw [hp_def, hr_def, ← tsum_add, ← ν.tsum_coe]
    refine tsum_congr fun o => ?_
    by_cases h : tieAccept τ o = true <;> simp [h]
  have hpne : p ≠ ⊤ := by rw [hp]; exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hn.ne')
  have hr : r = 1 - (n : ℝ≥0∞)⁻¹ := by
    rw [← hp]; exact ENNReal.eq_sub_of_add_eq hpne (by rw [add_comm]; exact hpr)
  have hE : tieExpectedReward τ coin (List.replicate n μ) =
      A * ∑ i ∈ Finset.range n, r ^ i := by
    rw [tieExpectedReward, List.map_replicate, ← tsum_tiePayoff_replicate]
    exact tsum_congr fun os => by rw [payoff_tieRule]
  have hA : A = τ * p + B := by
    rw [hA_def, hp_def, hB_def, ← tsum_withCoin_mul_fst coin μ, ← ENNReal.tsum_mul_left,
      ← tsum_add]
    refine tsum_congr fun o => ?_
    rw [accept_value_eq, mul_add]
    ring
  have hM : expectedMax (List.replicate n μ) ≤ n * A := by
    have hnp : (n : ℝ≥0∞) * p = 1 :=
      by rw [hp]; exact ENNReal.mul_inv_cancel (by exact_mod_cast hn.ne') (by simp)
    calc expectedMax (List.replicate n μ) ≤ τ + n * B := expectedMax_replicate_le τ μ n
      _ = n * A := by
        rw [hA]
        calc (τ : ℝ≥0∞) + n * B = τ * (n * p) + n * B := by rw [hnp, mul_one]
          _ = n * (τ * p + B) := by ring
  have hgeom : 1 - r ^ n = p * ∑ i ∈ Finset.range n, r ^ i :=
    ENNReal.sub_eq_of_eq_add (ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top
      (by rw [← hpr]; exact le_add_self))) (geom_identity hpr n).symm
  rw [hE, ← hr, hgeom]
  have hnp : p * (n : ℝ≥0∞) = 1 := by
    rw [hp]; exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp)
  calc p * (∑ i ∈ Finset.range n, r ^ i) * expectedMax (List.replicate n μ)
      ≤ p * (∑ i ∈ Finset.range n, r ^ i) * (n * A) := by gcongr
    _ = (p * n) * (A * ∑ i ∈ Finset.range n, r ^ i) := by ring
    _ = A * ∑ i ∈ Finset.range n, r ^ i := by rw [hnp, one_mul]

private theorem ofReal_one_sub_exp_le {n : ℕ} (hn : 0 < n) :
    ENNReal.ofReal (1 - Real.exp (-1)) ≤ 1 - (1 - (n : ℝ≥0∞)⁻¹) ^ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (1 - (n : ℝ≥0∞)⁻¹) = ENNReal.ofReal (1 - 1 / n) := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, one_div,
      ENNReal.ofReal_inv_of_pos hn', ENNReal.ofReal_natCast]
  have hnn : (0 : ℝ) ≤ 1 - 1 / n := by
    rw [sub_nonneg, div_le_one hn']; exact_mod_cast hn
  rw [h1, ← ENNReal.ofReal_pow hnn, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ (pow_nonneg hnn n)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := Real.one_sub_div_pow_le_exp_neg (n := n) (t := 1) (by exact_mod_cast hn)
  linarith

/-- **The i.i.d. prophet inequality, `1 - 1/e` form.** -/
theorem ofReal_one_sub_exp_mul_expectedMax_le {n : ℕ} (μ : PMF ℝ≥0) (τ : ℝ≥0) (coin : PMF Bool)
    (hacc : (withCoin coin μ).toOuterMeasure {o | tieAccept τ o = true} = (n : ℝ≥0∞)⁻¹) :
    ENNReal.ofReal (1 - Real.exp (-1)) * expectedMax (List.replicate n μ) ≤
      tieExpectedReward τ coin (List.replicate n μ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [expectedMax, listMax]
  calc ENNReal.ofReal (1 - Real.exp (-1)) * expectedMax (List.replicate n μ)
      ≤ (1 - (1 - (n : ℝ≥0∞)⁻¹) ^ n) * expectedMax (List.replicate n μ) := by
        gcongr; exact ofReal_one_sub_exp_le hn
    _ ≤ _ := one_sub_pow_mul_expectedMax_le μ τ coin hacc

/-- Every acceptance probability `q ∈ (0, 1]` is attained by a threshold with a tie-breaking
coin. -/
theorem exists_tieAccept_eq (μ : PMF ℝ≥0) {q : ℝ≥0∞} (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ (τ : ℝ≥0) (coin : PMF Bool),
      (withCoin coin μ).toOuterMeasure {o | tieAccept τ o = true} = q := by
  obtain ⟨τ, hgt, hge⟩ := PMF.exists_tail_quantile μ hq hq1
  have hIci : μ.toOuterMeasure (Ici τ) = μ.toOuterMeasure (Ioi τ) + μ τ := by
    simp only [← PMF.toMeasure_apply_eq_toOuterMeasure]
    rw [← Ioi_union_left, MeasureTheory.measure_union (by simp) (measurableSet_singleton τ),
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton τ)]
  rw [hIci] at hge
  rcases eq_or_ne (μ τ) 0 with h0 | h0
  · refine ⟨τ, PMF.pure false, ?_⟩
    rw [toOuterMeasure_tieAccept, h0, mul_zero, add_zero]
    rw [h0, add_zero] at hge
    exact le_antisymm hgt hge
  set a := μ.toOuterMeasure (Ioi τ)
  have hβ : (q - a) / μ τ ≤ 1 := by
    rw [ENNReal.div_le_iff h0 (PMF.apply_ne_top _ _), one_mul, tsub_le_iff_left]
    exact hge
  refine ⟨τ, PMF.ofFintype (fun b => cond b ((q - a) / μ τ) (1 - (q - a) / μ τ)) ?_, ?_⟩
  · simp [add_tsub_cancel_of_le hβ]
  · rw [toOuterMeasure_tieAccept, PMF.ofFintype_apply, Bool.cond_true,
      ENNReal.div_mul_cancel h0 (PMF.apply_ne_top _ _), add_tsub_cancel_of_le hgt]

/-- **The i.i.d. prophet inequality**: for `n` i.i.d. values, some threshold with a tie-breaking
coin collects at least `1 - (1 - 1/n)ⁿ ≥ 1 - 1/e` of the prophet's expected reward. -/
theorem exists_one_sub_pow_mul_expectedMax_le (μ : PMF ℝ≥0) (n : ℕ) :
    ∃ (τ : ℝ≥0) (coin : PMF Bool),
      (1 - (1 - (n : ℝ≥0∞)⁻¹) ^ n) * expectedMax (List.replicate n μ) ≤
        tieExpectedReward τ coin (List.replicate n μ) ∧
      ENNReal.ofReal (1 - Real.exp (-1)) * expectedMax (List.replicate n μ) ≤
        tieExpectedReward τ coin (List.replicate n μ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, PMF.pure false, by simp [expectedMax, listMax]⟩
  obtain ⟨τ, coin, h⟩ := exists_tieAccept_eq μ (q := (n : ℝ≥0∞)⁻¹) (by simp)
    (ENNReal.inv_le_one.mpr (by exact_mod_cast hn))
  exact ⟨τ, coin, one_sub_pow_mul_expectedMax_le μ τ coin h,
    ofReal_one_sub_exp_mul_expectedMax_le μ τ coin h⟩

private theorem tsum_tiePayoff_le_valueFrom (τ : ℝ≥0) (coin : PMF Bool) :
    ∀ (laws : List (PMF ℝ≥0)) (past : List ℝ≥0),
      ∑' os, jointLaw (laws.map (withCoin coin)) os * tiePayoff τ os ≤ valueFrom reward laws past
  | [], _ => by simp [tiePayoff]
  | μ :: laws, past => by
      rw [List.map_cons, tsum_jointLaw_cons_mul, tsum_withCoin_mul, valueFrom_cons]
      refine tsum_le_tsum fun x => ?_
      gcongr μ x * ?_
      have hstop : ∑' xs, jointLaw laws xs * reward (x :: past) xs = x :=
        tsum_pmf_mul_const _ _
      have hle : ∀ b, ∑' os, jointLaw (laws.map (withCoin coin)) os * tiePayoff τ ((x, b) :: os) ≤
          max (∑' xs, jointLaw laws xs * reward (x :: past) xs)
            (valueFrom reward laws (x :: past)) := by
        intro b
        by_cases h : tieAccept τ (x, b) = true
        · simp only [tiePayoff, h, ↓reduceIte, tsum_pmf_mul_const]
          exact hstop.symm.le.trans (le_max_left _ _)
        · have h' : tieAccept τ (x, b) = false := by simpa using h
          simp only [tiePayoff, h', Bool.false_eq_true, ↓reduceIte]
          exact (tsum_tiePayoff_le_valueFrom τ coin laws (x :: past)).trans (le_max_right _ _)
      calc coin true * _ + coin false * _
          ≤ coin true * max (∑' xs, jointLaw laws xs * reward (x :: past) xs)
              (valueFrom reward laws (x :: past)) +
            coin false * max (∑' xs, jointLaw laws xs * reward (x :: past) xs)
              (valueFrom reward laws (x :: past)) := by gcongr <;> exact hle _
        _ = _ := by rw [← add_mul, PMF.apply_true_add_apply_false, one_mul]

/-- A randomized threshold collects no more than the optimal deterministic gambler. -/
theorem tieExpectedReward_le_valueFrom (τ : ℝ≥0) (coin : PMF Bool) (laws : List (PMF ℝ≥0)) :
    tieExpectedReward τ coin laws ≤ valueFrom reward laws [] := by
  rw [tieExpectedReward]
  simp only [payoff_tieRule]
  exact tsum_tiePayoff_le_valueFrom τ coin laws []

/-- **The optimal gambler on i.i.d. values** collects at least `1 - (1 - 1/n)ⁿ ≥ 1 - 1/e` of the
prophet's expected reward. -/
theorem one_sub_pow_mul_expectedMax_le_expectedReward_optimalRule (μ : PMF ℝ≥0) (n : ℕ) :
    (1 - (1 - (n : ℝ≥0∞)⁻¹) ^ n) * expectedMax (List.replicate n μ) ≤
        expectedReward (optimalRule reward (List.replicate n μ)) (List.replicate n μ) ∧
      ENNReal.ofReal (1 - Real.exp (-1)) * expectedMax (List.replicate n μ) ≤
        expectedReward (optimalRule reward (List.replicate n μ)) (List.replicate n μ) := by
  obtain ⟨τ, coin, h₁, h₂⟩ := exists_one_sub_pow_mul_expectedMax_le μ n
  rw [expectedReward, tsum_payoff_optimalRule]
  exact ⟨h₁.trans (tieExpectedReward_le_valueFrom τ coin _),
    h₂.trans (tieExpectedReward_le_valueFrom τ coin _)⟩

end Cslib.Probability.OptimalStopping.Prophet
