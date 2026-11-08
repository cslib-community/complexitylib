/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Probability.OptimalStopping.Prophet
import CslibFrontier.Probability.OptimalStopping.ProphetIID
import CslibFrontier.Probability.OptimalStopping.Secretary

/-! Checks for optimal stopping: exact secretary success probabilities for small `n`, the optimal
cutoff for three candidates and the resulting optimal success probability `1/2`, a rule that never
stops; the prophet inequality's Kleinberg–Weinberg threshold on the tight instance, Samuel-Cahn's
median hypotheses and theorem (a degenerate law, and a law with an atom at the median), a
concrete violation of every constant above `1/2`, and the backward-induction value of the tight
instance; tail quantiles and the unconditional Samuel-Cahn theorem; and the i.i.d. bound
`1 - (1 - 1/n)ⁿ` on two values `fiveOrOne`, where the threshold `1` with a `3/8` tie-breaking coin
attains it and every deterministic memoryless rule falls short. -/

namespace ComplexityTests.OptimalStopping

open Cslib.Probability.OptimalStopping
open scoped ENNReal NNReal

/-! ### The secretary problem -/

namespace Secretary

open Cslib.Probability.OptimalStopping.Secretary

/-- With three candidates, skipping the first and hiring the next best-so-far wins with
probability `1/2`. -/
theorem successProb_cutoffRule_two_three : successProb (cutoffRule 2) 3 = 1 / 2 := by
  rw [successProb_cutoffRule (le_refl 2)]
  norm_num [Finset.sum_Icc_succ_top]

/-- With one candidate, hiring it always wins. -/
example : successProb (cutoffRule 1) 1 = 1 := by
  rw [successProb_cutoffRule_one]
  norm_num

/-- The optimal cutoff for three candidates is `2`: `1/2 ≤ 1 < 1 + 1/2`. -/
theorem optimalCutoff_three : optimalCutoff 3 = 2 := by
  refine le_antisymm (optimalCutoff_le (by norm_num) (by norm_num [Finset.sum_Ico_succ_top])) ?_
  by_contra hlt
  have h := sum_optimalCutoff_le 3
  rw [show optimalCutoff 3 = 1 by have := one_le_optimalCutoff 3; omega] at h
  norm_num [Finset.sum_Ico_succ_top] at h

/-- No rank-based rule hires the best of three candidates with probability more than `1/2`. -/
example (rule : Rule) : successProb rule 3 ≤ 1 / 2 := by
  have := successProb_le_successProb_optimalCutoff rule 3
  rwa [optimalCutoff_three, successProb_cutoffRule_two_three] at this

theorem stopIndex_never : ∀ past xs : List ℕ, stopIndex (fun _ => false) past xs = none
  | _, [] => rfl
  | past, x :: xs => by simp [stopIndex, stopIndex_never (x :: past) xs]

/-- A rule that never stops never wins. -/
example (n : ℕ) : successProb (fun _ => false) n = 0 := by
  simp [successProb, Wins, stopIndex_never]

/-- The optimal cutoff and `⌊n/e⌋ + 1` give nonvacuous two-sided bounds. -/
example (n : ℕ) (hn : 1 ≤ n) :
    Real.exp (-1) - 1 / n ≤ successProb (cutoffRule (optimalCutoff n)) n ∧
      successProb (cutoffRule (optimalCutoff n)) n ≤ Real.exp (-1) + 1 / n :=
  ⟨(exp_neg_one_sub_le_successProb_floor hn).trans
      (successProb_le_successProb_optimalCutoff _ n),
    successProb_le_exp_neg_one_add _ n⟩

end Secretary

/-! ### The prophet inequality -/

namespace Prophet

open Cslib.Probability.OptimalStopping.Prophet

theorem jointLaw_pure (a : ℝ≥0) : jointLaw [PMF.pure a] = PMF.pure [a] := by
  simp [jointLaw_cons, PMF.pure_bind, PMF.pure_map]

/-- A sure value `1` has median `1`, so Samuel-Cahn's median hypotheses are satisfiable. -/
example : (jointLaw [PMF.pure (1 : ℝ≥0)]).toOuterMeasure {xs | listMax xs < 1} ≤ 1 / 2 ∧
    1 / 2 ≤ (jointLaw [PMF.pure (1 : ℝ≥0)]).toOuterMeasure {xs | listMax xs ≤ 1} := by
  simp [jointLaw_pure, PMF.toOuterMeasure_pure_apply, listMax]

/-- `PMF.toOuterMeasure_apply` with the indicator written as a factor, the form taken by
`tsum_jointLaw_cons_mul`. -/
private theorem toOuterMeasure_eq_tsum {α : Type*} (p : PMF α) (s : Set α) [DecidablePred (· ∈ s)] :
    p.toOuterMeasure s = ∑' x, p x * if x ∈ s then 1 else 0 := by
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ s <;> simp [Set.indicator, hx]

/-- On the tight instance with `k = 1`, `max` is never below `1` and is at most `1` with
probability `1/2`, so `1` is a median of `max` with an atom. -/
theorem median_tightLaws_one :
    (jointLaw (tightLaws 1)).toOuterMeasure {xs | listMax xs < 1} ≤ 1 / 2 ∧
      1 / 2 ≤ (jointLaw (tightLaws 1)).toOuterMeasure {xs | listMax xs ≤ 1} := by
  classical
  constructor <;>
  · rw [toOuterMeasure_eq_tsum, tightLaws_eq, tsum_jointLaw_cons_mul, tsum_pure_mul,
      tsum_jointLaw_cons_mul, tsum_longShot_mul]
    simp only [tsum_jointLaw_nil_mul, Set.mem_ofPred_eq, listMax]
    norm_num

/-- Samuel-Cahn's median theorem applies nondegenerately to the tight instance. -/
example : expectedMax (tightLaws 1) ≤ 2 * expectedReward (thresholdRule 1) (tightLaws 1) ∨
    expectedMax (tightLaws 1) ≤ 2 * expectedReward (strictThresholdRule 1) (tightLaws 1) :=
  expectedMax_le_two_mul_expectedReward_median _ median_tightLaws_one.1 median_tightLaws_one.2

/-- Here `E[max] = 3/2 ≤ 2 · 1`, the median is at or above `E[max]/2`, and the rule accepting
values of at least the median is the one that applies. -/
example : expectedMax (tightLaws 1) ≤ 2 * expectedReward (thresholdRule 1) (tightLaws 1) := by
  refine expectedMax_le_two_mul_expectedReward_thresholdRule_of_le _ median_tightLaws_one.1 ?_
  rw [expectedMax_tightLaws, ← ENNReal.toReal_le_toReal (by finiteness) (by simp)]
  norm_num [ENNReal.toReal_div]

/-- On the tight instance with `k = 1`, `E[max] = 3/2`. -/
theorem expectedMax_tightLaws_one : expectedMax (tightLaws 1) = 3 / 2 := by
  rw [expectedMax_tightLaws]
  norm_num

/-- With `k = 1`, every rule collects less than `3/4` of the prophet's `3/2`. -/
example (stop : List ℝ≥0 → Bool) :
    expectedReward stop (tightLaws 1) < 3 / 4 * expectedMax (tightLaws 1) := by
  refine (expectedReward_tightLaws_le 1 stop).trans_lt ?_
  rw [expectedMax_tightLaws_one, ← ENNReal.toReal_lt_toReal (by simp) (by finiteness)]
  norm_num [ENNReal.toReal_div]

/-- The Kleinberg–Weinberg threshold applies to every instance with finite `E[max]`; on the tight
instance it gives `3/2 ≤ 2 E[reward]`. -/
example : expectedMax (tightLaws 1) ≤
    2 * expectedReward (thresholdRule (expectedMax (tightLaws 1) / 2).toNNReal) (tightLaws 1) :=
  expectedMax_le_two_mul_expectedReward_half _ (by rw [expectedMax_tightLaws_one]; finiteness)

/-- The factor `1/2` cannot be improved to `0.51`. -/
example : ∃ k, ∀ stop, expectedReward stop (tightLaws k) < 51 / 100 * expectedMax (tightLaws k) :=
  exists_tightLaws_lt (by
    rw [← ENNReal.toReal_lt_toReal (by simp) (by finiteness)]
    norm_num [ENNReal.toReal_div])

/-- The backward-induction value of the tight instance is at most `1`, through the
characterization of the value as the best expected reward of any rule. -/
example (k : ℕ) : valueFrom reward (tightLaws k) [] ≤ 1 := by
  rw [valueFrom_eq_iSup]
  exact iSup_le fun stop => expectedReward_tightLaws_le k stop

/-- Taking the sure value `1` attains the bound, so the value of the tight instance is `1`. -/
example (k : ℕ) : valueFrom reward (tightLaws k) [] = 1 := by
  refine le_antisymm ?_ ?_
  · rw [valueFrom_eq_iSup]
    exact iSup_le fun stop => expectedReward_tightLaws_le k stop
  · rw [valueFrom_eq_iSup]
    refine le_iSup_of_le (fun _ => true) (le_of_eq ?_)
    rw [tightLaws_eq, tsum_jointLaw_cons_mul]
    simp only [payoff_cons, ite_true, reward]
    simp [tsum_pmf_mul_const]

end Prophet

/-! ### Tail quantiles and the i.i.d. prophet inequality -/

namespace ProphetIID

open Cslib.Probability.OptimalStopping.Prophet

/-- A sure value `1` has the upper quantile `1` at every level. -/
example (q : ℝ≥0∞) (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ τ : ℝ≥0, (PMF.pure (1 : ℝ≥0)).toOuterMeasure (Set.Ioi τ) ≤ q ∧
      q ≤ (PMF.pure (1 : ℝ≥0)).toOuterMeasure (Set.Ici τ) :=
  Cslib.Probability.PMF.exists_tail_quantile _ hq hq1

/-- Samuel-Cahn's theorem needs no median hypothesis. -/
example : ∃ m : ℝ≥0,
    expectedMax (tightLaws 1) ≤ 2 * expectedReward (thresholdRule m) (tightLaws 1) ∨
      expectedMax (tightLaws 1) ≤ 2 * expectedReward (strictThresholdRule m) (tightLaws 1) :=
  exists_expectedMax_le_two_mul_expectedReward _

/-- `5` with probability `1/5`, and `1` otherwise. -/
noncomputable def fiveOrOne : PMF ℝ≥0 :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin 5)).map fun i => if i.val = 0 then 5 else 1

theorem tsum_fiveOrOne_mul (f : ℝ≥0 → ℝ≥0∞) :
    ∑' x, fiveOrOne x * f x = (f 5 + 4 * f 1) / 5 := by
  rw [fiveOrOne, Cslib.Probability.PMF.tsum_map_mul, tsum_fintype]
  simp only [Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← Finset.mul_sum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, ↓reduceIte, Fin.val_succ, Nat.add_one_ne_zero, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [ENNReal.div_eq_inv_mul]

private theorem inv_five : (5 : ℝ≥0∞)⁻¹ = ((5⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  rw [ENNReal.coe_inv (by norm_num), ENNReal.coe_ofNat]

/-- Every deterministic memoryless (time-invariant) rule on two values `fiveOrOne` collects at
most `9/5`, attained by accepting both values or only `5`. -/
theorem expectedReward_acceptRule_le (a : ℝ≥0 → Bool) :
    expectedReward (acceptRule a) [fiveOrOne, fiveOrOne] ≤ 9 / 5 := by
  rw [expectedReward]
  simp only [tsum_jointLaw_cons_mul, tsum_jointLaw_nil_mul, payoff_cons, payoff_nil, acceptRule,
    reward, tsum_fiveOrOne_mul]
  rcases Bool.eq_false_or_eq_true (a 5) with h5 | h5 <;>
    rcases Bool.eq_false_or_eq_true (a 1) with h1 | h1 <;>
    simp only [h5, h1, Bool.false_eq_true, ↓reduceIte] <;>
    · simp only [div_eq_mul_inv, inv_five]
      norm_cast
      rw [← NNReal.coe_le_coe]
      push_cast
      norm_num

/-- `E[max] = 5 (1 - (4/5)²) + 1 (4/5)² = 61/25`. -/
theorem expectedMax_fiveOrOne : expectedMax [fiveOrOne, fiveOrOne] = 61 / 25 := by
  have h55 : listMax [5, 5] = 5 := by simp [listMax]
  have h51 : listMax [5, 1] = 5 := by simp [listMax]
  have h15 : listMax [1, 5] = 5 := by simp [listMax]
  have h11 : listMax [1, 1] = 1 := by simp [listMax]
  rw [expectedMax]
  simp only [tsum_jointLaw_cons_mul, tsum_jointLaw_nil_mul, tsum_fiveOrOne_mul, h55, h51, h15,
    h11]
  have h25 : (25 : ℝ≥0∞)⁻¹ = ((25⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_inv (by norm_num), ENNReal.coe_ofNat]
  simp only [div_eq_mul_inv, inv_five, h25]
  norm_cast
  rw [← NNReal.coe_inj]
  push_cast
  norm_num

/-- With `n = 2` the constant is `1 - (1 - 1/2)² = 3/4`. -/
theorem one_sub_one_sub_inv_two_sq : (1 - (1 - (2 : ℝ≥0∞)⁻¹) ^ 2) = 3 / 4 := by
  rw [ENNReal.one_sub_inv_two]
  refine ENNReal.sub_eq_of_eq_add (by simp) ?_
  have h2 : (2 : ℝ≥0∞)⁻¹ = ((2⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_inv (by norm_num), ENNReal.coe_ofNat]
  have h4 : (4 : ℝ≥0∞)⁻¹ = ((4⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_inv (by norm_num), ENNReal.coe_ofNat]
  simp only [div_eq_mul_inv, h2, h4]
  norm_cast
  rw [← NNReal.coe_inj]
  push_cast
  norm_num

/-- The coin showing `true` with probability `3/8`. -/
noncomputable def threeEighths : PMF Bool :=
  PMF.ofFintype (fun b => cond b ((3 / 8 : ℝ≥0) : ℝ≥0∞) ((5 / 8 : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool]
    simp only [Bool.cond_true, Bool.cond_false]
    norm_cast
    rw [← NNReal.coe_inj]
    push_cast
    norm_num)

/-- The threshold `1` with the `3/8` coin accepts with probability `1/5 + 3/8 · 4/5 = 1/2`. -/
theorem acceptProb_fiveOrOne :
    (withCoin threeEighths fiveOrOne).toOuterMeasure {o | tieAccept 1 o = true} =
      ((2 : ℕ) : ℝ≥0∞)⁻¹ := by
  have hIoi : fiveOrOne.toOuterMeasure (Set.Ioi 1) = 1 / 5 := by
    rw [PMF.toOuterMeasure_apply]
    have : ∀ x, (Set.Ioi (1 : ℝ≥0)).indicator fiveOrOne x =
        fiveOrOne x * (if 1 < x then 1 else 0) := fun x => by
      by_cases h : (1 : ℝ≥0) < x <;> simp [h]
    simp only [this, tsum_fiveOrOne_mul]
    norm_num
  have h1 : fiveOrOne 1 = 4 / 5 := by
    have : fiveOrOne 1 = ∑' x, fiveOrOne x * (if x = 1 then 1 else 0) := by
      rw [tsum_eq_single 1 fun x hx => by simp [hx]]; simp
    rw [this, tsum_fiveOrOne_mul]
    norm_num
  rw [toOuterMeasure_tieAccept, hIoi, h1]
  simp only [threeEighths, PMF.ofFintype_apply, Bool.cond_true, Nat.cast_ofNat]
  have h2 : (2 : ℝ≥0∞)⁻¹ = ((2⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_inv (by norm_num), ENNReal.coe_ofNat]
  simp only [div_eq_mul_inv, inv_five, h2]
  norm_cast
  rw [← NNReal.coe_inj]
  push_cast
  norm_num

/-- **The tie-breaking coin is needed.** On two i.i.d. values `fiveOrOne`, every deterministic
memoryless rule collects less than `1 - (1 - 1/2)² = 3/4` of `E[max]`, while the threshold `1`
with a `3/8` coin attains it. -/
theorem coin_needed :
    (∀ a : ℝ≥0 → Bool, expectedReward (acceptRule a) [fiveOrOne, fiveOrOne] <
        (1 - (1 - ((2 : ℕ) : ℝ≥0∞)⁻¹) ^ 2) * expectedMax [fiveOrOne, fiveOrOne]) ∧
      (1 - (1 - ((2 : ℕ) : ℝ≥0∞)⁻¹) ^ 2) * expectedMax [fiveOrOne, fiveOrOne] ≤
        tieExpectedReward 1 threeEighths [fiveOrOne, fiveOrOne] := by
  refine ⟨fun a => (expectedReward_acceptRule_le a).trans_lt ?_,
    one_sub_pow_mul_expectedMax_le (n := 2) fiveOrOne 1 threeEighths acceptProb_fiveOrOne⟩
  rw [Nat.cast_ofNat, one_sub_one_sub_inv_two_sq, expectedMax_fiveOrOne]
  have h4 : (4 : ℝ≥0∞)⁻¹ = ((4⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_inv (by norm_num), ENNReal.coe_ofNat]
  have h25 : (25 : ℝ≥0∞)⁻¹ = ((25⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_inv (by norm_num), ENNReal.coe_ofNat]
  simp only [div_eq_mul_inv, inv_five, h4, h25]
  norm_cast
  rw [← NNReal.coe_lt_coe]
  push_cast
  norm_num

/-- Some threshold and coin attain `1 - (1 - 1/n)ⁿ` and `1 - 1/e` for every law and `n`. -/
example (μ : PMF ℝ≥0) (n : ℕ) : ∃ (τ : ℝ≥0) (coin : PMF Bool),
    (1 - (1 - (n : ℝ≥0∞)⁻¹) ^ n) * expectedMax (List.replicate n μ) ≤
      tieExpectedReward τ coin (List.replicate n μ) ∧
    ENNReal.ofReal (1 - Real.exp (-1)) * expectedMax (List.replicate n μ) ≤
      tieExpectedReward τ coin (List.replicate n μ) :=
  exists_one_sub_pow_mul_expectedMax_le μ n

/-- The optimal deterministic gambler on two values `fiveOrOne` collects at least
`3/4 · 61/25 = 183/100`, more than any memoryless rule. -/
example : 3 / 4 * (61 / 25 : ℝ≥0∞) ≤
    expectedReward (optimalRule reward (List.replicate 2 fiveOrOne))
      (List.replicate 2 fiveOrOne) := by
  have h := (one_sub_pow_mul_expectedMax_le_expectedReward_optimalRule fiveOrOne 2).1
  rwa [Nat.cast_ofNat, one_sub_one_sub_inv_two_sq, List.replicate_succ, List.replicate_one,
    expectedMax_fiveOrOne] at h

end ProphetIID

end ComplexityTests.OptimalStopping
