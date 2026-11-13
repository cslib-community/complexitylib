/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.NatarajanUpperBound
import CslibFrontier.MachineLearning.PACLearning.GrowthFunction
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The agnostic upper bound for multiclass PAC learning on countable domains

Work in progress for [ShalevShwartzBenDavid2014, Theorem 29.3(1)–(2)]: this file currently
contains the counting step. If `C` N-shatters no finite set of more than `d` points and has `k`
labels, then its Boolean loss class shatters no finite set of more than `6 d (log k + 1)` points
(`card_le_of_setShatters_lossClass_of_natarajan`). A shattered set of `n` labeled points carries
`2 ^ n` loss patterns, while Natarajan's lemma bounds them by `k ^ (2 d) exp (n / 3) 3 ^ d`.

## Main results

- `card_le_of_setShatters_lossClass_of_natarajan`: the shattering bound for the loss class.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

namespace Cslib.MachineLearning.PACLearning

variable {α β : Type*}

/-- **The loss class of a class of bounded Natarajan dimension shatters few points**: if `C`
N-shatters no finite set of more than `d` points and has `k ≥ 1` labels, then its loss class
shatters no finite set of more than `6 d (log k + 1)` labeled points. -/
theorem card_le_of_setShatters_lossClass_of_natarajan [Fintype β] [DecidableEq β] [Nonempty β]
    {C : ConceptClass α β} {d : ℕ} (hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ d)
    {W : Finset (α × β)} (hW : SetShatters (lossClass C) ↑W) :
    (W.card : ℝ) ≤ 6 * d * (Real.log (Fintype.card β) + 1) := by
  set n := W.card
  set k := Fintype.card β
  have hk : 0 < k := Fintype.card_pos
  have hT : (1 : ℝ) ≤ 3 := by norm_num
  have hpow : (2 : ℝ) ^ n ≤ (k : ℝ) ^ (2 * d) * (Real.exp (n / 3) * 3 ^ d) := by
    calc (2 : ℝ) ^ n = (growthFunction (lossClass C) n : ℝ) := by
          rw [growthFunction_eq_two_pow_of_setShatters hW]
          push_cast
          rfl
      _ ≤ natarajanSum n k d := by exact_mod_cast growthFunction_lossClass_le_natarajanSum hC n
      _ ≤ (k : ℝ) ^ (2 * d) * (Real.exp (n / 3) * 3 ^ d) :=
          natarajanSum_le_pow_mul_exp_mul_pow n d hk hT
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  have hlog2 : (2 : ℝ) / 3 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hlog3 : Real.log 3 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h := Real.exp_one_gt_d9
    calc (3 : ℝ) ≤ Real.exp 1 * Real.exp 1 := by nlinarith
      _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg hk1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  push_cast at hlog
  nlinarith [mul_le_mul_of_nonneg_left hlog2.le hn0, mul_le_mul_of_nonneg_left hlog3 hd0]

end Cslib.MachineLearning.PACLearning
