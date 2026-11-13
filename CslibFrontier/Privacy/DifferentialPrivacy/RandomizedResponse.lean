/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Privacy.DifferentialPrivacy.Hamming
public import CslibFrontier.Languages.Probabilistic.Vector
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Randomized response

Randomized response [DworkRoth2014, §3.2] is a survey protocol for a yes/no question. The
respondent flips a coin. On tails they answer truthfully; on heads they flip a second coin and
answer "Yes" on heads and "No" on tails. `randomizedResponse truth` is this protocol as a
`ProbComp Bool` program over fair coins, with `true` for "Yes" and for a truthful answer. The
privacy statements apply `DifferentiallyPrivate` to its output law
`ProbComp.eval (randomizedResponse truth)`: the protocol is a finite program, and only its
semantics is a `PMF`.

The answer agrees with the truth with probability `3/4` (`eval_randomizedResponse_apply`), so
randomized response is `(ln 3, 0)`-differentially private for a single respondent
(`differentiallyPrivate_randomizedResponse`) [DworkRoth2014, Claim 3.5], and `ln 3` is optimal
(`differentiallyPrivate_randomizedResponse_iff`).

`randomizedResponseSurvey x` lets each of `n` respondents answer independently. It is
`(ln 3, 0)`-private for Hamming adjacency (`differentiallyPrivate_randomizedResponseSurvey`). The
expected number of "Yes" answers is `n / 4 + (number of true "Yes") / 2`
(`sum_eval_randomizedResponseSurvey_mul_card`), so twice the fraction of "Yes" answers minus
`1/2` is an unbiased estimator of the true fraction
(`sum_eval_randomizedResponseSurvey_mul_estimator`) [DworkRoth2014, §2.3].

## Main definitions

* `Cslib.Privacy.randomizedResponse`: one respondent's randomized response.
* `Cslib.Privacy.randomizedResponseSurvey`: `n` independent respondents.

## Main results

* `Cslib.Privacy.differentiallyPrivate_randomizedResponse`,
  `Cslib.Privacy.differentiallyPrivate_randomizedResponse_iff`: exactly `(ln 3, 0)`-private.
* `Cslib.Privacy.differentiallyPrivate_randomizedResponseSurvey`: the survey is
  `(ln 3, 0)`-private for Hamming adjacency.
* `Cslib.Privacy.sum_eval_randomizedResponseSurvey_mul_estimator`: the unbiased estimator.

## References

* [DworkRoth2014]
-/

open scoped ENNReal

public section

namespace Cslib.Privacy

/-- Randomized response [DworkRoth2014, §3.2]: flip a coin; on tails (`truthful = true`) answer
truthfully, and on heads answer with a second fair coin. -/
noncomputable def randomizedResponse (truth : Bool) : ProbComp Bool := do
  let truthful ← ProbComp.uniform Bool
  if truthful then return truth else ProbComp.uniform Bool

/-- Randomized response agrees with the truth with probability `3/4`. -/
theorem eval_randomizedResponse_apply (truth answer : Bool) :
    ProbComp.eval (randomizedResponse truth) answer = if answer = truth then 3 / 4 else 1 / 4 := by
  simp only [randomizedResponse, ProbComp.eval_bind, ProbComp.eval_uniform, PMF.bind_apply,
    tsum_fintype, Fintype.sum_bool, Probability.PMF.uniformOfFintype_apply, Fintype.card_bool,
    ite_true, Bool.false_eq_true, ite_false, ProbComp.eval_pure, PMF.pure_apply]
  have h1 : (2 : ℝ≥0∞)⁻¹ * 2⁻¹ = 4⁻¹ := by
    rw [← ENNReal.mul_inv (by simp) (by simp)]
    norm_num
  have h3 : (2 : ℝ≥0∞)⁻¹ + 4⁻¹ = 3 / 4 := by
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    norm_num
  cases truth <;> cases answer <;> simp [h1, h3]

/-- Randomized response is `(ln 3, 0)`-differentially private for a single respondent, whose
datum may change arbitrarily [DworkRoth2014, Claim 3.5]. -/
theorem differentiallyPrivate_randomizedResponse :
    DifferentiallyPrivate (fun _ _ => True) (fun truth => ProbComp.eval (randomizedResponse truth))
      (Real.log 3) 0 := by
  refine DifferentiallyPrivate.of_apply_le fun x y _ r => ?_
  rw [Real.exp_log (by norm_num), ENNReal.ofReal_ofNat, eval_randomizedResponse_apply,
    eval_randomizedResponse_apply]
  rw [← ENNReal.toReal_le_toReal (by split_ifs <;> finiteness) (by split_ifs <;> finiteness)]
  split_ifs <;> simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_one] <;> norm_num

/-- `ln 3` is optimal: randomized response is `(ε, 0)`-differentially private exactly when
`ln 3 ≤ ε`. -/
theorem differentiallyPrivate_randomizedResponse_iff {ε : ℝ} :
    DifferentiallyPrivate (fun _ _ => True) (fun truth => ProbComp.eval (randomizedResponse truth))
      ε 0 ↔ Real.log 3 ≤ ε := by
  refine ⟨fun h => ?_, fun h => differentiallyPrivate_randomizedResponse.mono h le_rfl⟩
  have key := DifferentiallyPrivate.iff_apply_le.mp h (x := true) (y := false) trivial true
  rw [eval_randomizedResponse_apply, eval_randomizedResponse_apply] at key
  simp only [ite_true, Bool.true_eq_false, ite_false] at key
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] at key
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one] at key
  rw [Real.log_le_iff_le_exp (by norm_num)]
  linarith

/-- The survey in which each of `n` respondents independently applies randomized response to
their own answer. -/
noncomputable def randomizedResponseSurvey {n : ℕ} (x : Fin n → Bool) : ProbComp (Fin n → Bool) :=
  OracleComp.pi fun i => randomizedResponse (x i)

/-- The survey's answers are independent randomized responses. -/
theorem eval_randomizedResponseSurvey {n : ℕ} (x : Fin n → Bool) :
    ProbComp.eval (randomizedResponseSurvey x) =
      Probability.PMF.pi fun i => ProbComp.eval (randomizedResponse (x i)) :=
  ProbComp.eval_pi _

/-- The randomized-response survey is `(ln 3, 0)`-differentially private for Hamming
adjacency. -/
theorem differentiallyPrivate_randomizedResponseSurvey (n : ℕ) :
    DifferentiallyPrivate HammingAdjacent
      (fun x : Fin n → Bool => ProbComp.eval (randomizedResponseSurvey x)) (Real.log 3) 0 := by
  simp only [eval_randomizedResponseSurvey]
  exact DifferentiallyPrivate.pi (M := fun _ truth => ProbComp.eval (randomizedResponse truth))
    (Real.log_nonneg (by norm_num)) fun _ => differentiallyPrivate_randomizedResponse

/-- The expected number of "Yes" answers is `n / 4 + (number of true "Yes") / 2`
[DworkRoth2014, §2.3]. -/
theorem sum_eval_randomizedResponseSurvey_mul_card {n : ℕ} (x : Fin n → Bool) :
    ∑ answers, (ProbComp.eval (randomizedResponseSurvey x) answers).toReal *
        (Finset.univ.filter fun i => answers i = true).card =
      n / 4 + (Finset.univ.filter fun i => x i = true).card / 2 := by
  have hcard (a : Fin n → Bool) : ((Finset.univ.filter fun i => a i = true).card : ℝ) =
      ∑ i, if a i = true then 1 else 0 := by
    rw [Finset.card_filter]; push_cast; rfl
  simp only [hcard, eval_randomizedResponseSurvey]
  rw [Probability.PMF.sum_pi_mul_sum (fun i => ProbComp.eval (randomizedResponse (x i)))
    (fun _ b => if b = true then (1 : ℝ) else 0)]
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false, mul_one, mul_zero, add_zero,
    eval_randomizedResponse_apply]
  rw [show (n : ℝ) / 4 + (∑ i, if x i = true then (1 : ℝ) else 0) / 2 =
      ∑ i, (1 / 4 + (if x i = true then (1 : ℝ) else 0) / 2) by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.sum_div]
    ring]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases x i <;> norm_num

/-- The estimator `2 · (fraction of "Yes" answers) - 1/2` is unbiased for the fraction of
respondents whose true answer is "Yes" [DworkRoth2014, §2.3]. -/
theorem sum_eval_randomizedResponseSurvey_mul_estimator {n : ℕ} (hn : n ≠ 0) (x : Fin n → Bool) :
    ∑ answers, (ProbComp.eval (randomizedResponseSurvey x) answers).toReal *
        (2 * ((Finset.univ.filter fun i => answers i = true).card / n) - 1 / 2) =
      (Finset.univ.filter fun i => x i = true).card / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  set μ := ProbComp.eval (randomizedResponseSurvey x)
  calc ∑ answers, (μ answers).toReal *
        (2 * ((Finset.univ.filter fun i => answers i = true).card / n) - 1 / 2)
      = 2 / n * ∑ answers, (μ answers).toReal *
            (Finset.univ.filter fun i => answers i = true).card -
          1 / 2 * ∑ answers, (μ answers).toReal := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun _ _ => ?_
        ring
    _ = (Finset.univ.filter fun i => x i = true).card / n := by
        rw [sum_eval_randomizedResponseSurvey_mul_card, Probability.PMF.sum_toReal]
        field_simp
        ring

end Cslib.Privacy
