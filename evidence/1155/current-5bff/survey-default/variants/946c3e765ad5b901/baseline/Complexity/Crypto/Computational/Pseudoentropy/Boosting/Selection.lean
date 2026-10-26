/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Pseudoentropy.Boosting.Clipped
public import Complexity.Crypto.Computational.Pseudoentropy.Boosting.Loop
public import Complexity.Languages.Probabilistic.Selection
import Complexity.Probability.PMF.Event
import Complexity.Computability.Probabilistic.Selection
import Complexity.Tactic.PPT

/-!
# Empirical selection of a clipped-vote predictor

Fresh labeled vote samples estimate each dyadic candidate's prediction probability.
`selectSlope` returns a natural numerator for use by `clippedPredict`; the analytic lower-tail
cutoff is never supplied to the program. The error bound combines the lower-tail argument,
slope discretization, and empirical selection with explicit losses.

## Main definitions

* `clippedTrial`, `selectSlope`: validate and select a finite dyadic candidate.
* `Parameters.predictionInverseTolerance`, `.predictionGridBound`: explicit polynomial budgets.

## Main results

* `isPPTOn_selectSlope`: charge the complete grid search and its fresh validation samples.
* `selectSlope_dense_margin`, `State.Successful.selectSlope_advantage`: transfer the loop's
  dense-margin guarantee to the selected predictor.

## References

[Holenstein2005], Lemma 2.4 and Claim 2.15. Empirical selection over a finite slope grid replaces
estimating the analytic cutoff directly.
Adapted from the cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.Boosting

open Probability BitString Turing.MultiTapeTM

/-- Test a candidate on one fresh labeled vote sample. -/
noncomputable def clippedTrial (precision numerator : ℕ) (source : ProbComp (List Bool × Bool)) :
    ProbComp Bool := do
  let sample ← source
  (fun answer => answer == sample.2) <$> clippedPredict precision numerator sample.1

/-- Select a dyadic slope by comparing empirical correctness on fresh labeled samples. -/
noncomputable def selectSlope (confidence inverseTolerance precision : ℕ)
    (source : ProbComp (List Bool × Bool)) : ProbComp ℕ :=
  OracleComp.selectBest (dyadicSize precision + 1) ((confidence + 1) * inverseTolerance ^ 2)
    (fun numerator => clippedTrial precision numerator source)

/-- A certified training sampler and efficient parameters give a strict PPT correctness trial. -/
theorem isPPTOn_clippedTrial {α : Type} {input : α ↪ List Bool}
    {precision numerator : α → ℕ} {source : α → ProbComp (List Bool × Bool)}
    (hprecision : ComputableInPolyTime precision input encUnary)
    (hnumerator : ComputableInPolyTime numerator input encUnary)
    (hsource : IsPPTOn input (encPair encBits encBool) source) :
    IsPPTOn input encBool (fun a => clippedTrial (precision a) (numerator a) (source a)) := by
  unfold clippedTrial
  ppt

attribute [program_certificate] isPPTOn_clippedTrial

/-- Selecting a clipped predictor is uniformly strict PPT, including the complete grid search. -/
theorem isPPTOn_selectSlope {α : Type} {input : α ↪ List Bool}
    {confidence inverseTolerance precision : α → ℕ} {source : α → ProbComp (List Bool × Bool)}
    (hconfidence : ComputableInPolyTime confidence input encUnary)
    (htolerance : ComputableInPolyTime inverseTolerance input encUnary)
    (hprecision : ComputableInPolyTime precision input encUnary)
    (hsource : IsPPTOn input (encPair encBits encBool) source) :
    IsPPTOn input encUnary (fun a =>
      selectSlope (confidence a) (inverseTolerance a) (precision a) (source a)) := by
  have hcount : ComputableInPolyTime (fun a => dyadicSize (precision a) + 1)
      input encUnary := by fun_prop
  have htrials : ComputableInPolyTime
      (fun a => (confidence a + 1) * inverseTolerance a ^ 2) input encUnary := by fun_prop
  have ha := ComputableInPolyTime.fst input encUnary
  have hi := ComputableInPolyTime.snd input encUnary
  have htrial := isPPTOn_clippedTrial (hprecision.comp ha) hi (hsource.preprocess ha)
  exact IsPPTOn.selectBest htrial hcount htrials

attribute [program_certificate] isPPTOn_selectSlope

namespace Parameters

/-- Polynomial inverse tolerance for selecting a predictor, also bounding its final advantage. -/
def predictionInverseTolerance (params : Parameters) : ℕ :=
  128 * params.inverseRate * params.denominator ^ 2

/-- A polynomial slope grid fine enough for the maximum possible vote margin. -/
def predictionGridBound (params : Parameters) : ℕ :=
  params.clock * params.predictionInverseTolerance

/-- The selection tolerance is computed from the encoded parameter record. -/
@[program_certificate]
theorem isPolyTime_predictionInverseTolerance {α : Type} {input : α ↪ List Bool}
    {params : α → Parameters}
    (hparams : ComputableInPolyTime params input encoding) :
    ComputableInPolyTime (fun a => (params a).predictionInverseTolerance) input encUnary := by
  unfold predictionInverseTolerance inverseRate denominator
  fun_prop

/-- The slope grid is polynomial in the encoded parameter record. -/
@[program_certificate]
theorem isPolyTime_predictionGridBound {α : Type} {input : α ↪ List Bool}
    {params : α → Parameters}
    (hparams : ComputableInPolyTime params input encoding) :
    ComputableInPolyTime (fun a => (params a).predictionGridBound) input encUnary := by
  unfold predictionGridBound clock inverseRate denominator
  fun_prop

theorem predictionInverseTolerance_pos (params : Parameters) :
    0 < params.predictionInverseTolerance := by
  exact mul_pos (mul_pos (by decide) params.inverseRate_pos) (pow_pos params.denominator_pos _)

/-- Explicit polynomial precisions leave an inverse-polynomial advantage after both rounding
and empirical selection. The bound deliberately leaves slack for the later reduction. -/
theorem Valid.prediction_error_le {params : Parameters} (hparams : params.Valid) :
    params.delta / 2 - params.gamma * params.delta ^ 3 / 16 +
        params.clock / (2 * dyadicSize params.predictionGridBound) +
        2 / params.predictionInverseTolerance ≤
      params.delta / 2 - 1 / params.predictionInverseTolerance := by
  have hr : (0 : ℝ) < params.inverseRate := by exact_mod_cast params.inverseRate_pos
  have hd : (0 : ℝ) < params.denominator := by exact_mod_cast params.denominator_pos
  have ht : (0 : ℝ) < params.predictionInverseTolerance := by
    exact_mod_cast params.predictionInverseTolerance_pos
  have hc : (0 : ℝ) < params.clock := by
    dsimp only [clock]
    push_cast
    positivity
  have hnum : (1 : ℝ) ≤ params.densityNumerator := by exact_mod_cast hparams.1
  have hgain : 8 * (1 / (params.predictionInverseTolerance : ℝ)) ≤
      params.gamma * params.delta ^ 3 / 16 := by
    have hform : params.gamma * params.delta ^ 3 / 16 =
        (params.densityNumerator : ℝ) ^ 2 /
          (16 * params.inverseRate * (params.denominator : ℝ) ^ 2) := by
      rw [show params.gamma * params.delta ^ 3 / 16 =
        (params.gamma * params.delta) * params.delta ^ 2 / 16 by ring,
        hparams.gamma_mul_delta]
      unfold rate delta
      field_simp
    rw [hform]
    have hbudget : 8 * (1 / (params.predictionInverseTolerance : ℝ)) =
        1 / (16 * params.inverseRate * (params.denominator : ℝ) ^ 2) := by
      unfold predictionInverseTolerance
      push_cast
      field_simp
      norm_num
    rw [hbudget]
    exact div_le_div_of_nonneg_right (one_le_pow₀ hnum) (by positivity)
  have hgrid : (params.clock : ℝ) * params.predictionInverseTolerance ≤
      dyadicSize params.predictionGridBound := by
    exact_mod_cast (lt_dyadicSize params.predictionGridBound).le
  have hround : (params.clock : ℝ) / (2 * dyadicSize params.predictionGridBound) ≤
      (1 / params.predictionInverseTolerance) / 2 := by
    calc
      _ ≤ (params.clock : ℝ) / (2 * (params.clock * params.predictionInverseTolerance)) :=
        div_le_div_of_nonneg_left hc.le (by positivity) (by linarith)
      _ = _ := by field_simp
  have htwo : (2 : ℝ) / params.predictionInverseTolerance =
      2 * (1 / params.predictionInverseTolerance) := by ring
  rw [htwo]
  linarith [one_div_pos.mpr ht]

/-- The same inverse-polynomial advantage also holds on the majority stopping branch. -/
theorem Valid.majority_error_le {params : Parameters} (hparams : params.Valid) :
    7 * params.delta / 16 ≤ params.delta / 2 - 1 / params.predictionInverseTolerance := by
  have hd : (0 : ℝ) < params.denominator := by exact_mod_cast params.denominator_pos
  have ht : (0 : ℝ) < params.predictionInverseTolerance := by
    exact_mod_cast params.predictionInverseTolerance_pos
  have hrone : (1 : ℝ) ≤ params.inverseRate := by
    exact_mod_cast Nat.succ_le_of_lt params.inverseRate_pos
  have hdone : (1 : ℝ) ≤ params.denominator := by
    exact_mod_cast Nat.succ_le_of_lt params.denominator_pos
  have hnum : (1 : ℝ) ≤ params.densityNumerator := by exact_mod_cast hparams.1
  have hproduct := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hrone hdone) hnum
  have hscale : (params.predictionInverseTolerance : ℝ) * params.delta =
      128 * (params.inverseRate * params.denominator * (params.densityNumerator : ℝ)) := by
    unfold predictionInverseTolerance delta
    push_cast
    field_simp
  have hinverse : (1 : ℝ) / params.predictionInverseTolerance ≤ params.delta / 16 := by
    apply (div_le_iff₀ ht).mpr
    nlinarith
  linarith

end Parameters

section Correctness

variable {α : Type} [Fintype α]

/-- The executable trial's success probability is one minus the clipped prediction error. -/
theorem eval_clippedTrial_true (precision numerator : ℕ) (source : ProbComp α)
    (votes : α → List Bool) (truth : α → Bool) :
    (ProbComp.eval (clippedTrial precision numerator
      ((fun x => (votes x, truth x)) <$> source)) true).toReal =
        1 - clippedError (ProbComp.eval source) (fun x => listVoteMargin (votes x) (truth x))
          (numerator / dyadicSize precision) := by
  have hmap (p : PMF Bool) (truth : Bool) :
      (p.map (fun answer => answer == truth)) true = p truth := by
    simp [PMF.map_apply]
  simp only [clippedTrial, ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_map,
    Cslib.Probability.PMF.bind_apply_toReal, Function.comp_def, hmap, eval_clippedPredict_correct]
  simp only [clippedError, mul_sub, mul_one, Finset.sum_sub_distrib,
    Cslib.Probability.PMF.sum_toReal, sub_sub_cancel]

/-- Except with one estimation failure per grid point, the selected predictor is within twice
the tolerance of every dyadic candidate. -/
theorem selectSlope_sound (confidence inverseTolerance precision : ℕ)
    (htolerance : 0 < inverseTolerance) (source : ProbComp α)
    (votes : α → List Bool) (truth : α → Bool) :
    ((ProbComp.eval (selectSlope confidence inverseTolerance precision
      ((fun x => (votes x, truth x)) <$> source))).toOuterMeasure {chosen |
        ¬ (chosen ≤ dyadicSize precision ∧ ∀ numerator ≤ dyadicSize precision,
          clippedError (ProbComp.eval source) (fun x => listVoteMargin (votes x) (truth x))
              (chosen / dyadicSize precision) ≤
            clippedError (ProbComp.eval source) (fun x => listVoteMargin (votes x) (truth x))
              (numerator / dyadicSize precision) + 2 / inverseTolerance)}).toReal ≤
      (dyadicSize precision + 1) * (1 / 2 : ℝ) ^ confidence := by
  have hineq (a b c : ℝ) : (1 - a ≤ 1 - b + c) ↔ b ≤ a + c := by
    constructor <;> intro h <;> linarith
  simpa only [selectSlope, eval_clippedTrial_true, Nat.lt_succ_iff, hineq, Nat.cast_add,
    Nat.cast_one] using ProbComp.selectBest_error_pow (dyadicSize precision + 1)
      confidence inverseTolerance (by positivity) htolerance
      (fun numerator => clippedTrial precision numerator ((fun x => (votes x, truth x)) <$> source))

/-- The empirically selected executable predictor inherits the dense-margin advantage, with
explicit dyadic rounding and sampling losses. -/
theorem selectSlope_dense_margin (confidence inverseTolerance precision : ℕ)
    (htolerance : 0 < inverseTolerance) (source : ProbComp α)
    (votes : α → List Bool) (truth : α → Bool) {δ gap bound : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hgap : 1 ≤ gap)
    (hmargin : ∀ x, |listVoteMargin (votes x) (truth x)| ≤ bound)
    (hdense : ∀ softSet : α → ℝ, (∀ x, softSet x ∈ Set.Icc 0 1) →
      δ ≤ (∑ x, (ProbComp.eval source x).toReal * softSet x) →
      (∑ x, (ProbComp.eval source x).toReal * softSet x) * gap ≤
        ∑ x, (ProbComp.eval source x).toReal * (softSet x * listVoteMargin (votes x) (truth x))) :
    ((ProbComp.eval (selectSlope confidence inverseTolerance precision
      ((fun x => (votes x, truth x)) <$> source))).toOuterMeasure {chosen |
        ¬ clippedError (ProbComp.eval source) (fun x => listVoteMargin (votes x) (truth x))
          (chosen / dyadicSize precision) ≤
            δ / 2 - δ * gap / (2 * bound) + bound / (2 * dyadicSize precision) +
              2 / inverseTolerance}).toReal ≤
      (dyadicSize precision + 1) * (1 / 2 : ℝ) ^ confidence := by
  obtain ⟨numerator, hnum, herror⟩ := exists_dyadic_clippedError_le (ProbComp.eval source)
    (fun x => listVoteMargin (votes x) (truth x)) precision hδ hδone hgap hmargin hdense
  refine le_trans ?_ (selectSlope_sound confidence inverseTolerance precision htolerance
    source votes truth)
  apply ENNReal.toReal_mono (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _)
  apply MeasureTheory.measure_mono
  intro chosen hbad hgood
  apply hbad
  exact (hgood.2 numerator hnum).trans (add_le_add herror le_rfl)

/-- On the dense-margin branch of a successful clocked run, empirical selection produces the
final clipped predictor with the boosting advantage and explicit approximation losses. -/
theorem State.Successful.selectSlope_error {source : ProbComp α} {observe : α → List Bool}
    {truth : α → Bool} {evaluate : List Bool → List Bool → Bool}
    {params : Parameters} {state : State}
    (hstate : State.Successful (ProbComp.eval source)
      (fun code x => evaluate code (observe x)) truth params state)
    (hparams : params.Valid) (hbounded : state.Bounded params.clock params.codeBound)
    (hactive : state.stopped = false) (confidence inverseTolerance precision : ℕ)
    (htolerance : 0 < inverseTolerance) :
    ((ProbComp.eval (selectSlope confidence inverseTolerance precision
      (withVotes evaluate ((fun x => (observe x, truth x)) <$> source) state))).toOuterMeasure
        {chosen | ¬ clippedError (ProbComp.eval source)
          (state.margin (fun code x => evaluate code (observe x)) truth)
          (chosen / dyadicSize precision) ≤
            params.delta / 2 - params.gamma * params.delta ^ 3 / 16 +
              params.clock / (2 * dyadicSize precision) + 2 / inverseTolerance}).toReal ≤
      (dyadicSize precision + 1) * (1 / 2 : ℝ) ^ confidence := by
  have hr : (0 : ℝ) < params.inverseRate := by exact_mod_cast params.inverseRate_pos
  have hd : (0 : ℝ) < params.denominator := by exact_mod_cast params.denominator_pos
  have hratepos := params.rate_pos
  have hrate : params.rate ≤ 1 / 2 := by
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (by exact_mod_cast two_le_dyadicSize params.rateBound)
  have hgap : 1 ≤ (params.clock : ℝ) * (params.gamma * params.delta ^ 2 / 8) :=
    (show 1 ≤ 1 / (2 * params.rate) from
      (le_div_iff₀ (by positivity)).mpr (by linarith)).trans hparams.clock_budget
  have hclock : (params.clock : ℝ) ≠ 0 := by
    dsimp only [Parameters.clock]
    push_cast
    positivity
  have hcancel : params.delta * (params.clock * (params.gamma * params.delta ^ 2 / 8)) /
      (2 * params.clock) = params.gamma * params.delta ^ 3 / 16 := by
    field_simp
    ring
  simp only [State.Successful, hactive, Bool.false_eq_true, ite_false] at hstate
  have h := selectSlope_dense_margin confidence inverseTolerance precision htolerance source
    (fun x => state.predictors.map (fun code => evaluate code (observe x))) truth
    hparams.delta_pos hparams.delta_le_one hgap (fun x => (abs_listVoteMargin_le _ _).trans (by
      simpa only [List.length_map] using
        (show (state.predictors.length : ℝ) ≤ params.clock from by exact_mod_cast hbounded.2.1)))
    hstate
  rw [hcancel] at h
  have hmargin : state.margin (fun code x => evaluate code (observe x)) truth =
      fun x => listVoteMargin (state.predictors.map (fun code => evaluate code (observe x)))
        (truth x) := rfl
  rw [hmargin]
  simpa only [withVotes, Functor.map_map, Function.comp_def, State.votes] using h

/-- With the explicit polynomial grid and tolerance, the final predictor beats `δ / 2` by an
inverse-polynomial amount. Only the supplied confidence controls selection failure. -/
theorem State.Successful.selectSlope_advantage {source : ProbComp α} {observe : α → List Bool}
    {truth : α → Bool} {evaluate : List Bool → List Bool → Bool}
    {params : Parameters} {state : State}
    (hstate : State.Successful (ProbComp.eval source)
      (fun code x => evaluate code (observe x)) truth params state)
    (hparams : params.Valid) (hbounded : state.Bounded params.clock params.codeBound)
    (hactive : state.stopped = false) (confidence : ℕ) :
    ((ProbComp.eval (selectSlope confidence params.predictionInverseTolerance
      params.predictionGridBound
      (withVotes evaluate ((fun x => (observe x, truth x)) <$> source) state))).toOuterMeasure
        {chosen | ¬ clippedError (ProbComp.eval source)
          (state.margin (fun code x => evaluate code (observe x)) truth)
          (chosen / dyadicSize params.predictionGridBound) ≤
            params.delta / 2 - 1 / params.predictionInverseTolerance}).toReal ≤
      (dyadicSize params.predictionGridBound + 1) * (1 / 2 : ℝ) ^ confidence := by
  refine le_trans ?_ (hstate.selectSlope_error hparams hbounded hactive confidence
    params.predictionInverseTolerance params.predictionGridBound
      params.predictionInverseTolerance_pos)
  apply ENNReal.toReal_mono (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _)
  apply MeasureTheory.measure_mono
  intro chosen hbad hgood
  exact hbad (hgood.trans hparams.prediction_error_le)

end Correctness

end Cslib.Crypto.Pseudoentropy.Boosting
