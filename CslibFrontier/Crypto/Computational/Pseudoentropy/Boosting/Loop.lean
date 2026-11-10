/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Pseudoentropy.Boosting.Program
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind

/-!
# Correctness of the clocked boosting loop

The potential invariant refers to the predictor descriptions stored by the executable program.
Its active branch records density restoration and accumulated potential decrease. Its stopped
branch records the error of the executable majority predictor. Weighted correlation for the
learner's truncated output remains an explicit hypothesis; implementing the learner and its
security reduction is separate work.

## Main definitions

* `State.GoodPredictor`: weighted correlation of the truncated description actually stored.
* `State.Invariant`, `State.Successful`: potential progress and the final prediction guarantee.

## Main results

* `State.Invariant.shift_add`: one valid shift decision and correlated predictor preserve the
  analytic invariant.
* `round_sound`, `run_invariant`: local test and learner errors accumulate additively.
* `run_sound`: a majority-or-dense-margin guarantee under the learner contract.

## References

[Holenstein2005], Section 2.2, Figure 2, Claims 2.7, 2.10–2.13, 2.16, and Lemma 2.14.
The proved clock replaces the worst-dense-set stopping test. Adapted from the cslib `crypto`
branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.Boosting

open Probability BitString

namespace Parameters

/-- The rational density lies in `(0, 1]`. Invalid parameters still define a terminating program. -/
def Valid (params : Parameters) : Prop :=
  0 < params.densityNumerator ∧ params.densityNumerator ≤ params.denominator

/-- The density represented by the integer parameters. -/
noncomputable def delta (params : Parameters) : ℝ :=
  params.densityNumerator / params.denominator

/-- The slope used by the dyadic weight sampler. -/
noncomputable def rate (params : Parameters) : ℝ := 1 / params.inverseRate

/-- The correlation required of the learner, so that `gamma * delta = rate`. -/
noncomputable def gamma (params : Parameters) : ℝ := params.rate / params.delta

@[simp] theorem denominator_pos (params : Parameters) : 0 < params.denominator :=
  dyadicSize_pos _

@[simp] theorem inverseRate_pos (params : Parameters) : 0 < params.inverseRate :=
  dyadicSize_pos _

theorem rate_pos (params : Parameters) : 0 < params.rate := by
  exact one_div_pos.mpr (by exact_mod_cast params.inverseRate_pos)

theorem Valid.delta_pos {params : Parameters} (h : params.Valid) : 0 < params.delta :=
  div_pos (by exact_mod_cast h.1) (by exact_mod_cast params.denominator_pos)

theorem Valid.delta_le_one {params : Parameters} (h : params.Valid) : params.delta ≤ 1 := by
  apply (div_le_one (by exact_mod_cast params.denominator_pos : (0 : ℝ) < params.denominator)).mpr
  exact_mod_cast h.2

theorem Valid.gamma_pos {params : Parameters} (h : params.Valid) : 0 < params.gamma :=
  div_pos params.rate_pos h.delta_pos

theorem Valid.gamma_mul_delta {params : Parameters} (h : params.Valid) :
    params.gamma * params.delta = params.rate :=
  div_mul_cancel₀ _ h.delta_pos.ne'

theorem Valid.inverse_delta {params : Parameters} (h : params.Valid) :
    1 ≤ params.denominator * params.delta := by
  rw [delta, mul_div_cancel₀ _ (by exact_mod_cast params.denominator_pos.ne' :
    (params.denominator : ℝ) ≠ 0)]
  exact_mod_cast h.1

theorem Valid.inverse_gamma {params : Parameters} (h : params.Valid) :
    1 ≤ params.inverseRate * params.gamma := by
  have hr : (params.inverseRate : ℝ) ≠ 0 := by exact_mod_cast params.inverseRate_pos.ne'
  rw [gamma, ← mul_div_assoc, rate, mul_one_div_cancel hr]
  exact (le_div_iff₀ h.delta_pos).mpr (by simpa using h.delta_le_one)

/-- The executable sampling precision meets the majority guard's tolerance. -/
theorem Valid.majority_precision {params : Parameters} (h : params.Valid) :
    1 / (params.majorityPrecision : ℝ) ≤ params.delta / 32 :=
  majority_precision_of_inverse _ h.inverse_delta

/-- The executable sampling precision meets the density guard's tolerance. -/
theorem Valid.shift_precision {params : Parameters} (h : params.Valid) :
    1 / (params.shiftPrecision : ℝ) ≤ params.delta * params.rate / 32 := by
  have hd : (0 : ℝ) < params.denominator := by exact_mod_cast params.denominator_pos
  have hr : (0 : ℝ) < params.inverseRate := by exact_mod_cast params.inverseRate_pos
  apply (div_le_iff₀ (by
    unfold shiftPrecision
    push_cast
    positivity : (0 : ℝ) < params.shiftPrecision)).mpr
  have heq : params.delta * params.rate / 32 * params.shiftPrecision =
      (params.densityNumerator : ℝ) := by
    unfold delta rate shiftPrecision
    push_cast
    field_simp
  rw [heq]
  exact_mod_cast h.1

/-- The integer clock pays for the initial potential, including equality at the boundary. -/
theorem Valid.clock_budget {params : Parameters} (h : params.Valid) :
    1 / (2 * params.rate) ≤ params.clock * (params.gamma * params.delta ^ 2 / 8) := by
  have hclock := clock_sufficient params.inverseRate params.denominator
    h.inverse_gamma h.inverse_delta
  rw [← h.gamma_mul_delta]
  apply (div_le_iff₀ (mul_pos (by norm_num) (mul_pos h.gamma_pos h.delta_pos))).mpr
  change 4 ≤ (params.clock : ℝ) * params.gamma ^ 2 * params.delta ^ 3 at hclock
  nlinarith

end Parameters

namespace State

variable {α : Type*}

/-- The signed margin of the stored descriptions on a labeled source point. -/
def margin (state : State) (predict : List Bool → α → Bool) (truth : α → Bool)
    (x : α) : ℝ :=
  listVoteMargin (state.predictors.map (fun code => predict code x)) (truth x)

@[simp] theorem margin_initial (predict : List Bool → α → Bool) (truth : α → Bool) (x : α) :
    initial.margin predict truth x = 0 := by simp [margin, initial]

@[simp] theorem margin_shift (state : State) (yes : Bool) (predict : List Bool → α → Bool)
    (truth : α → Bool) (x : α) :
    (state.shift yes).margin predict truth x = state.margin predict truth x := rfl

@[simp] theorem margin_add (state : State) (bound : ℕ) (code : List Bool)
    (predict : List Bool → α → Bool) (truth : α → Bool) (x : α) :
    (state.add bound code).margin predict truth x =
      state.margin predict truth x + signedVote (predict (code.take bound) x) (truth x) :=
  listVoteMargin_cons _ _ _

variable [Fintype α] (source : PMF α) (predict : List Bool → α → Bool) (truth : α → Bool)
  (params : Parameters)

/-- The learner's obligation is weighted correlation of the description actually stored. -/
def GoodPredictor (state : State) (code : List Bool) : Prop :=
  params.gamma * density source params.rate
      (fun x => state.margin predict truth x - state.threshold) ≤
    ∑ x, (source x).toReal * (weight params.rate (state.margin predict truth x - state.threshold) *
      signedVote (predict (code.take params.codeBound) x) (truth x))

/-- A good state either has small majority error or records all progress so far.
The extra unit of shift in the density clause allows the next round to restore density. -/
def Invariant (rounds : ℕ) (state : State) : Prop :=
  if state.stopped then
    (source.toOuterMeasure {x |
      listStrictMajority (state.predictors.map (fun code => predict code x)) ≠ truth x}).toReal ≤
        7 * params.delta / 16
  else
    params.delta ≤ density source params.rate
      (fun x => state.margin predict truth x - state.threshold - 1) ∧
    averagePotential source params.rate (fun x => state.margin predict truth x - state.threshold) ≤
      1 / (2 * params.rate) + params.delta * state.threshold -
        rounds * (params.gamma * params.delta ^ 2 / 8)

/-- Before any predictors, the density is full and the potential equals its initial budget. -/
theorem invariant_initial (hparams : params.Valid) :
    Invariant source predict truth params 0 initial := by
  simp only [Invariant, show initial.stopped = false from rfl, Bool.false_eq_true, ite_false,
    margin_initial, show initial.threshold = 0 from rfl, Nat.cast_zero, mul_zero, zero_mul,
    sub_zero, add_zero]
  refine ⟨?_, by simp⟩
  have hdensity := density_antitone source params.rate_pos.le
    (margin := fun _ => 0) (margin' := fun _ => -1) (by intro; norm_num)
  exact hparams.delta_le_one.trans (by simpa using hdensity)

/-- A valid stopping decision establishes the stopped branch for every subsequent round. -/
theorem invariant_stop (rounds : ℕ) (state : State)
    (herror : (source.toOuterMeasure {x | listStrictMajority
      (state.predictors.map (fun code => predict code x)) ≠ truth x}).toReal ≤
        7 * params.delta / 16) :
    Invariant source predict truth params rounds {state with stopped := true} := herror

/-- One valid shift decision and one correlated predictor maintain the analytic invariant.
All margins here are computed from the program's stored descriptions. -/
theorem Invariant.shift_add {rounds : ℕ} {state : State}
    (hstate : Invariant source predict truth params rounds state)
    (hparams : params.Valid) (hactive : state.stopped = false) (yes : Bool) (code : List Bool)
    (hguard : if yes then density source params.rate
      (fun x => state.margin predict truth x - state.threshold) ≤
        params.delta * (1 + params.rate / 16)
      else params.delta ≤ density source params.rate
        (fun x => state.margin predict truth x - state.threshold))
    (hbelow : 3 * params.delta / 8 ≤
      (source.toOuterMeasure {x | state.margin predict truth x ≤ 0}).toReal)
    (hcorrelation : GoodPredictor source predict truth params (state.shift yes) code) :
    Invariant source predict truth params (rounds + 1)
      ((state.shift yes).add params.codeBound code) := by
  have hinvariant := hstate
  simp only [Invariant, hactive, Bool.false_eq_true, ite_false] at hinvariant
  obtain ⟨hrestore, hpotential⟩ := hinvariant
  let before := fun x => state.margin predict truth x - state.threshold
  let vote := fun x => signedVote (predict (code.take params.codeBound) x) (truth x)
  have hshift (x : α) : (state.shift yes).margin predict truth x - (state.shift yes).threshold =
      before x - if yes then 1 else 0 := by
    rw [margin_shift]
    change state.margin predict truth x - ((state.threshold + if yes then 1 else 0 : ℕ) : ℝ) = _
    cases yes <;> simp [before, sub_sub]
  have hnext (x : α) :
      ((state.shift yes).add params.codeBound code).margin predict truth x -
        ((state.shift yes).add params.codeBound code).threshold =
      before x - (if yes then 1 else 0) + vote x := by
    rw [margin_add]
    change (state.shift yes).margin predict truth x + vote x - (state.shift yes).threshold = _
    linarith [hshift x]
  have hdensity : params.delta ≤ density source params.rate
      (fun x => before x - if yes then 1 else 0) := by
    cases yes
    · simpa only [Bool.false_eq_true, ite_false, sub_zero] using hguard
    · simpa only [ite_true] using hrestore
  have hmass : 3 * params.delta / 8 ≤ (source.toOuterMeasure {x | before x ≤ 0}).toReal := by
    refine hbelow.trans (ENNReal.toReal_mono (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _)
      (MeasureTheory.measure_mono ?_))
    intro x hx
    change state.margin predict truth x ≤ 0 at hx
    change state.margin predict truth x - (state.threshold : ℝ) ≤ 0
    linarith [Nat.cast_nonneg (α := ℝ) state.threshold]
  have hstep := step_progress source hparams.gamma_pos hparams.delta_pos hparams.delta_le_one
    before vote (fun _ => by simp [vote]) yes
    (by intro hy; subst yes; simpa only [ite_true, hparams.gamma_mul_delta] using hguard)
    (fun _ => hmass) (by simpa only [hparams.gamma_mul_delta] using hdensity)
    (by simpa only [GoodPredictor, hshift, hparams.gamma_mul_delta] using hcorrelation)
  rw [hparams.gamma_mul_delta] at hstep
  have hrestored := hdensity.trans (density_vote_shift_ge source params.rate_pos.le
    (fun x => before x - if yes then 1 else 0) vote
      (fun x => (abs_le.mp (by simp [vote] : |vote x| ≤ 1)).2))
  have hactiveNext : ((state.shift yes).add params.codeBound code).stopped = false := hactive
  simp only [Invariant, hactiveNext, Bool.false_eq_true, ite_false]
  constructor
  · simpa only [hnext] using hrestored
  · have hnextPotential := (show averagePotential source params.rate
        (fun x => ((state.shift yes).add params.codeBound code).margin predict truth x -
          ((state.shift yes).add params.codeBound code).threshold) ≤
        averagePotential source params.rate before + (if yes then params.delta else 0) -
          params.gamma * params.delta ^ 2 / 8 from by simpa only [hnext] using hstep)
    have hthreshold : (((state.shift yes).add params.codeBound code).threshold : ℝ) =
        state.threshold + if yes then 1 else 0 := by cases yes <;> simp [shift, add]
    refine hnextPotential.trans ?_
    rw [hthreshold]
    dsimp only [before]
    push_cast
    cases yes <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> linarith

/-- At the clock, the program has either a good majority predictor or a collection with large
average signed margin on every dense soft set. The latter is the input to the clipped-vote step. -/
def Successful (state : State) : Prop :=
  if state.stopped then
    (source.toOuterMeasure {x |
      listStrictMajority (state.predictors.map (fun code => predict code x)) ≠ truth x}).toReal ≤
        7 * params.delta / 16
  else ∀ softSet : α → ℝ, (∀ x, softSet x ∈ Set.Icc 0 1) →
    params.delta ≤ ∑ x, (source x).toReal * softSet x →
      (∑ x, (source x).toReal * softSet x) *
        (params.clock * (params.gamma * params.delta ^ 2 / 8)) ≤
      ∑ x, (source x).toReal * (softSet x * state.margin predict truth x)

/-- The same invariant that follows the program proves its clock-boundary guarantee. -/
theorem Invariant.successful {state : State}
    (hstate : Invariant source predict truth params params.clock state)
    (hparams : params.Valid) : Successful source predict truth params state := by
  unfold Successful Invariant at *
  split_ifs at hstate ⊢ with hstop
  · exact hstate
  · intro softSet hsoftSet hdensity
    exact dense_margin_of_budget source params.rate_pos (Nat.cast_nonneg state.threshold)
      (state.margin predict truth) softSet hsoftSet hdensity hparams.clock_budget hstate.2

end State

section Correctness

variable {α : Type} [Fintype α]
  (source : ProbComp α) (observe : α → List Bool) (truth : α → Bool)
  (evaluate : List Bool → List Bool → Bool) (learn : State → ProbComp (List Bool))
  (params : Parameters)

/-- A sampled round preserves the potential invariant except for its two test errors and
the learner's stated error. The learner need only succeed when the shifted measure is dense. -/
theorem round_sound (hparams : params.Valid) {error : ℝ} (herror : 0 ≤ error)
    {rounds : ℕ} {state : State}
    (hstate : State.Invariant (ProbComp.eval source)
      (fun code x => evaluate code (observe x)) truth params rounds state)
    (hlearn : ∀ yes : Bool,
      params.delta ≤ density (ProbComp.eval source) params.rate
        (fun x => (state.shift yes).margin (fun code x => evaluate code (observe x)) truth x -
          (state.shift yes).threshold) →
      ((ProbComp.eval (learn (state.shift yes))).toOuterMeasure {code | ¬ State.GoodPredictor
        (ProbComp.eval source) (fun code x => evaluate code (observe x)) truth params
        (state.shift yes) code}).toReal ≤ error) :
    ((ProbComp.eval (round evaluate
      ((fun x => (observe x, truth x)) <$> source) learn params state)).toOuterMeasure
      {next | ¬ State.Invariant (ProbComp.eval source)
        (fun code x => evaluate code (observe x)) truth params (rounds + 1) next}).toReal ≤
      2 * (1 / 2 : ℝ) ^ params.confidence + error := by
  classical
  let predict := fun code x => evaluate code (observe x)
  let votes := fun x => state.votes evaluate (observe x)
  let stopGuard := fun stop : Bool => if stop then
    ((ProbComp.eval source).toOuterMeasure {x | listStrictMajority (votes x) ≠ truth x}).toReal ≤
      7 * params.delta / 16
    else 3 * params.delta / 8 ≤ ((ProbComp.eval source).toOuterMeasure
      {x | state.margin predict truth x ≤ 0}).toReal
  let shiftGuard := fun yes : Bool => if yes then
    density (ProbComp.eval source) params.rate
      (fun x => state.margin predict truth x - state.threshold) ≤
        params.delta * (1 + params.rate / 16)
    else params.delta ≤ density (ProbComp.eval source) params.rate
      (fun x => state.margin predict truth x - state.threshold)
  have hstop := testMajority_source_sound source votes truth params.confidence
    params.majorityPrecision params.densityNumerator params.denominator
    (by have := params.denominator_pos; unfold Parameters.majorityPrecision; positivity)
    params.denominator_pos hparams.majority_precision
  have hshift := testShift_weights_sound source votes truth params.confidence
    params.shiftPrecision params.densityNumerator params.denominator params.rateBound 1
    state.threshold
    (by
      have := params.denominator_pos
      have := params.inverseRate_pos
      unfold Parameters.shiftPrecision
      positivity)
    params.denominator_pos (by
      simpa only [Parameters.delta, Parameters.rate, Parameters.inverseRate, Nat.cast_one]
        using hparams.shift_precision)
  by_cases hactive : state.stopped = true
  · have hnext : State.Invariant (ProbComp.eval source) predict truth params
        (rounds + 1) state := by
      simpa only [State.Invariant, hactive, ite_true] using hstate
    dsimp only [predict] at hnext
    simp only [round, hactive, ite_true, ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply,
      Set.mem_ofPred_eq, hnext, not_true_eq_false, ite_false, ENNReal.toReal_zero]
    positivity
  · have hflag : state.stopped = false := by cases hs : state.stopped <;> simp_all
    simp only [round, hflag, Bool.false_eq_true, ite_false, withVotes, Functor.map_map,
      bind_map_left, ProbComp.eval_bind]
    refine (PMF.toOuterMeasure_bind_failure_toReal_le _ _ {stop | stopGuard stop} _
      (error := (1 / 2 : ℝ) ^ params.confidence + error) (by positivity) ?_).trans ?_
    · intro stop _ hgoodStop
      cases stop
      · simp only [Bool.false_eq_true, ite_false, ProbComp.eval_bind]
        refine (PMF.toOuterMeasure_bind_failure_toReal_le _ _ {yes | shiftGuard yes} _
          herror ?_).trans ?_
        · intro yes _ hgoodShift
          have hdensity : params.delta ≤ density (ProbComp.eval source) params.rate
              (fun x => (state.shift yes).margin predict truth x -
                (state.shift yes).threshold) := by
            simp only [State.margin_shift]
            cases yes
            · exact hgoodShift
            · have hrestore := hstate
              simp only [State.Invariant, hflag, Bool.false_eq_true, ite_false] at hrestore
              simpa only [State.shift, ite_true, Nat.cast_add, Nat.cast_one,
                sub_add_eq_sub_sub, predict] using hrestore.1
          have hlearner := hlearn yes hdensity
          simp only [ProbComp.eval_pure]
          change (((ProbComp.eval (learn (state.shift yes))).map
            ((state.shift yes).add params.codeBound)).toOuterMeasure
            {next | ¬ State.Invariant (ProbComp.eval source) predict truth params
              (rounds + 1) next}).toReal ≤ error
          rw [PMF.toOuterMeasure_map_apply]
          refine (ENNReal.toReal_mono (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _)
            (MeasureTheory.measure_mono ?_)).trans hlearner
          intro code hbad hgood
          exact hbad (State.Invariant.shift_add _ _ _ _ hstate hparams hflag yes code
            hgoodShift hgoodStop hgood)
        · have hshift' : ((ProbComp.eval (testShift params.confidence params.shiftPrecision
              params.densityNumerator params.denominator 1 params.inverseRate do
                let x ← source
                sampleWeight params.rateBound 1 state.threshold (votes x) (truth x))).toOuterMeasure
                {yes | ¬ shiftGuard yes}).toReal ≤ (1 / 2 : ℝ) ^ params.confidence := by
            simpa only [Nat.cast_one, shiftGuard, votes, predict, State.margin, State.votes,
              Parameters.delta, Parameters.rate, Parameters.inverseRate] using hshift
          exact add_le_add hshift' le_rfl
      · have hnext := State.invariant_stop (ProbComp.eval source) predict truth params
          (rounds + 1) state hgoodStop
        dsimp only [predict] at hnext
        simp only [ite_true, ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply,
          Set.mem_ofPred_eq, hnext, not_true_eq_false, ite_false, ENNReal.toReal_zero]
        positivity
    · have hstop' : ((ProbComp.eval (testMajority params.confidence params.majorityPrecision
          params.densityNumerator params.denominator
          ((fun x => listNonpositiveMargin (votes x) (truth x)) <$> source))).toOuterMeasure
          {stop | ¬ stopGuard stop}).toReal ≤
          (1 / 2 : ℝ) ^ params.confidence := by
        simpa only [stopGuard, votes, predict, State.margin, State.votes, Parameters.delta]
          using hstop
      calc
        _ ≤ (1 / 2 : ℝ) ^ params.confidence + ((1 / 2 : ℝ) ^ params.confidence + error) :=
          add_le_add hstop' le_rfl
        _ = _ := by ring

variable (hparams : params.Valid) {error : ℝ} (herror : 0 ≤ error)
  (hlearn : ∀ state : State,
    params.delta ≤ density (ProbComp.eval source) params.rate
      (fun x => state.margin (fun code x => evaluate code (observe x)) truth x - state.threshold) →
    ((ProbComp.eval (learn state)).toOuterMeasure
      {code | ¬ State.GoodPredictor (ProbComp.eval source)
        (fun code x => evaluate code (observe x)) truth params state code}).toReal ≤ error)

include hparams herror hlearn

/-- Adaptive choices incur only the sum of the local errors, with no independence assumption
between rounds. Stopped states keep their majority guarantee for the remaining clock ticks. -/
theorem run_invariant :
    ((ProbComp.eval (run evaluate
      ((fun x => (observe x, truth x)) <$> source) learn params)).toOuterMeasure
      {state | ¬ State.Invariant (ProbComp.eval source)
        (fun code x => evaluate code (observe x)) truth params params.clock state}).toReal ≤
      params.clock * (2 * (1 / 2 : ℝ) ^ params.confidence + error) := by
  exact ProbComp.iterate_failure_toReal_le_mul params.clock
    (round evaluate ((fun x => (observe x, truth x)) <$> source) learn params) State.initial
    (State.Invariant (ProbComp.eval source) (fun code x => evaluate code (observe x)) truth params)
    (State.invariant_initial _ _ _ _ hparams) (by positivity)
    (fun _ _ _ hstate => round_sound source observe truth evaluate learn params hparams herror
      hstate (fun yes => hlearn _))

/-- The executable loop produces the majority-or-dense-margin guarantee, except with its
explicit total error. The learner contract remains a hypothesis. Combining this with a
certified learner and the final clipped-vote predictor is a separate development. -/
theorem run_sound :
    ((ProbComp.eval (run evaluate
      ((fun x => (observe x, truth x)) <$> source) learn params)).toOuterMeasure
      {state | ¬ State.Successful (ProbComp.eval source)
        (fun code x => evaluate code (observe x)) truth params state}).toReal ≤
      params.clock * (2 * (1 / 2 : ℝ) ^ params.confidence + error) := by
  refine (ENNReal.toReal_mono (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _)
    (MeasureTheory.measure_mono ?_)).trans
      (run_invariant source observe truth evaluate learn params hparams herror hlearn)
  intro state hbad hgood
  exact hbad (State.Invariant.successful _ _ _ _ hgood hparams)

end Correctness

end Cslib.Crypto.Pseudoentropy.Boosting
