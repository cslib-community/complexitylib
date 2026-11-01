/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Repeat
public import Complexity.Languages.Probabilistic.Iteration
import Complexity.Probability.PMF.Event
import Complexity.Languages.Probabilistic.Concentration

/-!
# Selecting a candidate by repeated trials

`OracleComp.selectBest count trials test` estimates the acceptance probability of each candidate
below `count` and returns the candidate with the largest success count. It is an ordinary bounded
program. The correctness rule charges one estimation failure per candidate and loses twice the
estimation tolerance relative to the best candidate. No independence between estimates is needed
by the selection argument; each estimate uses the independent trials in `countTrue`.

## Main definitions

* `Cslib.OracleComp.selectUpdate`: update the next index and the running best index and count.
* `Cslib.OracleComp.selectStep`: estimate one candidate and update the running empirical maximum.
* `Cslib.OracleComp.selectBest`: select an index by empirical success count.
* `Cslib.OracleComp.selectFrom`, `.sampleBest`: select from a list or a sampled candidate pool.

## Main results

* `Cslib.ProbComp.selectBest_error_pow`, `.selectFrom_error_pow`: statistical selection bounds.
* `Cslib.ProbComp.sampleBest_error_pow`: combine discovery and validation failures.
* `Cslib.ProbComp.selectStep_bounded`, `.sampleBest_support`: bounds on every execution.

## References

Adapted from the cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
The deviation estimate is the Hoeffding bound from [Hoeffding1963].
-/

@[expose] public section

namespace Cslib

open Probability

namespace OracleComp

universe u

variable {Query : Type u} {spec : OracleSpec.{u, 0} Query}

/-- Update the next index, best index, and best success count, preferring later indices on ties. -/
def selectUpdate : ℕ × ℕ × ℕ → ℕ → ℕ × ℕ × ℕ
  | (next, best, count), successes =>
    (next + 1, if count ≤ successes then (next, successes) else (best, count))

/-- Estimate one candidate and update the running empirical maximum. -/
def selectStep (trials : ℕ) (test : ℕ → OracleComp spec Bool)
    (state : ℕ × ℕ × ℕ) : OracleComp spec (ℕ × ℕ × ℕ) :=
  selectUpdate state <$> countTrue trials (test state.1)

/-- Return an index with the largest observed success count.
When there are no candidates, return zero. -/
def selectBest (count trials : ℕ) (test : ℕ → OracleComp spec Bool) :
    OracleComp spec ℕ :=
  (fun (_, best, _) => best) <$> iterate count (selectStep trials test) (0, 0, 0)

/-- Select an empirically best value from a list, returning the fallback for an empty list. -/
def selectFrom {α : Type} (values : List α) (trials : ℕ)
    (test : α → OracleComp spec Bool) (fallback : α) : OracleComp spec α := do
  let chosen ← selectBest values.length trials (fun i => test (values[i]?.getD fallback))
  return values[chosen]?.getD fallback

/-- Draw a candidate pool and select the candidate with the highest empirical score. -/
def sampleBest {α : Type} (count trials : ℕ) (source : OracleComp spec α)
    (test : α → OracleComp spec Bool) (fallback : α) : OracleComp spec α := do
  let values ← replicate count source
  selectFrom values trials test fallback

end OracleComp

namespace ProbComp

/-- Selection can only return a listed candidate or the supplied fallback. This holds on every
execution, independently of estimation accuracy. -/
theorem selectFrom_support {α : Type} (values : List α) (trials : ℕ)
    (test : α → ProbComp Bool) (fallback : α) {chosen : α}
    (hchosen : chosen ∈ (eval (OracleComp.selectFrom values trials test fallback)).support) :
    chosen = fallback ∨ chosen ∈ values := by
  simp only [OracleComp.selectFrom, bind_pure_comp, eval_map, PMF.mem_support_map_iff] at hchosen
  obtain ⟨i, _, rfl⟩ := hchosen
  cases hvalue : values[i]? with
  | none => simp
  | some value =>
    right
    exact List.mem_of_getElem? hvalue

/-- Empirical selection preserves the support of its candidate sampler, apart from the fixed
fallback. In particular, bounds on descriptions survive every statistical failure. -/
theorem sampleBest_support {α : Type} (count trials : ℕ) (source : ProbComp α)
    (test : α → ProbComp Bool) (fallback : α) {chosen : α}
    (hchosen : chosen ∈ (eval (OracleComp.sampleBest count trials source test fallback)).support) :
    chosen = fallback ∨ chosen ∈ (eval source).support := by
  rw [OracleComp.sampleBest, eval_bind, PMF.mem_support_bind_iff] at hchosen
  obtain ⟨values, hvalues, hchosen⟩ := hchosen
  rcases selectFrom_support values trials test fallback hchosen with hdefault | hmem
  · exact Or.inl hdefault
  · exact Or.inr (((mem_support_replicate_iff count source values).mp hvalues).2 _ hmem)

/-- Candidate selection keeps both indices within the elapsed count and the success count within
the trial budget on every execution, regardless of statistical estimation errors. -/
theorem selectStep_bounded (trials : ℕ) (test : ℕ → ProbComp Bool) (i : ℕ)
    (next best count : ℕ) (hstate : next = i ∧ best ≤ i ∧ count ≤ trials)
    (next' best' count' : ℕ)
    (hnext : (next', best', count') ∈
      (eval (OracleComp.selectStep trials test (next, best, count))).support) :
    next' = i + 1 ∧ best' ≤ i + 1 ∧ count' ≤ trials := by
  rw [OracleComp.selectStep, eval_map, PMF.mem_support_map_iff] at hnext
  obtain ⟨successes, hsuccesses, hupdate⟩ := hnext
  have hbound := countTrue_le trials (test next) hsuccesses
  dsimp only [OracleComp.selectUpdate] at hupdate
  split_ifs at hupdate <;> simp_all <;> lia

private def SelectionInvariant (trials : ℕ) (rate : ℕ → ℝ) (ε : ℝ)
    (i : ℕ) (state : ℕ × ℕ × ℕ) : Prop :=
  state.1 = i ∧ (i = 0 → state.2 = (0, 0)) ∧
    (0 < i → state.2.1 < i ∧ (state.2.2 : ℝ) / trials ≤ rate state.2.1 + ε) ∧
    ∀ j < i, rate j ≤ (state.2.2 : ℝ) / trials + ε

private theorem SelectionInvariant.update {trials i : ℕ} {rate : ℕ → ℝ} {ε : ℝ}
    {state : ℕ × ℕ × ℕ} (hstate : SelectionInvariant trials rate ε i state)
    (successes : ℕ) (haccurate : |(successes : ℝ) / trials - rate i| ≤ ε) :
    SelectionInvariant trials rate ε (i + 1) (OracleComp.selectUpdate state successes) := by
  rcases state with ⟨next, best, count⟩
  obtain ⟨hindex, hzero, hchosen, hall⟩ := hstate
  obtain ⟨hlower, hupper⟩ := abs_le.mp haccurate
  have htrials : (0 : ℝ) ≤ trials := by positivity
  dsimp only [SelectionInvariant, OracleComp.selectUpdate] at hindex hzero hchosen hall ⊢
  split_ifs with hscore
  · have hcompare : (count : ℝ) / trials ≤ successes / trials :=
      div_le_div_of_nonneg_right (by exact_mod_cast hscore) htrials
    refine ⟨by lia, by simp, fun _ => ⟨by lia, ?_⟩, ?_⟩
    · simpa only [hindex] using (show (successes : ℝ) / trials ≤ rate i + ε by linarith)
    · intro j hj
      by_cases hji : j < i
      · have := hall j hji
        dsimp only
        linarith
      · have : j = i := by lia
        subst j
        dsimp only
        linarith
  · have hi : 0 < i := by
      by_contra h
      obtain ⟨rfl, rfl⟩ := hzero (by lia)
      simp at hscore
    have hcompare : (successes : ℝ) / trials ≤ count / trials :=
      div_le_div_of_nonneg_right (by exact_mod_cast (show successes ≤ count by lia)) htrials
    obtain ⟨hchosenIndex, hchosenRate⟩ := hchosen hi
    refine ⟨by lia, by simp, fun _ => ⟨by lia, hchosenRate⟩, ?_⟩
    intro j hj
    by_cases hji : j < i
    · exact hall j hji
    · have : j = i := by lia
      subst j
      linarith

/-- If every empirical probability is accurate except with probability `error`, selection loses
at most twice the tolerance relative to every candidate, except with probability `count * error`.
The returned index is in range on this same event. -/
theorem selectBest_error_le (count trials : ℕ) (hcount : 0 < count)
    (test : ℕ → ProbComp Bool) {ε error : ℝ} (herror : 0 ≤ error)
    (hestimate : ∀ i < count,
      ((eval (OracleComp.countTrue trials (test i))).toOuterMeasure {successes |
        ε ≤ |(successes : ℝ) / trials - (eval (test i) true).toReal|}).toReal ≤ error) :
    ((eval (OracleComp.selectBest count trials test)).toOuterMeasure {chosen |
      ¬ (chosen < count ∧ ∀ i < count,
        (eval (test i) true).toReal ≤ (eval (test chosen) true).toReal + 2 * ε)}).toReal ≤
      count * error := by
  let rate := fun i => (eval (test i) true).toReal
  have hrun := iterate_failure_toReal_le_mul count (OracleComp.selectStep trials test)
    (0, 0, 0) (SelectionInvariant trials rate ε)
    (by simp [SelectionInvariant]) herror (by
      intro i hi state hstate
      rw [OracleComp.selectStep, eval_map, PMF.toOuterMeasure_map_apply]
      rw [hstate.1]
      refine le_trans ?_ (hestimate i hi)
      apply ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
      apply MeasureTheory.measure_mono
      intro successes hbad
      by_contra haccurate
      exact hbad (hstate.update successes (le_of_lt (lt_of_not_ge haccurate))))
  rw [OracleComp.selectBest, eval_map, PMF.toOuterMeasure_map_apply]
  refine le_trans ?_ hrun
  apply ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
  apply MeasureTheory.measure_mono
  rintro ⟨next, best, count⟩ hbad hstate
  obtain ⟨_, _, hchosen, hall⟩ := hstate
  obtain ⟨hindex, hselected⟩ := hchosen hcount
  apply hbad
  refine ⟨hindex, fun i hi => ?_⟩
  have := hall i hi
  dsimp only [rate] at *
  linarith

/-- A polynomial trial budget selects within twice the requested inverse tolerance of the best
candidate, with one exponentially small failure term per candidate. -/
theorem selectBest_error_pow (count confidence inverseTolerance : ℕ) (hcount : 0 < count)
    (htolerance : 0 < inverseTolerance) (test : ℕ → ProbComp Bool) :
    ((eval (OracleComp.selectBest count
      ((confidence + 1) * inverseTolerance ^ 2) test)).toOuterMeasure
      {chosen | ¬ (chosen < count ∧ ∀ i < count,
        (eval (test i) true).toReal ≤
          (eval (test chosen) true).toReal + 2 / inverseTolerance)}).toReal ≤
      count * (1 / 2 : ℝ) ^ confidence := by
  simpa only [mul_one_div] using selectBest_error_le count
    ((confidence + 1) * inverseTolerance ^ 2) hcount test (by positivity)
    (fun i _ => countTrue_average_deviation_pow confidence inverseTolerance htolerance (test i))

/-- A fresh test of the selected candidate fails at most as often as any specified candidate,
up to twice the estimation tolerance and the probability of a selection error. -/
theorem selectBest_test_error_le (count confidence inverseTolerance : ℕ)
    (htolerance : 0 < inverseTolerance) (test : ℕ → ProbComp Bool) (i : ℕ) (hi : i < count) :
    (eval (do
      let chosen ← OracleComp.selectBest count ((confidence + 1) * inverseTolerance ^ 2) test
      test chosen) false).toReal ≤ (eval (test i) false).toReal + 2 / inverseTolerance +
        count * (1 / 2 : ℝ) ^ confidence := by
  have hselect := selectBest_error_pow count confidence inverseTolerance (by lia) htolerance test
  have hfailure := Probability.PMF.toOuterMeasure_bind_failure_toReal_le
    (eval (OracleComp.selectBest count ((confidence + 1) * inverseTolerance ^ 2) test))
    (fun chosen => eval (test chosen))
    {chosen | chosen < count ∧ ∀ j < count,
      (eval (test j) true).toReal ≤ (eval (test chosen) true).toReal + 2 / inverseTolerance}
    {false} (error := (eval (test i) false).toReal + 2 / inverseTolerance)
    (by positivity) (by
      intro chosen _ hgood
      have hchosen := Probability.PMF.toReal_true_add_toReal_false (eval (test chosen))
      have hi' := Probability.PMF.toReal_true_add_toReal_false (eval (test i))
      simp only [PMF.toOuterMeasure_apply_singleton]
      have := hgood.2 i hi
      linarith)
  simp only [Set.compl_ofPred, PMF.toOuterMeasure_apply_singleton] at hfailure
  rw [eval_bind]
  linarith

/-- Empirical selection from a nonempty list loses at most twice the estimation tolerance
relative to every listed candidate, except for one small failure term per candidate. -/
theorem selectFrom_error_pow {α : Type} (values : List α) (hvalues : 0 < values.length)
    (confidence inverseTolerance : ℕ) (htolerance : 0 < inverseTolerance)
    (test : α → ProbComp Bool) (fallback : α) :
    ((eval (OracleComp.selectFrom values
      ((confidence + 1) * inverseTolerance ^ 2) test fallback)).toOuterMeasure
      {chosen | ¬ (chosen ∈ values ∧ ∀ value ∈ values,
        (eval (test value) true).toReal ≤
          (eval (test chosen) true).toReal + 2 / inverseTolerance)}).toReal ≤
      values.length * (1 / 2 : ℝ) ^ confidence := by
  simp only [OracleComp.selectFrom, bind_pure_comp, eval_map, PMF.toOuterMeasure_map_apply]
  refine le_trans ?_ (selectBest_error_pow values.length confidence inverseTolerance hvalues
    htolerance (fun i => test (values[i]?.getD fallback)))
  apply ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
  apply MeasureTheory.measure_mono
  intro chosen hbad hgood
  obtain ⟨hchosen, hbest⟩ := hgood
  apply hbad
  refine ⟨?_, ?_⟩
  · simp only [List.getElem?_eq_getElem hchosen, Option.getD_some]
    exact List.getElem_mem hchosen
  · intro value hmem
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
    simpa only [List.getElem?_eq_getElem hi, Option.getD_some] using hbest i hi

/-- A noticeable chance of drawing a good candidate can be amplified by sampling a pool and
estimating every candidate. The two failure terms pay separately for discovery and selection. -/
theorem sampleBest_error_pow {α : Type} (source : ProbComp α) (test : α → ProbComp Bool)
    (fallback : α) (confidence inverseSuccess inverseTolerance : ℕ)
    (hsuccess : 0 < inverseSuccess) (htolerance : 0 < inverseTolerance) (threshold : ℝ)
    (hgood : (1 : ℝ) / inverseSuccess ≤ ((eval source).toOuterMeasure
      {value | threshold ≤ (eval (test value) true).toReal}).toReal) :
    ((eval (OracleComp.sampleBest ((confidence + 1) * inverseSuccess ^ 2)
      ((confidence + 1) * inverseTolerance ^ 2) source test fallback)).toOuterMeasure
        {chosen | ¬ threshold - 2 / inverseTolerance ≤ (eval (test chosen) true).toReal}).toReal ≤
      (((confidence + 1) * inverseSuccess ^ 2 : ℕ) + 1) * (1 / 2 : ℝ) ^ confidence := by
  let count := (confidence + 1) * inverseSuccess ^ 2
  have hcount : 0 < count := by dsimp only [count]; positivity
  have hdiscover := replicate_failure_pow source
    (fun value => threshold ≤ (eval (test value) true).toReal) confidence inverseSuccess
    hsuccess hgood
  have hselect := Probability.PMF.toOuterMeasure_bind_failure_toReal_le
    (eval (OracleComp.replicate count source))
    (fun values => eval (OracleComp.selectFrom values
      ((confidence + 1) * inverseTolerance ^ 2) test fallback))
    {values | ∃ value ∈ values, threshold ≤ (eval (test value) true).toReal}
    {chosen | ¬ threshold - 2 / inverseTolerance ≤ (eval (test chosen) true).toReal}
    (error := count * (1 / 2 : ℝ) ^ confidence) (by positivity) (by
      intro values hvalues hgood
      have hlength := ((mem_support_replicate_iff count source values).mp hvalues).1
      have h := selectFrom_error_pow values (by lia) confidence inverseTolerance htolerance
        test fallback
      rw [hlength] at h
      refine le_trans ?_ h
      apply ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
      apply MeasureTheory.measure_mono
      intro chosen hbad hchosen
      obtain ⟨value, hmem, hvalue⟩ := hgood
      have := hchosen.2 value hmem
      exact hbad (by linarith))
  simp only [Set.compl_ofPred] at hselect
  change ((eval (OracleComp.sampleBest count _ source test fallback)).toOuterMeasure _).toReal ≤ _
  rw [OracleComp.sampleBest, eval_bind]
  calc
    _ ≤ _ := hselect
    _ ≤ (1 / 2 : ℝ) ^ confidence + count * (1 / 2 : ℝ) ^ confidence := by
      gcongr
    _ = _ := by dsimp only [count]; push_cast; ring

end ProbComp

end Cslib
