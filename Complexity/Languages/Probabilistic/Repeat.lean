/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Basic
public import Complexity.Languages.Probabilistic.Semantics
public import Complexity.Probability.BitString.List
public import Complexity.Probability.Product
public import Complexity.Probability.IID
import Complexity.Foundations.Data.BitString.Weight
import Mathlib.Algebra.BigOperators.Fin

/-!
# Bounded repetition of probabilistic programs

`OracleComp.replicate` collects the results of an ordinary `List.mapM` traversal in execution
order. Closed runs draw independent samples, even when the output type is infinite. Efficiency
is certified separately in `Computability.Probabilistic.Repeat`.

## Main definitions

* `Cslib.OracleComp.replicate`: collect a bounded number of runs.
* `Cslib.OracleComp.countTrue`, `.testProbabilityLT`: count successes and test rational thresholds.
* `Cslib.OracleComp.repeatAll`: run repeated Boolean trials, accepting when all accept.

## Main results

* `Cslib.OracleComp.replicate_add`, `.replicate_snoc`: split an execution into segments.
* `Cslib.OracleComp.evalWith_repeatAll_true`, `.evalWith_repeatAll_true_toReal`: independent
  repetition multiplies acceptance probabilities under any stateless handler.
* `Cslib.ProbComp.eval_replicate`: finite outputs have the independent product law.
* `Cslib.ProbComp.eval_replicate_iid`: the independent law on arbitrary output types.
* `Cslib.ProbComp.eval_replicate_map`: transport a sampling law through repeated draws.
* `Cslib.ProbComp.eval_replicate_splice`: draw one coordinate first without changing the joint law.
* `Cslib.ProbComp.eval_countTrue`: the success count is a sum of independent indicators.
* `Cslib.ProbComp.countTrue_le`: every supported success count respects the trial budget.
* `Cslib.ProbComp.eval_replicate_of_uniform`: realize the joint law from independent finite seeds.
* `Cslib.ProbComp.eval_replicate_of_uniformList`: collect independent draws from one flat bit list.
* `Cslib.ProbComp.toOuterMeasure_replicate_forall`: all runs pass a test with the power of the
  one-run probability.

## References

Adapted from Languages/Probabilistic/Repeat.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing typed program interface and list
traversal.
-/

@[expose] public section

namespace Cslib

open Probability

namespace OracleComp

universe u v

variable {Query : Type u} {spec : OracleSpec.{u, v} Query} {α β : Type v}

/-- Collect the results of a bounded number of runs in execution order. -/
def replicate (count : ℕ) (program : OracleComp spec α) : OracleComp spec (List α) :=
  (List.replicate count ()).mapM (fun _ => program)

/-- Zero runs return the empty list. -/
@[simp] theorem replicate_zero (program : OracleComp spec α) :
    replicate 0 program = pure [] := rfl

/-- `count + 1` runs make one run, then `count` more, and list its result first. -/
theorem replicate_succ (count : ℕ) (program : OracleComp spec α) :
    replicate (count + 1) program = program >>= fun first =>
      List.cons first <$> replicate count program := by
  simp [replicate, List.replicate_succ, bind_pure_comp]

/-- Split repeated runs into two consecutive segments. -/
theorem replicate_add (first second : ℕ) (program : OracleComp spec α) :
    replicate (first + second) program = (do
      let front ← replicate first program
      let back ← replicate second program
      return front ++ back) := by
  simp only [replicate, List.replicate_add, List.mapM_append]

/-- Split off the last draw of a repeated program. -/
theorem replicate_snoc (count : ℕ) (program : OracleComp spec α) :
    replicate (count + 1) program = (do
      let front ← replicate count program
      (fun last => front ++ [last]) <$> program) := by
  simpa [replicate, bind_pure_comp] using replicate_add count 1 program

/-- Deterministic postprocessing commutes with collecting the draws. -/
theorem replicate_map (count : ℕ) (program : OracleComp spec α) (f : α → β) :
    replicate count (f <$> program) = List.map f <$> replicate count program := by
  induction count with
  | zero => simp
  | succ count ih =>
    simp only [replicate_succ, ih, bind_map_left, map_bind, Functor.map_map, List.map_cons]

variable {spec : OracleSpec.{u, 0} Query}

/-- Count the true results of a bounded number of runs of a Boolean program. -/
def countTrue (count : ℕ) (program : OracleComp spec Bool) : OracleComp spec ℕ :=
  List.count true <$> replicate count program

/-- Compare an empirical acceptance rate with a rational threshold by natural cross-products.
Accuracy theorems require a positive count and denominator; the program is total at zero. -/
def testProbabilityLT (count numerator denominator : ℕ)
    (program : OracleComp spec Bool) : OracleComp spec Bool :=
  (fun successes => decide (successes * denominator < count * numerator)) <$>
    countTrue count program

/-- Run `count` copies of a Boolean program in sequence, returning `false` as soon as one run
returns `false` and `true` when all runs return `true`. -/
def repeatAll (program : OracleComp spec Bool) : ℕ → OracleComp spec Bool
  | 0 => pure true
  | k + 1 => do
    if ← program then repeatAll program k else pure false

/-- Zero repetitions of a Boolean program accept unconditionally. -/
@[simp] theorem repeatAll_zero (program : OracleComp spec Bool) :
    repeatAll program 0 = pure true := rfl

/-- `count + 1` repetitions run the program once, continuing if it accepts and rejecting
otherwise. -/
@[simp] theorem repeatAll_succ (program : OracleComp spec Bool) (count : ℕ) :
    repeatAll program (count + 1) = (do
      if ← program then repeatAll program count else pure false) := rfl

/-- The probability that `count` independent sequential runs all return `true` under a stateless
handler `h` is the `count`-th power of the single-run probability. -/
theorem evalWith_repeatAll_true (h : (q : Query) → PMF (spec q))
    (program : OracleComp spec Bool) (count : ℕ) :
    evalWith h (repeatAll program count) true = evalWith h program true ^ count := by
  induction count with
  | zero =>
    simp only [repeatAll_zero, evalWith_pure, PMF.pure_apply, ite_true, pow_zero]
  | succ count ih =>
    rw [pow_succ', ← ih]
    simp only [repeatAll_succ, evalWith_bind]
    rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
    simp only [ite_true, Bool.false_eq_true, ite_false, evalWith_pure, PMF.pure_apply,
      Bool.true_eq_false, mul_zero, add_zero]

/-- The real probability that `count` independent sequential runs all return `true` under a
stateless handler `h` is the `count`-th power of the single-run real probability. -/
theorem evalWith_repeatAll_true_toReal (h : (q : Query) → PMF (spec q))
    (program : OracleComp spec Bool) (count : ℕ) :
    (evalWith h (repeatAll program count) true).toReal =
      (evalWith h program true).toReal ^ count := by
  rw [evalWith_repeatAll_true, ENNReal.toReal_pow]

end OracleComp

namespace ProbComp

variable {α Seed : Type}

/-- A supported collected result has the prescribed length and supported entries. -/
theorem mem_support_replicate_iff (count : ℕ) (program : ProbComp α) (values : List α) :
    values ∈ (eval (OracleComp.replicate count program)).support ↔
      values.length = count ∧ ∀ value ∈ values, value ∈ (eval program).support := by
  induction count generalizing values with
  | zero => cases values <;> simp
  | succ count ih =>
    cases values with
    | nil => simp [OracleComp.replicate_succ]
    | cons value rest => simp [OracleComp.replicate_succ, ih, and_assoc, and_left_comm]

/-- Repetition preserves equality of closed-program distributions, including infinite outputs. -/
theorem eval_replicate_congr {first second : ProbComp α} (h : eval first = eval second)
    (count : ℕ) : eval (OracleComp.replicate count first) =
      eval (OracleComp.replicate count second) := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [OracleComp.replicate_succ, eval_bind, eval_map, h, ih]

/-- Draw one designated coordinate first, then insert it between independent prefix and suffix
draws. This preserves the complete joint law, including repeated sample values. -/
theorem eval_replicate_splice (source : ProbComp α) (before after : ℕ) :
    eval (do
      let middle ← source
      let front ← OracleComp.replicate before source
      let back ← OracleComp.replicate after source
      pure (front ++ middle :: back)) =
        eval (OracleComp.replicate (before + (after + 1)) source) := by
  rw [OracleComp.replicate_add, OracleComp.replicate_succ]
  simp only [eval_bind, eval_pure, eval_map, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  exact PMF.bind_comm _ _ _

/-- An encoded sampling law lifts to repeated draws without requiring either type to be finite
or the encoding to be injective. The order and multiplicity of all draws are preserved. -/
theorem eval_replicate_map {β : Type} {source : ProbComp α} {encoded : ProbComp β}
    {encode : α → β} (h : eval encoded = (eval source).map encode) (count : ℕ) :
    eval (OracleComp.replicate count encoded) =
      (eval (OracleComp.replicate count source)).map (List.map encode) := by
  rw [← eval_map] at h
  rw [eval_replicate_congr h, OracleComp.replicate_map, eval_map]

/-- Independent repetition on arbitrary output types, including integers and failure options.
Unlike the finite-product specialization, this law needs no finiteness assumption. -/
theorem eval_replicate_iid (count : ℕ) (program : ProbComp α) :
    eval (OracleComp.replicate count program) =
      (Probability.PMF.iid (eval program) count).map List.ofFn := by
  induction count with
  | zero => simp [Probability.PMF.iid]
  | succ count ih =>
    simp only [OracleComp.replicate_succ, eval_bind, eval_map, ih, Probability.PMF.iid,
      PMF.monad_bind_eq_bind, PMF.map_bind, PMF.map_comp, Function.comp_def,
      List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]

/-- Repeated closed runs have the independent product law for any finite output distribution. -/
theorem eval_replicate [Finite α] (count : ℕ) (program : ProbComp α) :
    eval (OracleComp.replicate count program) =
      (Probability.PMF.pi (fun _ : Fin count => eval program)).map List.ofFn := by
  induction count with
  | zero =>
    simp only [OracleComp.replicate_zero, eval_pure, PMF.map, Function.comp_def,
      List.ofFn_zero, PMF.bind_const]
  | succ count ih =>
    rw [OracleComp.replicate_succ, eval_bind]
    simp [eval_map, ih, Probability.PMF.pi_fin_succ, PMF.map_bind, PMF.map_comp,
      Function.comp_def, List.ofFn_succ]

/-- Counting successful repeated trials is the sum of independent Boolean indicators. -/
theorem eval_countTrue (count : ℕ) (program : ProbComp Bool) :
    eval (OracleComp.countTrue count program) =
      (Probability.PMF.pi (fun _ : Fin count => eval program)).map
        (fun bits => ∑ i, (bits i).toNat) := by
  rw [OracleComp.countTrue, eval_map, eval_replicate, PMF.map_comp]
  congr 1
  funext bits
  exact (BitString.count_true_ofFn bits).trans (BitString.weight_eq_sum_toNat bits)

/-- Every supported result is bounded by the number of trials, including zero trials. -/
theorem countTrue_le (count : ℕ) (program : ProbComp Bool) {successes : ℕ}
    (h : successes ∈ (eval (OracleComp.countTrue count program)).support) : successes ≤ count := by
  rw [OracleComp.countTrue, eval_map, PMF.mem_support_map_iff] at h
  obtain ⟨votes, hvotes, rfl⟩ := h
  exact List.count_le_length.trans_eq ((mem_support_replicate_iff _ _ _).mp hvotes).1

/-- Repeated closed runs use independent uniform seeds, including at count zero. The output
type need not be finite. -/
theorem eval_replicate_of_uniform [Fintype Seed] [Nonempty Seed]
    (count : ℕ) (program : ProbComp α) (evaluate : Seed → α)
    (hlaw : eval program = (PMF.uniformOfFintype Seed).map evaluate) :
    eval (OracleComp.replicate count program) =
      (PMF.uniformOfFintype (Fin count → Seed)).map
        (fun seeds => List.ofFn (fun i => evaluate (seeds i))) := by
  have h := eval_replicate_map (source := uniform Seed)
    (by simpa only [eval_uniform] using hlaw) count
  simpa only [eval_replicate, eval_uniform, Probability.PMF.pi_uniformOfFintype,
    PMF.map_comp, Function.comp_def, List.map_ofFn] using h

/-- One flat uniform bit list supplies independent seeds for every repeated run, including
zero repetitions and zero-width seeds. -/
theorem eval_replicate_of_uniformList (count width : ℕ) (program : ProbComp α)
    (evaluate : List Bool → α)
    (hlaw : eval program = (BitString.uniformList width).map evaluate) :
    eval (OracleComp.replicate count program) =
      (BitString.uniformList (count * width)).map
        (fun tape => (BitString.listRows count width tape).map evaluate) := by
  have hseed : eval program = (PMF.uniformOfFintype (BitString width)).map
      (fun bits => evaluate (List.ofFn bits)) := by
    simpa only [BitString.uniformList, PMF.map_comp, Function.comp_def] using hlaw
  rw [eval_replicate_of_uniform count program _ hseed]
  simpa only [PMF.map_comp, Function.comp_def, List.map_ofFn] using
    (congrArg (PMF.map (List.map evaluate)) (BitString.uniformList_listRows count width)).symm

/-- Every one of `n` independent runs satisfies a test with the `n`-th power of the probability
of one run. -/
theorem toOuterMeasure_replicate_forall {β : Type} (program : ProbComp β)
    (f : β → Bool) (n : ℕ) :
    (eval (OracleComp.replicate n program)).toOuterMeasure {l | ∀ b ∈ l, f b = true} =
      (eval program).toOuterMeasure {b | f b = true} ^ n := by
  induction n with
  | zero => simp [PMF.toOuterMeasure_pure_apply]
  | succ n ih =>
    rw [OracleComp.replicate_succ, eval_bind, PMF.toOuterMeasure_bind_apply, pow_succ',
      PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun b => ?_
    rw [eval_map, PMF.toOuterMeasure_map_apply]
    by_cases hb : f b = true
    · have hpre : List.cons b ⁻¹' {l | ∀ c ∈ l, f c = true} = {l | ∀ c ∈ l, f c = true} := by
        ext l
        simp [hb]
      rw [hpre, ih, Set.indicator_of_mem (by exact hb), PMF.toOuterMeasure_apply]
    · have hpre : List.cons b ⁻¹' {l | ∀ c ∈ l, f c = true} = ∅ := by
        ext l
        simp [hb]
      rw [hpre, Set.indicator_of_notMem (by exact hb)]
      simp

/-- The probability that `count` independent sequential runs of a closed probabilistic program
all accept is the `count`-th power of the single-run acceptance probability. -/
theorem eval_repeatAll_true (program : ProbComp Bool) (count : ℕ) :
    eval (OracleComp.repeatAll program count) true = eval program true ^ count :=
  OracleComp.evalWith_repeatAll_true _ program count

/-- The real probability that `count` independent sequential runs of a closed probabilistic program
all accept is the `count`-th power of the single-run real acceptance probability. -/
theorem eval_repeatAll_true_toReal (program : ProbComp Bool) (count : ℕ) :
    (eval (OracleComp.repeatAll program count) true).toReal = (eval program true).toReal ^ count :=
  OracleComp.evalWith_repeatAll_true_toReal _ program count

end ProbComp

end Cslib
