/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Semantics
public import Mathlib.Data.List.OfFn
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event

/-!
# Bounded adaptive probabilistic iteration

`OracleComp.iterate count step initial` repeats a state-dependent program a bounded number of
times. Its invariant rule reasons only about supported transitions. A common finite seed
realizing each reachable step presents the complete loop as a deterministic fold over independent
uniform seeds. State types need not be finite. These are semantic laws; efficiency is separate.

## Main definitions

* `Cslib.OracleComp.iterate`: bounded iteration of a state-dependent program.

## Main results

* `Cslib.OracleComp.iterate_map`: a representation commuting with each step commutes with the loop.
* `Cslib.OracleComp.run_interpret_iterate`: stateful interpretation threads one shared hidden state
  through the loop.
* `Cslib.OracleComp.interpret_iterate`: replacing every call by a program iterates the replaced
  steps.
* `Cslib.OracleComp.iterate_invariant`: possible transitions preserve the final invariant.
* `Cslib.ProbComp.iterate_invariant`: the same for supported transitions of closed programs.
* `Cslib.ProbComp.iterate_failure_le`, `iterate_failure_toReal_le_mul`: local failure bounds
  accumulate additively across adaptive rounds.
* `Cslib.ProbComp.eval_iterate_of_uniform`: exact evaluation from independent saved seeds.

## References

Adapted from Languages/Probabilistic/Iteration.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the typed `PFunctor.FreeM` program interface.
-/

@[expose] public section

namespace Cslib

namespace OracleComp

universe u v w

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {State : Type v}

/-- Repeat a state-dependent program a bounded number of times. -/
def iterate : ℕ → (State → OracleComp spec State) → State → OracleComp spec State
  | 0, _, initial => pure initial
  | count + 1, step, initial => iterate count step initial >>= step

/-- Zero iterations return the initial state. -/
@[simp] theorem iterate_zero (step : State → OracleComp spec State) (initial : State) :
    iterate 0 step initial = pure initial := rfl

/-- `count + 1` iterations run `count` iterations, then one more step. -/
theorem iterate_succ (count : ℕ) (step : State → OracleComp spec State) (initial : State) :
    iterate (count + 1) step initial = iterate count step initial >>= step := rfl

/-- A bounded loop may expose its first transition as well as its last. -/
theorem iterate_succ_bind (count : ℕ) (step : State → OracleComp spec State) (initial : State) :
    iterate (count + 1) step initial = step initial >>= iterate count step := by
  induction count generalizing initial with
  | zero => simp [iterate]
  | succ count ih => rw [iterate_succ, ih, bind_assoc]; rfl

/-- Repeating a step that leaves the initial state unchanged has no effects. -/
theorem iterate_eq_pure (count : ℕ) (step : State → OracleComp spec State) (initial : State)
    (h : step initial = pure initial) : iterate count step initial = pure initial := by
  induction count <;> simp_all [iterate]

/-- A state representation commuting with one step commutes with the complete loop. -/
theorem iterate_map {Other : Type v} (count : ℕ) (step : State → OracleComp spec State)
    (next : Other → OracleComp spec Other) (f : State → Other)
    (hstep : ∀ state, next (f state) = f <$> step state) (initial : State) :
    iterate count next (f initial) = f <$> iterate count step initial := by
  induction count with
  | zero => simp
  | succ count ih => simp only [iterate_succ, ih, bind_map_left, map_bind, hstep]

/-- Replacing every call of a loop by a program over another interface iterates the replaced
steps. -/
theorem interpret_iterate {κ : Type w} {target : OracleSpec.{w, v} κ}
    (handler : (q : ι) → OracleComp target (spec q)) (count : ℕ)
    (step : State → OracleComp spec State) (initial : State) :
    interpret handler (iterate count step initial) =
      iterate count (fun state => interpret handler (step state)) initial := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [iterate_succ, interpret_bind, ih]

/-- Interpreting a loop with a stateful handler is a loop on the joint program and handler state.
The hidden state is retained between iterations, including effects of the last transition. -/
theorem run_interpret_iterate {Hidden : Type v} {κ : Type w}
    {target : OracleSpec.{w, v} κ}
    (handler : (q : ι) → StateT Hidden (OracleComp target) (spec q))
    (count : ℕ) (step : State → OracleComp spec State) (initial : State) (hidden : Hidden) :
    (interpret handler (iterate count step initial)).run hidden =
      iterate count (fun pair : State × Hidden => (interpret handler (step pair.1)).run pair.2)
        (initial, hidden) := by
  induction count with
  | zero => simp
  | succ count ih => simp only [iterate_succ, interpret_bind, StateT.run_bind, ih]

/-- An invariant indexed by the number of completed steps holds for every possible result of a
bounded loop when every possible step preserves it. -/
theorem iterate_invariant {possible : (q : ι) → Set (spec q)}
    {step : State → OracleComp spec State} {count : ℕ} {initial : State}
    (invariant : ℕ → State → Prop) (hbase : invariant 0 initial)
    (hpreserve : ∀ i state, i < count → invariant i state →
      ∀ next ∈ supportWith possible (step state), invariant (i + 1) next) :
    ∀ state ∈ supportWith possible (iterate count step initial), invariant count state := by
  induction count with
  | zero =>
    intro state hstate
    exact (eq_of_mem_supportWith_pure hstate) ▸ hbase
  | succ count ih =>
    intro state hstate
    rw [iterate_succ] at hstate
    obtain ⟨middle, hmiddle, hstate⟩ := mem_supportWith_bind_iff.mp hstate
    exact hpreserve count middle (Nat.lt_succ_self count)
      (ih (fun i state hi => hpreserve i state (Nat.lt_succ_of_lt hi)) middle hmiddle)
      state hstate

end OracleComp

namespace ProbComp

open Probability

variable {State Seed : Type}

/-- Every possible final state satisfies an invariant preserved by every supported transition. -/
theorem iterate_invariant (count : ℕ) (step : State → ProbComp State) (initial : State)
    (invariant : ℕ → State → Prop) (hinit : invariant 0 initial)
    (hpreserve : ∀ i < count, ∀ state, invariant i state →
      ∀ next ∈ (eval (step state)).support, invariant (i + 1) next) :
    ∀ state ∈ (eval (OracleComp.iterate count step initial)).support, invariant count state := by
  rw [support_eval]
  exact OracleComp.iterate_invariant invariant hinit fun i state hi hstate next hnext =>
    hpreserve i hi state hstate next (by rwa [support_eval])

/-- Per-step failures of an invariant accumulate additively across an adaptive loop.
The local bound is needed only at states where the preceding invariant holds. -/
theorem iterate_failure_le (count : ℕ) (step : State → ProbComp State) (initial : State)
    (invariant : ℕ → State → Prop) (hinit : invariant 0 initial) (error : ℕ → ENNReal)
    (hstep : ∀ i < count, ∀ state, invariant i state →
      (eval (step state)).toOuterMeasure {next | ¬ invariant (i + 1) next} ≤ error i) :
    (eval (OracleComp.iterate count step initial)).toOuterMeasure
      {state | ¬ invariant count state} ≤ ∑ i ∈ Finset.range count, error i := by
  classical
  have htrace (i : ℕ) (hi : i ≤ count) :
      (eval (OracleComp.iterate i step initial)).toOuterMeasure
        {state | ¬ invariant i state} ≤ ∑ j ∈ Finset.range i, error j := by
    induction i with
    | zero => simp [eval_pure, PMF.toOuterMeasure_pure_apply, hinit]
    | succ i ih =>
      rw [OracleComp.iterate_succ, eval_bind, Finset.sum_range_succ]
      exact (Probability.PMF.toOuterMeasure_bind_failure_le _ _
        {state | invariant i state} _ (error i)
        (fun state _ hinvariant => hstep i (by lia) state hinvariant)).trans
          (add_le_add (ih (by lia)) le_rfl)
  exact htrace count le_rfl

/-- The real-valued form of the adaptive error rule. -/
theorem iterate_failure_toReal_le (count : ℕ) (step : State → ProbComp State) (initial : State)
    (invariant : ℕ → State → Prop) (hinit : invariant 0 initial) (error : ℕ → ℝ)
    (herror : ∀ i < count, 0 ≤ error i)
    (hstep : ∀ i < count, ∀ state, invariant i state →
      ((eval (step state)).toOuterMeasure {next | ¬ invariant (i + 1) next}).toReal ≤ error i) :
    ((eval (OracleComp.iterate count step initial)).toOuterMeasure
      {state | ¬ invariant count state}).toReal ≤ ∑ i ∈ Finset.range count, error i := by
  have h := iterate_failure_le count step initial invariant hinit
    (fun i => ENNReal.ofReal (error i)) (fun i hi state hinvariant =>
      (ENNReal.le_ofReal_iff_toReal_le (Probability.PMF.toOuterMeasure_ne_top _ _)
        (herror i hi)).mpr (hstep i hi state hinvariant))
  have hnonneg := fun i hi => herror i (Finset.mem_range.mp hi)
  rw [← ENNReal.ofReal_sum_of_nonneg hnonneg] at h
  exact ENNReal.toReal_le_of_le_ofReal (Finset.sum_nonneg hnonneg) h

/-- A uniform per-round error `ε` gives total error at most `count * ε`, including adaptive
rounds and state spaces that are not finite. -/
theorem iterate_failure_toReal_le_mul (count : ℕ) (step : State → ProbComp State)
    (initial : State) (invariant : ℕ → State → Prop) (hinit : invariant 0 initial)
    {error : ℝ} (herror : 0 ≤ error)
    (hstep : ∀ i < count, ∀ state, invariant i state →
      ((eval (step state)).toOuterMeasure {next | ¬ invariant (i + 1) next}).toReal ≤ error) :
    ((eval (OracleComp.iterate count step initial)).toOuterMeasure
      {state | ¬ invariant count state}).toReal ≤ count * error := by
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
    iterate_failure_toReal_le count step initial invariant hinit (fun _ => error)
      (fun _ _ => herror) hstep

/-- Independent uniform seeds realize an adaptive loop when they realize each reachable step.
The invariant allows the realization law to be restricted to reachable states. -/
theorem eval_iterate_of_uniform [Fintype Seed] [Nonempty Seed]
    (count : ℕ) (step : State → ProbComp State) (initial : State) (evaluate : State → Seed → State)
    (invariant : ℕ → State → Prop) (hinit : invariant 0 initial)
    (hpreserve : ∀ i < count, ∀ state, invariant i state →
      ∀ next ∈ (eval (step state)).support, invariant (i + 1) next)
    (hlaw : ∀ i < count, ∀ state, invariant i state →
      eval (step state) = (PMF.uniformOfFintype Seed).map (evaluate state)) :
    eval (OracleComp.iterate count step initial) =
      (PMF.uniformOfFintype (Fin count → Seed)).map
        (fun seeds => (List.ofFn seeds).foldl evaluate initial) := by
  have htrace (i : ℕ) (hi : i ≤ count) : eval (OracleComp.iterate i step initial) =
      (PMF.uniformOfFintype (Fin i → Seed)).map
        (fun seeds => (List.ofFn seeds).foldl evaluate initial) := by
    induction i with
    | zero =>
      rw [OracleComp.iterate_zero, eval_pure]
      simp only [List.ofFn_zero, List.foldl_nil, Function.const_def, PMF.map_const]
    | succ i ih =>
      rw [OracleComp.iterate_succ, eval_bind]
      trans (eval (OracleComp.iterate i step initial)).bind
        (fun state => (PMF.uniformOfFintype Seed).map (evaluate state))
      · apply PMF.bind_congr_on_support
        intro state hstate
        exact hlaw i (by lia) state (iterate_invariant i step initial invariant hinit
          (fun j hj => hpreserve j (by lia)) state hstate)
      · rw [ih (by lia), ← PMF.uniformOfFintype_map_equiv
          ((Equiv.prodComm (Fin i → Seed) Seed).trans (Fin.snocEquiv (fun _ => Seed))),
          PMF.map_comp, ← PMF.uniformOfFintype_prod]
        simp only [PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def,
          Fin.snocEquiv, Equiv.prodComm, Equiv.trans_apply, Equiv.coe_fn_mk,
          List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, Prod.swap,
          List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact htrace count le_rfl

end ProbComp

end Cslib
