/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Iteration

/-!
# Probabilistic loops as chains of distributions

A bounded loop `OracleComp.iterate count step initial` that is run with a probabilistic stateful
handler, or evaluated as a closed program, has the law of the `count`-step chain
`Nat.iterate (fun dist => dist.bind next) count (PMF.pure start)`. In this form, two loops can be
compared one step at a time with `Probability.PMF.map_iterate_bind_of_invariant` and
`Probability.PMF.iterate_bind_comm_of_invariant`.

## Main results

* `Cslib.OracleComp.run_interpret_iterate_pmf`: a loop run with a probabilistic stateful handler is
  the chain on the joint program and handler state.
* `Cslib.ProbComp.eval_iterate`: a closed loop evaluates to the chain of its step laws.
* `Cslib.ProbComp.eval_iterate_congr`: steps with the same law give loops with the same law.
-/

public section

namespace Cslib

namespace OracleComp

universe u v

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {State : Type v}

/-- Running a loop with a probabilistic stateful handler gives the `count`-step chain of
distributions on the joint program and handler state. -/
theorem run_interpret_iterate_pmf {Hidden : Type v}
    (handler : (q : ι) → StateT Hidden PMF (spec q))
    (count : ℕ) (step : State → OracleComp spec State) (initial : State) (hidden : Hidden) :
    (interpret handler (iterate count step initial)).run hidden =
      Nat.iterate (fun dist => dist.bind fun pair : State × Hidden =>
        (interpret handler (step pair.1)).run pair.2) count (PMF.pure (initial, hidden)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [iterate_succ, interpret_bind, StateT.run_bind, ih, Function.iterate_succ_apply']
    rfl

end OracleComp

namespace ProbComp

variable {State : Type}

/-- A closed loop evaluates to the `count`-step chain of its step laws. -/
theorem eval_iterate (count : ℕ) (step : State → ProbComp State) (initial : State) :
    eval (OracleComp.iterate count step initial) =
      Nat.iterate (fun dist => dist.bind fun state => eval (step state)) count
        (PMF.pure initial) := by
  induction count with
  | zero => rfl
  | succ count ih => rw [OracleComp.iterate_succ, eval_bind, ih, Function.iterate_succ_apply']

/-- Steps with the same law give loops with the same law. -/
theorem eval_iterate_congr {step step' : State → ProbComp State}
    (h : ∀ state, eval (step state) = eval (step' state)) (count : ℕ) (initial : State) :
    eval (OracleComp.iterate count step initial) =
      eval (OracleComp.iterate count step' initial) := by
  simp only [eval_iterate, h]

end ProbComp

end Cslib
