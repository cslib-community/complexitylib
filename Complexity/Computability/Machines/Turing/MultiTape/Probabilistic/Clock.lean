/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Clock
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic

/-!
# Internal clocks for probabilistic machines

The common clock controller preserves the source distribution when coin draws leave private
interpreter state unchanged. The law may be biased; fair-coin semantics is a special case.
This hypothesis is needed because clock bookkeeping consumes extra discarded coin draws.
Query programs may still update arbitrary shared private state.

The budget tape must already be prepared. Its construction and runtime are a separate obligation.

## Main definitions

* `Turing.MultiTapePTM.withClock`: the common clock consumer with Boolean-indexed transitions.

## Main results

* `Turing.MultiTapePTM.run_interpret_runConfigFrom_withClock_add`: a prepared budget reproduces
  the clocked source's tapes and private state and halts, allowing extra time after exhaustion.

## References

The common proof in `MultiTape.Machine.Clock` adapts the cslib `crypto` branch's
MultiTape/Oracle/Clock.lean at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

variable {k : ℕ} {State Oracle Query OracleState : Type} {spec : OracleSpec.{0, 0} Query}
  {input : List Bool} [DecidableEq Oracle]

/-- The common unary-budget controller specialized to Boolean-indexed transitions. -/
abbrev withClock (machine : MultiTapePTM k Bool State Oracle) :
    MultiTapePTM (k + 1) Bool (Clock.Control State) Oracle :=
  MultiTapeMachine.withClock machine

/-- A prepared budget implements the externally clocked run and then halts. Coin draws must be
stateless, whereas the query program may modify arbitrary shared private state. -/
theorem run_interpret_runConfigFrom_withClock_add (machine : MultiTapePTM k Bool State Oracle)
    (coin : OracleComp spec Bool)
    (query : Oracle → List Bool → OracleComp spec (List Bool))
    (oracle : (q : Query) → StateT OracleState PMF (spec q)) (coinLaw : PMF Bool)
    (hcoin : ∀ s, (OracleComp.interpret oracle coin).run s = coinLaw.map (fun bit => (bit, s)))
    (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool) (position : ℤ)
    (budget padding : ℕ) (s : OracleState)
    (hbudget : ∀ i : ℕ, i < budget → tape (position + i) = some true)
    (hstop : tape (position + budget) ≠ some true) :
    (OracleComp.interpret oracle
      (machine.withClock.runConfigFrom coin query (2 * budget + 1 + padding)
        (AuxiliaryTape.config cfg tape position false))).run s =
      ((OracleComp.interpret oracle (machine.runConfigFrom coin query budget cfg)).run s).map
        (fun (final, s') => (AuxiliaryTape.stopped final tape (position + budget), s')) := by
  apply MultiTapeMachine.run_interpret_runConfigFrom_withClock_add machine
    (fun choices => choices <$> coin) (fun _ _ => by rw [Functor.map_map]; rfl)
    query oracle ?_ cfg tape position budget padding s hbudget hstop
  intro α a s
  change (OracleComp.interpret oracle ((fun _ : Bool => a) <$> coin)).run s = _
  simp only [OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map, hcoin, PMF.map_comp]
  exact PMF.map_const coinLaw (a, s)

end Turing.MultiTapePTM
