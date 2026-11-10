/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Sequential
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic

/-!
# Sequencing fair-coin machines

Sampling a coin commutes with mapping the selected action. Thus the common machine sequencing
theorem applies directly, without an additional probabilistic compiler or interpreter.
The coin program is explicit: the result also applies to stateful, nonuniform coin sources.

## Main definitions

* `Turing.MultiTapePTM.seq`: the common compiler specialized to Boolean-indexed transitions.

## Main results

* `Turing.MultiTapePTM.run_interpret_runConfigFrom_seq`: two halting bounds add while preserving
  the whole joint distribution of configuration and private interpreter state.

## References

The common proof in `MultiTape.Machine.Sequential` adapts the cslib `crypto` branch's
MultiTape/Oracle/Sequential.lean at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine MultiTapeMachine.Sequential

variable {k : ℕ} {Symbol State₀ State₁ Oracle Query OracleState : Type}
  {spec : OracleSpec.{0, 0} Query} {input : List Symbol} [DecidableEq Oracle]

/-- The common sequential compiler specialized to Boolean-indexed transitions. -/
abbrev seq (first : MultiTapePTM k Symbol State₀ Oracle)
    (second : MultiTapePTM k Symbol State₁ Oracle) :
    MultiTapePTM k Symbol (State₀ ⊕ State₁) Oracle :=
  MultiTapeMachine.seq first second

/-- Sequencing retains every tape and private state, even for random stopping times.
Both phases must actually halt within their bounds; clock exhaustion alone is insufficient. -/
theorem run_interpret_runConfigFrom_seq
    (first : MultiTapePTM k Symbol State₀ Oracle) (second : MultiTapePTM k Symbol State₁ Oracle)
    (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (oracle : (q : Query) → StateT OracleState PMF (spec q))
    (cfg : Config k Symbol State₀ Oracle input) (firstTime secondTime : ℕ) (s : OracleState)
    (hfirst : ∀ result ∈
      ((OracleComp.interpret oracle (first.runConfigFrom coin query firstTime cfg)).run s).support,
      result.1.tapes.state = none)
    (hsecond : ∀ result ∈
      ((OracleComp.interpret oracle (first.runConfigFrom coin query firstTime cfg)).run s).support,
      ∀ final ∈ ((OracleComp.interpret oracle
        (second.runConfigFrom coin query secondTime (start second result.1))).run result.2).support,
        final.1.tapes.state = none) :
    (OracleComp.interpret oracle ((first.seq second).runConfigFrom coin query
      (firstTime + secondTime) (left second cfg))).run s =
      ((OracleComp.interpret oracle (first.runConfigFrom coin query firstTime cfg)).run s).bind
        (fun result => ((OracleComp.interpret oracle
          (second.runConfigFrom coin query secondTime (start second result.1))).run result.2).map
          (fun (final, s') => (right final, s'))) := by
  exact MultiTapeMachine.run_interpret_runConfigFrom_seq first second
    (fun choices => choices <$> coin) (fun _ _ => by rw [Functor.map_map]; rfl)
    query oracle cfg firstTime secondTime s hfirst hsecond

end Turing.MultiTapePTM
