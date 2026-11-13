/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Languages.Probabilistic.Oracle.RunState
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Efficient stateful oracle runs

An oracle-PPT word program run against an efficient stateful oracle is PPT, with the final oracle
state returned. The statements use `ProbOracleComp.runState`: the run is
`(program.runState (oracle caller)).run (initial caller)`. They are
`IsOraclePPTOn.run_interpret_preprocess` and `IsOraclePPT.run_interpret_preprocess'` stated on
`runState`, with the same resource allowance: a local invariant of the oracle state bounds each
reply and the encoded state added by each call. Each is derived from the corresponding theorem,
whose conclusion is definitionally the same run. State a run as `(P.runState O).run s` and certify
it here; `run_interpret_preprocess` remains for runs still written with `OracleComp.interpret` and
`OracleComp.sumHandler`.

## Main results

* `Cslib.Probability.IsOraclePPTOn.isPPTOn_runState`: running an oracle-PPT program against an
  efficient stateful oracle is PPT, with polynomial-time preparation, initial state and allowance.
* `Cslib.Probability.IsOraclePPT.isPPTOn_runState`: the same for a program parameterized by the
  unary security parameter and a word.
-/

public section

namespace Cslib.Probability

open Turing.MultiTapeTM

variable {Operation α β Caller State : Type} [DecidableEq Operation]
  {source : α ↪ List Bool} {input : Caller ↪ List Bool} {output : β ↪ List Bool}
  {operationEncoding : Operation ↪ List Bool} {stateEncoding : State ↪ List Bool}

/-- Running an oracle-PPT program against an efficient stateful oracle is PPT in the caller, with
the final oracle state returned. `prepare` computes the program's input from the caller and
`initial` the oracle's initial state. On every supported call from a state satisfying
`invariant`, the oracle keeps the invariant, and the reply and the encoded state it adds are
bounded by the computed allowance `resources caller request`. -/
theorem IsOraclePPTOn.isPPTOn_runState {program : α → WordOracleComp Operation β}
    {oracle : Caller → Operation × List Bool → StateT State ProbComp (List Bool)}
    {prepare : Caller → α} {initial : Caller → State} {resources : Caller → List Bool → ℕ}
    (hprogram : IsOraclePPTOn source output program)
    (hprepare : ComputableInPolyTime prepare input source)
    (horacle : IsPPTOn (encHandlerCall input operationEncoding stateEncoding)
      (encPair encBits stateEncoding)
      (fun ⟨caller, request, state⟩ => oracle caller request state))
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (invariant : Caller → State → Prop) (hinit : ∀ a, invariant a (initial a))
    (hresources : ComputableInPolyTime (fun pair => resources pair.1 pair.2)
      (encPair input encBits) encUnary)
    (hpreserve : ∀ a request state, invariant a state →
      ∀ result ∈ (ProbComp.eval (oracle a request state)).support,
        invariant a result.2 ∧ result.1.length ≤ resources a request.2 ∧
        (stateEncoding result.2).length ≤ (stateEncoding state).length + resources a request.2) :
    IsPPTOn input (encPair output stateEncoding)
      (fun a => ((program (prepare a)).runState (oracle a)).run (initial a)) :=
  hprogram.run_interpret_preprocess (handler := fun a request => oracle a request) hprepare.tidy
    horacle hinitial.tidy invariant hinit hresources.tidy hpreserve

/-- Running a parameterized oracle-PPT program against an efficient stateful oracle is PPT in the
caller, with the final oracle state returned. `prepare` computes the security parameter and word
from the caller, and `initial` the oracle's initial state, both in polynomial time; the oracle
condition is that of `IsOraclePPTOn.isPPTOn_runState`. -/
theorem IsOraclePPT.isPPTOn_runState {program : ℕ → List Bool → WordOracleComp Operation β}
    {oracle : Caller → Operation × List Bool → StateT State ProbComp (List Bool)}
    {prepare : Caller → ℕ × List Bool} {initial : Caller → State}
    {resources : Caller → List Bool → ℕ} (hprogram : IsOraclePPT output program)
    (hprepare : ComputableInPolyTime prepare input (encPair encUnary encBits))
    (horacle : IsPPTOn (encHandlerCall input operationEncoding stateEncoding)
      (encPair encBits stateEncoding)
      (fun ⟨caller, request, state⟩ => oracle caller request state))
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (invariant : Caller → State → Prop) (hinit : ∀ a, invariant a (initial a))
    (hresources : ComputableInPolyTime (fun pair => resources pair.1 pair.2)
      (encPair input encBits) encUnary)
    (hpreserve : ∀ a request state, invariant a state →
      ∀ result ∈ (ProbComp.eval (oracle a request state)).support,
        invariant a result.2 ∧ result.1.length ≤ resources a request.2 ∧
        (stateEncoding result.2).length ≤ (stateEncoding state).length + resources a request.2) :
    IsPPTOn input (encPair output stateEncoding)
      (fun a => ((program (prepare a).1 (prepare a).2).runState (oracle a)).run (initial a)) :=
  hprogram.run_interpret_preprocess' (handler := fun a request => oracle a request) hprepare
    horacle hinitial invariant hinit hresources hpreserve

end Cslib.Probability
