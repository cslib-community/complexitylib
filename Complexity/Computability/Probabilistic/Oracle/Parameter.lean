/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.OracleSimulation
public import Complexity.Computability.Probabilistic.Oracle.Substitution
public import Complexity.Computability.Probabilistic.QueryBounds

/-!
# Uniform oracle PPT with a security parameter

The unary security parameter and auxiliary word use the same pair encoding as closed `IsPPT`.
`IsOraclePPT` is a specialization of the existing joint-state contract, with the same named word
channels. No second machine model or interpreter is introduced. A single `Unit` channel suffices
for cryptographic random-function experiments.

## Main definitions

* `Cslib.Probability.IsOraclePPT`: strict uniform oracle PPT with a unary security parameter.

## Main results

* `Cslib.Probability.IsOraclePPT.query_bounds`: polynomial external call and request budgets.
* `Cslib.Probability.IsOraclePPT.run_interpret_preprocess`: efficient closed stateful substitution.
* `Cslib.Probability.IsOraclePPT.run_interpret_preprocess_open`: efficient open stateful
  substitution, whose handler may call an external oracle.
* `Cslib.Probability.IsOraclePPT.run_interpret_preprocess_open'`: the same with plain
  `ComputableInPolyTime` side conditions.

## References

Adapts the security-parameter interface in Computability/Probabilistic/Oracle.lean on the cslib
`crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing word channels.
-/

@[expose] public section

namespace Cslib.Probability

open Turing.MultiTapeTM

/-- One uniform oracle machine on a unary security parameter and an auxiliary word. -/
@[fun_prop]
def IsOraclePPT {Operation β : Type} [DecidableEq Operation] (output : β ↪ List Bool)
    (program : ℕ → List Bool → WordOracleComp Operation β) : Prop :=
  IsOraclePPTOn (encPair encUnary encBits) output (fun input => program input.1 input.2)

variable {Operation β : Type} [DecidableEq Operation] {output : β ↪ List Bool}
  {program program' : ℕ → List Bool → WordOracleComp Operation β}

/-- Expose the existing encoded-input contract. -/
theorem IsOraclePPT.on (h : IsOraclePPT output program) :
    IsOraclePPTOn (encPair encUnary encBits) output (fun input => program input.1 input.2) := h

/-- An encoded certificate for the unary parameter and word is uniform oracle PPT. -/
@[fun_prop]
theorem IsOraclePPTOn.isOraclePPT
    (h : IsOraclePPTOn (encPair encUnary encBits) output (fun input => program input.1 input.2)) :
    IsOraclePPT output program := h

/-- Equality of the joint output/state semantics preserves the parameterized certificate. -/
theorem IsOraclePPT.congr (h : IsOraclePPT output program)
    (heq : ∀ n input (State : Type)
      (oracle : Operation × List Bool → StateT State PMF (List Bool)) state,
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (program n input)).run state =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (program' n input)).run state) : IsOraclePPT output program' :=
  h.on.congr (fun input => heq input.1 input.2)

/-- The same polynomial bounds external calls and request lengths, independently of replies. -/
theorem IsOraclePPT.query_bounds (h : IsOraclePPT output program) :
    ∃ c d : ℕ, ∀ n input, (program n input).IsQueryBounded (c * (n + input.length + 2) ^ d) ∧
      (program n input).QueriesSatisfy fun request =>
        request.2.length ≤ c * (n + input.length + 2) ^ d := by
  obtain ⟨c, d, hbound⟩ := h.on.query_bounds
  refine ⟨c * 2 ^ d, d, fun n input => ?_⟩
  have hsize : (encPair encUnary encBits (n, input)).length + 1 ≤
      2 * (n + input.length + 2) := by
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
    lia
  have hpoly := Nat.mul_le_mul_left c (Nat.pow_le_pow_left hsize d)
  rw [Nat.mul_pow, ← Nat.mul_assoc] at hpoly
  obtain ⟨hcalls, hsize⟩ := hbound (n, input)
  exact ⟨hcalls.mono hpoly, hsize.mono fun _ hlength => hlength.trans hpoly⟩

/-- Supply a closed stateful handler to a parameterized oracle program. The result retains the
final private state, and a local invariant charges reply length and all added encoded storage. -/
theorem IsOraclePPT.run_interpret_preprocess {Caller State : Type}
    {input : Caller ↪ List Bool}
    {operationEncoding : Operation ↪ List Bool}
    {stateEncoding : State ↪ List Bool}
    {handler : Caller → Operation × List Bool → State → ProbComp (List Bool × State)}
    {prepare : Caller → ℕ × List Bool} {initial : Caller → State}
    {resources : Caller → List Bool → ℕ} (hprogram : IsOraclePPT output program)
    (hprepare : ComputableTidilyInPolyTime prepare input (encPair encUnary encBits))
    (hhandler : IsPPTOn
      (encPair input (encPair (encPair operationEncoding encBits) stateEncoding))
      (encPair encBits stateEncoding) (fun pair => handler pair.1 pair.2.1 pair.2.2))
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (invariant : Caller → State → Prop) (hinit : ∀ a, invariant a (initial a))
    (hresources : ComputableTidilyInPolyTime (fun pair => resources pair.1 pair.2)
      (encPair input encBits) encUnary)
    (hpreserve : ∀ a request state, invariant a state →
      ∀ result ∈ (ProbComp.eval (handler a request state)).support,
        invariant a result.2 ∧ result.1.length ≤ resources a request.2 ∧
        (stateEncoding result.2).length ≤ (stateEncoding state).length + resources a request.2) :
    IsPPTOn input (encPair output stateEncoding) (fun a =>
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n)) (handler a))
          (program (prepare a).1 (prepare a).2)).run (initial a)) :=
  hprogram.on.run_interpret_preprocess hprepare hhandler hinitial invariant hinit
    hresources hpreserve

/-- Supply a stateful handler with its own external calls to a parameterized oracle program. The
result retains the handler's final state and every external oracle's state, and a local
invariant charges reply length and all added encoded storage. -/
theorem IsOraclePPT.run_interpret_preprocess_open {External Caller State : Type}
    [DecidableEq External] [Finite External] {input : Caller ↪ List Bool}
    {operationEncoding : Operation ↪ List Bool}
    {stateEncoding : State ↪ List Bool}
    {handler : Caller → Operation × List Bool → State →
      WordOracleComp External (List Bool × State)}
    {prepare : Caller → ℕ × List Bool} {initial : Caller → State}
    {resources : Caller → List Bool → ℕ} (hprogram : IsOraclePPT output program)
    (hprepare : ComputableTidilyInPolyTime prepare input (encPair encUnary encBits))
    (hhandler : IsOraclePPTOn
      (encPair input (encPair (encPair operationEncoding encBits) stateEncoding))
      (encPair encBits stateEncoding) (fun pair => handler pair.1 pair.2.1 pair.2.2))
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (invariant : Caller → State → Prop) (hinit : ∀ a, invariant a (initial a))
    (hresources : ComputableTidilyInPolyTime (fun pair => resources pair.1 pair.2)
      (encPair input encBits) encUnary)
    (hpreserve : ∀ a request state, invariant a state →
      ∀ result ∈ OracleComp.support (handler a request state),
        invariant a result.2 ∧ result.1.length ≤ resources a request.2 ∧
        (stateEncoding result.2).length ≤ (stateEncoding state).length + resources a request.2) :
    IsOraclePPTOn input (encPair output stateEncoding) (fun a =>
      (OracleComp.interpret
        (ProbOracleComp.handler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))) (handler a))
          (program (prepare a).1 (prepare a).2)).run (initial a)) :=
  hprogram.on.run_interpret_preprocess_open hprepare hhandler hinitial invariant hinit
    hresources hpreserve

/-- `Cslib.Probability.IsOraclePPT.run_interpret_preprocess_open` with plain polynomial-time
preparation, initial state and resource allowance. -/
theorem IsOraclePPT.run_interpret_preprocess_open' {External Caller State : Type}
    [DecidableEq External] [Finite External] {input : Caller ↪ List Bool}
    {operationEncoding : Operation ↪ List Bool}
    {stateEncoding : State ↪ List Bool}
    {handler : Caller → Operation × List Bool → State →
      WordOracleComp External (List Bool × State)}
    {prepare : Caller → ℕ × List Bool} {initial : Caller → State}
    {resources : Caller → List Bool → ℕ} (hprogram : IsOraclePPT output program)
    (hprepare : ComputableInPolyTime prepare input (encPair encUnary encBits))
    (hhandler : IsOraclePPTOn
      (encPair input (encPair (encPair operationEncoding encBits) stateEncoding))
      (encPair encBits stateEncoding) (fun pair => handler pair.1 pair.2.1 pair.2.2))
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (invariant : Caller → State → Prop) (hinit : ∀ a, invariant a (initial a))
    (hresources : ComputableInPolyTime (fun pair => resources pair.1 pair.2)
      (encPair input encBits) encUnary)
    (hpreserve : ∀ a request state, invariant a state →
      ∀ result ∈ OracleComp.support (handler a request state),
        invariant a result.2 ∧ result.1.length ≤ resources a request.2 ∧
        (stateEncoding result.2).length ≤ (stateEncoding state).length + resources a request.2) :
    IsOraclePPTOn input (encPair output stateEncoding) (fun a =>
      (OracleComp.interpret
        (ProbOracleComp.handler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))) (handler a))
          (program (prepare a).1 (prepare a).2)).run (initial a)) :=
  hprogram.on.run_interpret_preprocess_open' hprepare hhandler hinitial invariant hinit
    hresources hpreserve

end Cslib.Probability
