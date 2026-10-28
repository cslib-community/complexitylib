/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.Oracle.Parameter
public import Complexity.Languages.Probabilistic.Presample
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Efficient oracle substitution with saved samples

A supplied list replaces fresh draws in a closed external handler. Its local contract covers
every supplied value and the fallback used on short lists. The sample list only shrinks, so no
additional storage invariant is needed. The certificate retains the output, ordinary private
state and unused suffix; only the separate distribution law forgets that suffix.

## Main results

* `Cslib.Probability.IsOraclePPTOn.run_interpret_withSampleList`: arbitrary encoded callers and
  saved values, with all sample consumption and storage charged.
* `Cslib.Probability.IsOraclePPT.run_interpret_withSampleList`: security-parameter specialization.

## References

Adapted from Computability/Probabilistic/Presample.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the common stateful substitution theorem.
-/

@[expose] public section

namespace Cslib.Probability

open Turing.MultiTapeTM

/-- Supply saved samples to a closed external handler. Bounds hold for every supplied value,
including the fallback on an exhausted list. The certificate retains the complete final state. -/
theorem IsOraclePPTOn.run_interpret_withSampleList
    {Operation α β Caller State Value : Type} [DecidableEq Operation]
    {source : α ↪ List Bool} {input : Caller ↪ List Bool} {output : β ↪ List Bool}
    {operationEncoding : Operation ↪ List Bool}
    {stateEncoding : State ↪ List Bool} {valueEncoding : Value ↪ List Bool}
    {program : α → WordOracleComp Operation β}
    {oracle : Caller → Value → Operation × List Bool → State → ProbComp (List Bool × State)}
    {prepare : Caller → α} {initial : Caller → State} {values : Caller → List Value}
    {resources : Caller → List Bool → ℕ} (hprogram : IsOraclePPTOn source output program)
    (fallback : Value) (hprepare : ComputableTidilyInPolyTime prepare input source)
    (horacle : IsPPTOn
      (encPair (encPair input valueEncoding)
        (encPair (encPair operationEncoding encBits) stateEncoding))
      (encPair encBits stateEncoding) (fun pair => oracle pair.1.1 pair.1.2 pair.2.1 pair.2.2))
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (hvalues : ComputableTidilyInPolyTime values input (encList valueEncoding))
    (invariant : Caller → State → Prop) (hinit : ∀ a, invariant a (initial a))
    (hresources : ComputableTidilyInPolyTime (fun pair => resources pair.1 pair.2)
      (encPair input encBits) encUnary)
    (hpreserve : ∀ a value request state, invariant a state →
      ∀ result ∈ (ProbComp.eval (oracle a value request state)).support,
        invariant a result.2 ∧ result.1.length ≤ resources a request.2 ∧
        (stateEncoding result.2).length ≤ (stateEncoding state).length + resources a request.2) :
    IsPPTOn input (encPair output (encPair stateEncoding (encList valueEncoding))) (fun a =>
      (OracleComp.interpret (ProbOracleComp.handler
        (fun n => StateT.lift (ProbComp.unifFin n))
        (OracleComp.withSampleList fallback (oracle a))) (program (prepare a))).run
          (initial a, values a)) := by
  let storage := encPair stateEncoding (encList valueEncoding)
  have hwrapped : IsPPTOn
      (encPair input (encPair (encPair operationEncoding encBits) storage))
      (encPair encBits storage) (fun pair =>
        OracleComp.withSampleList fallback (oracle pair.1) pair.2.1 pair.2.2) := by
    unfold OracleComp.withSampleList
    apply IsPPTOn.map_with (left := encPair encBits stateEncoding)
    · exact horacle.preprocess
        (prepare := fun pair : Caller × ((Operation × List Bool) × (State × List Value)) =>
          ((pair.1, pair.2.2.2.headD fallback), (pair.2.1, pair.2.2.1)))
        (by dsimp only [storage]; fun_prop)
    · dsimp only [storage]; fun_prop
  refine hprogram.run_interpret_preprocess (operationEncoding := operationEncoding)
    hprepare hwrapped (hinitial.prod hvalues)
    (fun a state => invariant a state.1) hinit
    (resources := fun a query => 2 * resources a query) (by fun_prop) ?_
  intro a request state hstate result hresult
  simp only [OracleComp.withSampleList, ProbComp.eval_map, PMF.mem_support_map_iff] at hresult
  obtain ⟨⟨answer, next⟩, hresult, rfl⟩ := hresult
  obtain ⟨hnext, hreply, hgrowth⟩ :=
    hpreserve a (state.2.headD fallback) request state.1 hstate (answer, next) hresult
  have htail := SizedListEncoding.length_drop_le (encA := valueEncoding)
    (encL := encList valueEncoding) state.2 1
  simp only [List.drop_one] at htail
  refine ⟨hnext, by dsimp at hreply ⊢; lia, ?_⟩
  simp only [length_encPair]
  dsimp at hgrowth ⊢
  lia

/-- Security-parameter specialization of saved-sample substitution, retaining the complete
ordinary state and unused suffix under the same local resource contract. -/
theorem IsOraclePPT.run_interpret_withSampleList
    {Operation β Caller State Value : Type} [DecidableEq Operation]
    {input : Caller ↪ List Bool} {output : β ↪ List Bool}
    {operationEncoding : Operation ↪ List Bool}
    {stateEncoding : State ↪ List Bool} {valueEncoding : Value ↪ List Bool}
    {program : ℕ → List Bool → WordOracleComp Operation β}
    {oracle : Caller → Value → Operation × List Bool → State → ProbComp (List Bool × State)}
    {prepare : Caller → ℕ × List Bool} {initial : Caller → State} {values : Caller → List Value}
    {resources : Caller → List Bool → ℕ} (hprogram : IsOraclePPT output program)
    (fallback : Value)
    (hprepare : ComputableTidilyInPolyTime prepare input (encPair encUnary encBits))
    (horacle : IsPPTOn
      (encPair (encPair input valueEncoding)
        (encPair (encPair operationEncoding encBits) stateEncoding))
      (encPair encBits stateEncoding) (fun pair => oracle pair.1.1 pair.1.2 pair.2.1 pair.2.2))
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (hvalues : ComputableTidilyInPolyTime values input (encList valueEncoding))
    (invariant : Caller → State → Prop) (hinit : ∀ a, invariant a (initial a))
    (hresources : ComputableTidilyInPolyTime (fun pair => resources pair.1 pair.2)
      (encPair input encBits) encUnary)
    (hpreserve : ∀ a value request state, invariant a state →
      ∀ result ∈ (ProbComp.eval (oracle a value request state)).support,
        invariant a result.2 ∧ result.1.length ≤ resources a request.2 ∧
        (stateEncoding result.2).length ≤ (stateEncoding state).length + resources a request.2) :
    IsPPTOn input (encPair output (encPair stateEncoding (encList valueEncoding))) (fun a =>
      (OracleComp.interpret (ProbOracleComp.handler
        (fun n => StateT.lift (ProbComp.unifFin n))
        (OracleComp.withSampleList fallback (oracle a)))
          (program (prepare a).1 (prepare a).2)).run (initial a, values a)) :=
  hprogram.on.run_interpret_withSampleList fallback hprepare horacle hinitial hvalues
    invariant hinit hresources hpreserve

end Cslib.Probability
