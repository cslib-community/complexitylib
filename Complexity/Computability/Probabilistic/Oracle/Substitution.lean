/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.Realization.OpenOracleSimulation
import Complexity.Languages.Probabilistic.Oracle.Simulation
import Complexity.Languages.Probabilistic.Simulation
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Open stateful oracle substitution

A certified oracle program can be interpreted against a stateful handler that is itself a
certified oracle program: the handler may draw private coins and call an arbitrary external
stateful oracle, whose replies may be arbitrarily long. The result is again strict oracle PPT,
returning the original result and the handler's final state, and it preserves the complete joint
law of the result, the handler's state and the external oracle's state.

A local invariant and an efficiently computed additive allowance bound each reply given to the
program and the encoded private storage added per call. Individually efficient calls alone do
not suffice: repeatedly doubling the handler's state is efficient per call but not overall.
Closed substitution (`Cslib.Probability.IsOraclePPTOn.run_interpret_preprocess`) is the special
case of a sampled closed handler without external channels.

## Main definitions

* `Cslib.Probability.encHandlerCall`: the encoded input of a stateful handler.

## Main results

* `Cslib.Probability.IsOraclePPTOn.run_interpret_preprocess_open`: open substitution with
  captured caller data, a local state invariant and an efficiently computed resource allowance.
* `Cslib.Probability.IsOraclePPTOn.run_interpret_preprocess_open'`: the same with plain
  `ComputableInPolyTime` side conditions.
* `Cslib.Probability.IsOraclePPTOn.run_interpret_preprocess_open_of_polyBounded`: the same with
  an allowance that is only polynomially bounded, not computed.
* `Cslib.Probability.IsOraclePPTOn.interpret_preprocess_open'`: stateless substitution with
  a polynomial-time reply allowance, retaining the arbitrary external oracle's state.
* `Cslib.Probability.IsOraclePPTOn.interpret_bitQueries`: replace each deterministic word query
  by a polynomial-time transformed request, keeping only one answer bit.

## References

Extends Computability/Probabilistic/OracleSimulation.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` from closed to open handlers.
-/

@[expose] public section

namespace Cslib.Probability

open Turing.MultiTapeTM

/-- The input of a stateful oracle handler: the caller's input, then the request (an operation
and its word), then the handler's state. Each pair frames its first part, so this is
`encPair input (encPair (encPair operationEncoding encBits) stateEncoding)`. -/
abbrev encHandlerCall {Caller Operation State : Type} (input : Caller ↪ List Bool)
    (operationEncoding : Operation ↪ List Bool) (stateEncoding : State ↪ List Bool) :
    Caller × (Operation × List Bool) × State ↪ List Bool :=
  encPair input (encPair (encPair operationEncoding encBits) stateEncoding)

/-- Substitute a stateful handler with its own external calls into an oracle program. The
substituted program is strict oracle PPT and preserves the joint law of the result, the
handler's final state and every external oracle's state. The allowance bounds each reply and the
added encoded state, and is polynomially bounded in the encoded caller and request; it need not
be computable. One invariant must hold for every possible handler result under every external
oracle. External replies to the handler need no length bound. -/
theorem IsOraclePPTOn.run_interpret_preprocess_open_of_polyBounded
    {Operation External α β Caller State : Type} [DecidableEq Operation]
    [DecidableEq External] [Finite External]
    {source : α ↪ List Bool} {input : Caller ↪ List Bool} {output : β ↪ List Bool}
    {operationEncoding : Operation ↪ List Bool} {stateEncoding : State ↪ List Bool}
    {program : α → WordOracleComp Operation β}
    {handler : Caller → Operation × List Bool → State →
      WordOracleComp External (List Bool × State)}
    {prepare : Caller → α} {initial : Caller → State} {resources : Caller → List Bool → ℕ}
    (hprogram : IsOraclePPTOn source output program)
    (hprepare : ComputableInPolyTime prepare input source)
    (hhandler : IsOraclePPTOn (encHandlerCall input operationEncoding stateEncoding)
      (encPair encBits stateEncoding)
      (fun ⟨caller, request, state⟩ => handler caller request state))
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (invariant : Caller → State → Prop) (hinit : ∀ a, invariant a (initial a))
    (hresources : PolyBounded (fun pair => (encPair input encBits pair).length)
      (fun pair => resources pair.1 pair.2))
    (hpreserve : ∀ a request state, invariant a state →
      ∀ result ∈ OracleComp.support (handler a request state),
        invariant a result.2 ∧ result.1.length ≤ resources a request.2 ∧
        (stateEncoding result.2).length ≤ (stateEncoding state).length + resources a request.2) :
    IsOraclePPTOn input (encPair output stateEncoding) (fun a =>
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))) (handler a))
          (program (prepare a))).run (initial a)) := by
  obtain ⟨resourceCoeff, resourceDegree, hbound⟩ := hresources.exists_le
  let allowance := fun size => resourceCoeff * (2 * size + 2) ^ resourceDegree
  have hallowance : PolynomiallyBounded allowance := by unfold allowance; fun_prop
  have hbound' (a : Caller) (query : List Bool) :
      resources a query ≤ allowance ((input a).length + query.length) := by
    have h := hbound (a, query)
    simp only [length_encPair, encBits_apply] at h
    exact h.trans (Nat.mul_le_mul_left resourceCoeff
      (Nat.pow_le_pow_left (by lia) resourceDegree))
  obtain ⟨hfiniteOp, k, Control, hfinite, machine, c, d, hrealize⟩ := hprogram
  let _ := hfiniteOp
  let _ := hfinite
  have hword : ComputableTidilyInPolyTime (fun a => source (prepare a)) input encBits :=
    hprepare.tidy.of_enc_eq (fun _ => rfl)
  have hcount : ComputableTidilyInPolyTime
      (fun a => c * ((source (prepare a)).length + 1) ^ d) input encUnary := by
    have hclock : ComputableTidilyInPolyTime (fun n => c * (n + 1) ^ d) encUnary encUnary := by
      fun_prop
    exact hclock.comp (ComputableTidilyInPolyTime.length_bits.comp hword)
  have hrun := OpenOracleSimulation.isOraclePPTOn_run machine
    hword.computableInPolyTime hcount.computableInPolyTime hhandler hinitial
    invariant hinit hallowance (fun a request state hstate result hresult => by
      obtain ⟨hstate', hreply, hgrowth⟩ := hpreserve a request state hstate result hresult
      exact ⟨hstate', hreply.trans (hbound' a request.2),
        hgrowth.trans (Nat.add_le_add_left (hbound' a request.2) _)⟩)
  apply IsOraclePPTOn.iff_encoded.mpr
  refine (IsOraclePPTOn.iff_encoded.mp hrun).congr fun a External' oracle e => ?_
  have hout : encPair output stateEncoding <$> (OracleComp.interpret
      (OracleComp.sumHandler
        (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))) (handler a))
        (program (prepare a))).run (initial a) =
      encPair encBits stateEncoding <$> (OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))) (handler a))
          (output <$> program (prepare a))).run (initial a) := by
    rw [OracleComp.interpret_map, StateT.run_map, Functor.map_map]
    rfl
  rw [hout, OracleComp.interpret_map, StateT.run_map, OracleComp.interpret_map, StateT.run_map,
    ProbOracleComp.run_interpret_run_interpret, ProbOracleComp.run_interpret_run_interpret,
    hrealize]


/-- Substitute a stateful handler with its own external calls into an oracle program. The
substituted program is strict oracle PPT and preserves the joint law of the result, the
handler's final state and every external oracle's state. The efficiently computed allowance
bounds each reply and the added encoded state; one invariant must hold for every possible handler
result under every external oracle. External replies to the handler need no length bound. -/
theorem IsOraclePPTOn.run_interpret_preprocess_open
    {Operation External α β Caller State : Type} [DecidableEq Operation]
    [DecidableEq External] [Finite External]
    {source : α ↪ List Bool} {input : Caller ↪ List Bool} {output : β ↪ List Bool}
    {operationEncoding : Operation ↪ List Bool} {stateEncoding : State ↪ List Bool}
    {program : α → WordOracleComp Operation β}
    {handler : Caller → Operation × List Bool → State →
      WordOracleComp External (List Bool × State)}
    {prepare : Caller → α} {initial : Caller → State} {resources : Caller → List Bool → ℕ}
    (hprogram : IsOraclePPTOn source output program)
    (hprepare : ComputableTidilyInPolyTime prepare input source)
    (hhandler : IsOraclePPTOn (encHandlerCall input operationEncoding stateEncoding)
      (encPair encBits stateEncoding)
      (fun ⟨caller, request, state⟩ => handler caller request state))
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
        (OracleComp.sumHandler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))) (handler a))
          (program (prepare a))).run (initial a)) :=
  hprogram.run_interpret_preprocess_open_of_polyBounded hprepare.computableInPolyTime hhandler
    hinitial.computableInPolyTime invariant hinit
    (by simpa only [encUnary_apply, List.length_replicate] using hresources.polyBounded_length)
    hpreserve

/-- `Cslib.Probability.IsOraclePPTOn.run_interpret_preprocess_open` with plain polynomial-time
preparation, initial state and resource allowance. -/
theorem IsOraclePPTOn.run_interpret_preprocess_open'
    {Operation External α β Caller State : Type} [DecidableEq Operation]
    [DecidableEq External] [Finite External]
    {source : α ↪ List Bool} {input : Caller ↪ List Bool} {output : β ↪ List Bool}
    {operationEncoding : Operation ↪ List Bool} {stateEncoding : State ↪ List Bool}
    {program : α → WordOracleComp Operation β}
    {handler : Caller → Operation × List Bool → State →
      WordOracleComp External (List Bool × State)}
    {prepare : Caller → α} {initial : Caller → State} {resources : Caller → List Bool → ℕ}
    (hprogram : IsOraclePPTOn source output program)
    (hprepare : ComputableInPolyTime prepare input source)
    (hhandler : IsOraclePPTOn (encHandlerCall input operationEncoding stateEncoding)
      (encPair encBits stateEncoding)
      (fun ⟨caller, request, state⟩ => handler caller request state))
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
        (OracleComp.sumHandler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))) (handler a))
          (program (prepare a))).run (initial a)) :=
  hprogram.run_interpret_preprocess_open_of_polyBounded hprepare hhandler hinitial invariant hinit
    (by simpa only [encUnary_apply, List.length_replicate] using hresources.polyBounded_length)
    hpreserve

/-- Stateless open substitution with an explicit polynomial-time bound on the replies given
back to the original program. This specializes stateful substitution to `Unit`; the external
oracle may still be stateful and return arbitrarily long answers. -/
theorem IsOraclePPTOn.interpret_preprocess_open'
    {Operation External α β Caller : Type} [DecidableEq Operation]
    [DecidableEq External] [Finite External]
    {source : α ↪ List Bool} {input : Caller ↪ List Bool} {output : β ↪ List Bool}
    {operationEncoding : Operation ↪ List Bool}
    {program : α → WordOracleComp Operation β}
    {handler : Caller → Operation × List Bool → WordOracleComp External (List Bool)}
    {prepare : Caller → α} {resources : Caller → List Bool → ℕ}
    (hprogram : IsOraclePPTOn source output program)
    (hprepare : ComputableInPolyTime prepare input source)
    (hhandler : IsOraclePPTOn (encPair input (encPair operationEncoding encBits)) encBits
      (fun pair => handler pair.1 pair.2))
    (hresources : ComputableInPolyTime (fun pair => resources pair.1 pair.2)
      (encPair input encBits) encUnary)
    (hbound : ∀ a request reply, reply ∈ OracleComp.support (handler a request) →
      reply.length ≤ resources a request.2) :
    IsOraclePPTOn input output (fun a => OracleComp.interpret
      (OracleComp.sumHandler (fun n => ProbOracleComp.sample (ProbComp.unifFin n)) (handler a))
      (program (prepare a))) := by
  let EIn := encPair input (encPair (encPair operationEncoding encBits) (encFinEnum Unit))
  have hlift : IsOraclePPTOn EIn (encPair encBits (encFinEnum Unit))
      (fun p : Caller × ((Operation × List Bool) × Unit) =>
        (fun reply => (reply, p.2.2)) <$> handler p.1 p.2.1) :=
    (hhandler.preprocess' (input := EIn)
      (prepare := fun p : Caller × ((Operation × List Bool) × Unit) => (p.1, p.2.1))
      (by dsimp only [EIn]; fun_prop)).map_with'
        (f := fun p reply => (reply, p.2.2)) (by dsimp only [EIn]; fun_prop)
  have hrun := hprogram.run_interpret_preprocess_open'
    (handler := fun a request (state : Unit) => (fun reply => (reply, state)) <$> handler a request)
    hprepare hlift
    (ComputableInPolyTime.const ()) (fun _ _ => True) (fun _ => trivial) hresources
    (fun a request state _ result hresult => by
      obtain ⟨reply, hreply, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
      exact ⟨trivial, hbound a request reply hreply, Nat.le_add_right _ _⟩)
  have h := hrun.map' (ComputableInPolyTime.fst output (encFinEnum Unit))
  convert h using 1
  funext a
  have hliftEq : OracleComp.sumHandler
      (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
      (fun request state => (fun reply => (reply, state)) <$> handler a request) =
      (fun q => StateT.lift (σ := Unit)
        (OracleComp.sumHandler (fun n => ProbOracleComp.sample (ProbComp.unifFin n))
          (handler a) q)) := by
    funext q state
    cases q <;> simp [OracleComp.sumHandler, StateT.lift, bind_pure_comp]
  rw [hliftEq, OracleComp.run_interpret_lift]
  simp

/-- Replacing every request by a polynomial-time computed word and reading at most one reply
bit preserves strict oracle polynomial time. The certificate holds uniformly for every external
stateful oracle, including oracles with arbitrarily long answers. -/
theorem IsOraclePPTOn.interpret_bitQueries
    {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {program : α → OracleComp (fun _ : Unit × List Bool => List Bool) β}
    {request : List Bool → List Bool}
    (hprogram : IsOraclePPTOn input output
      (fun a => OracleComp.interpret ProbOracleComp.query (program a)))
    (hrequest : ComputableTidilyInPolyTime request encBits encBits) :
    IsOraclePPTOn input output (fun a => OracleComp.interpret ProbOracleComp.query
      (OracleComp.interpret (fun q : Unit × List Bool =>
        List.take 1 <$> OracleComp.query ((), request q.2)) (program a))) := by
  have hhandler : IsOraclePPTOn
      (encPair input (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit)))
      (encPair encBits (encFinEnum Unit))
      (fun pair : α × (Unit × List Bool) × Unit =>
        (fun r => (r, ())) <$> (List.take 1 <$> ProbOracleComp.query
          (spec := fun _ : Unit × List Bool => List Bool) ((), request pair.2.1.2))) :=
    (IsOraclePPTOn.query_take () (request := fun pair : α × (Unit × List Bool) × Unit =>
      request pair.2.1.2) (limit := fun _ => 1) (hrequest.comp (by fun_prop))
      (by fun_prop)).map (by fun_prop)
  have hsub := hprogram.run_interpret_preprocess_open (State := Unit)
    (handler := fun _ q _ => (fun r => (r, ())) <$> (List.take 1 <$> ProbOracleComp.query
      (spec := fun _ : Unit × List Bool => List Bool) ((), request q.2)))
    (prepare := id) (initial := fun _ => ()) (resources := fun _ _ => 1)
    ComputableTidilyInPolyTime.id' hhandler (ComputableTidilyInPolyTime.const ())
    (fun _ _ => True) (fun _ => trivial) (ComputableTidilyInPolyTime.const 1)
    (fun a query state _ result hresult => by
      obtain ⟨r, hr, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
      obtain ⟨r', -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hr
      exact ⟨trivial, List.length_take_le _ _, Nat.le_add_right _ _⟩)
  refine (hsub.map (ComputableTidilyInPolyTime.fst output (encFinEnum Unit))).congr
    fun a State oracle s => ?_
  congr 2
  rw [OracleComp.interpret_interpret, OracleComp.interpret_interpret]
  have hH : (fun q : Unit × List Bool => OracleComp.interpret (OracleComp.sumHandler
      (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
      (fun (q : Unit × List Bool) (_ : Unit) => (fun r => (r, ())) <$> (List.take 1 <$>
        ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
          ((), request q.2)))) (ProbOracleComp.query q)) =
      fun q : Unit × List Bool => StateT.lift (List.take 1 <$>
        ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
          ((), request q.2)) := by
    funext q
    rw [ProbOracleComp.interpret_query]
    funext u
    simp [StateT.lift]
  rw [hH, OracleComp.run_interpret_lift, Functor.map_map]
  simp only [OracleComp.interpret_map, OracleComp.interpret_query, id_map', id]

end Cslib.Probability
