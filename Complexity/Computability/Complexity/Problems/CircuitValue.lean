/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.EvaluationTime
public import Complexity.Computability.Complexity.Classes.P
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# The circuit value problem

The *circuit value problem* asks whether a Boolean circuit outputs true on a given input
[Arora and Barak, Section 6.1][AroraBarak09]. Here an instance is a De Morgan circuit with one
output and `n` inputs together with an input in `BitString n`, so every instance is well formed.
It is encoded by the binary encoding of the circuit (`Cslib.Circuits.Boolean.encCircuit`: the
number of inputs in unary, the gates in program order with wire numbers in binary, the output
wire) followed by the input bits.

The circuit value problem is in `P` (`Cslib.Complexity.CircuitValue.mem_P`): the decider
evaluates the gate list with the polynomial-time evaluator
`Cslib.Circuits.Boolean.computableInPolyTime_evalOutput`. Ladner showed that it is
`P`-complete under logarithmic-space reductions [Ladner1975]; this is proved in
`Complexity/Computability/Complexity/Problems/CircuitValue/Completeness.lean`
(`Cslib.Complexity.CircuitValue.logSpaceComplete`).

## Main definitions

* `Cslib.Complexity.CircuitValue`: the instances whose circuit outputs true on the input.
* `Cslib.Complexity.encCircuitValue`: the encoding of instances.

## Main results

* `Cslib.Complexity.CircuitValue.computableInPolyTime_eval`: evaluation is polynomial-time.
* `Cslib.Complexity.CircuitValue.mem_P`: the circuit value problem is in `P`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
* [R. E. Ladner, *The circuit value problem is log space complete for P*][Ladner1975]
-/

@[expose] public section

namespace Cslib.Complexity

open Circuits Circuits.Boolean Turing.MultiTapeTM

/-- **The circuit value problem**: the De Morgan circuits with one output, each with an input of
its arity, whose output on that input is true. -/
def CircuitValue : Set (Σ n, Circuit signature n 1 × BitString n) :=
  {x | x.2.1.eval interpretation x.2.2 0 = true}

theorem mem_CircuitValue {x : Σ n, Circuit signature n 1 × BitString n} :
    x ∈ CircuitValue ↔ x.2.1.eval interpretation x.2.2 0 = true :=
  Iff.rfl

/-- Instances of the circuit value problem encoded by the binary encoding of the circuit
(`encCircuit`), followed by the input bits. -/
def encCircuitValue : (Σ n, Circuit signature n 1 × BitString n) ↪ List Bool :=
  ⟨fun x => encPair (encCircuit 1) encBits (⟨x.1, x.2.1⟩, List.ofFn x.2.2), by
    rintro ⟨n, c, x⟩ ⟨n', c', x'⟩ h
    obtain ⟨hc, hx⟩ := Prod.ext_iff.1 ((encPair (encCircuit 1) encBits).injective h)
    obtain ⟨rfl, hc⟩ := Sigma.mk.inj_iff.1 hc
    obtain rfl := eq_of_heq hc
    obtain rfl := List.ofFn_injective hx
    rfl⟩

theorem encCircuitValue_apply (x : Σ n, Circuit signature n 1 × BitString n) :
    encCircuitValue x = encPair (encPair encUnary encCode) encBits
      ((x.1, x.2.1.code), List.ofFn x.2.2) :=
  rfl

namespace CircuitValue

/-- The output of a circuit is the output of its code: the output wire is the only entry of the
list of output wires. -/
private theorem eval_eq_evalOutput (x : Σ n, Circuit signature n 1 × BitString n) :
    x.2.1.eval interpretation x.2.2 0 =
      evalOutput (List.ofFn x.2.2) x.2.1.code.1 (x.2.1.code.2.headD 0) := by
  rw [Circuit.eval_eq_evalOutput]
  rfl

/-- Evaluating a circuit on an input is polynomial-time, on the encoding `encCircuitValue`. -/
@[fun_prop]
theorem computableInPolyTime_eval :
    ComputableInPolyTime (fun x : Σ n, Circuit signature n 1 × BitString n =>
      x.2.1.eval interpretation x.2.2 0) encCircuitValue encBool := by
  have hraw : ComputableInPolyTime
      (fun x : Σ n, Circuit signature n 1 × BitString n => ((x.1, x.2.1.code), List.ofFn x.2.2))
      encCircuitValue (encPair (encPair encUnary encCode) encBits) :=
    .of_eq fun _ => rfl
  have hout : ComputableInPolyTime
      (fun r : (ℕ × (List (Op × List ℕ) × List ℕ)) × List Bool =>
        evalOutput r.2 r.1.2.1 (r.1.2.2.headD 0))
      (encPair (encPair encUnary encCode) encBits) encBool := by
    fun_prop
  rw [funext eval_eq_evalOutput]
  exact hout.comp hraw

/-- **The circuit value problem is in `P`**, for the binary encoding of circuits followed by the
input bits. -/
theorem mem_P : CircuitValue ∈ P encCircuitValue :=
  ⟨_, computableInPolyTime_eval, fun _ => Iff.rfl⟩

end CircuitValue

end Cslib.Complexity
