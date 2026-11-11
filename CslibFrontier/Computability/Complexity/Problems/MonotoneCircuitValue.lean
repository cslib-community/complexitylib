/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CircuitValue
public import CslibFrontier.Computability.Complexity.Classes.LogSpace
public import CslibFrontier.Computability.Circuit.Monotone.Basic
public import CslibFrontier.Computability.Circuit.Encoding.MapOp

/-!
# The monotone circuit value problem

The *monotone circuit value problem* asks whether a monotone circuit (`Cslib.Circuits.Monotone`:
constants, binary conjunction and binary disjunction, no negation) outputs true on a given input
[Goldschlager1977], [Arora and Barak, Section 6.7][AroraBarak09]. As for the circuit value problem
(`Cslib.Complexity.CircuitValue`), an instance is a circuit with one output and `n` inputs
together with an input in `BitString n`. A monotone circuit is encoded as the same circuit read in
the De Morgan basis (`Cslib.Circuits.Monotone.toDeMorgan`), so an encoded instance of the monotone
problem is an encoded instance of the circuit value problem
(`Cslib.Complexity.encMonotoneCircuitValue`).

The problem reduces to the circuit value problem in logarithmic space, indeed by the identity on
encodings (`Cslib.Complexity.MonotoneCircuitValue.logSpaceReducible_circuitValue`), and hence is in
`P` (`Cslib.Complexity.MonotoneCircuitValue.mem_P`). It is `P`-complete under logarithmic-space
reductions
(`CslibFrontier/Computability/Complexity/Problems/MonotoneCircuitValue/Completeness.lean`).

## Main definitions

* `Cslib.Complexity.MonotoneCircuitValue`: the instances whose monotone circuit outputs true.
* `Cslib.Complexity.MonotoneCircuitValue.toDeMorgan`: an instance read in the De Morgan basis.
* `Cslib.Complexity.encMonotoneCircuitValue`: the encoding of instances.

## Main results

* `Cslib.Complexity.MonotoneCircuitValue.mem_iff_toDeMorgan_mem`: a monotone instance is a
  yes-instance iff its De Morgan reading is.
* `Cslib.Complexity.MonotoneCircuitValue.logSpaceReducible_circuitValue`: the monotone problem
  reduces to the circuit value problem.
* `Cslib.Complexity.MonotoneCircuitValue.mem_P`: the monotone circuit value problem is in `P`.

## References

* [L. M. Goldschlager, *The monotone and planar circuit value problems are log space complete
  for P*][Goldschlager1977]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.7][AroraBarak09]
-/

@[expose] public section



namespace Cslib.Complexity

open Circuits Circuits.Boolean Turing.MultiTapeTM

/-- **The monotone circuit value problem**: the monotone circuits with one output, each with an
input of its arity, whose output on that input is true [Goldschlager1977]. -/
def MonotoneCircuitValue : Set (Σ n, Circuit Monotone.signature n 1 × BitString n) :=
  {x | x.2.1.eval Monotone.interpretation x.2.2 0 = true}

theorem mem_MonotoneCircuitValue {x : Σ n, Circuit Monotone.signature n 1 × BitString n} :
    x ∈ MonotoneCircuitValue ↔ x.2.1.eval Monotone.interpretation x.2.2 0 = true :=
  Iff.rfl

namespace MonotoneCircuitValue

/-- A monotone instance read as an instance of the circuit value problem, in the De Morgan
basis. -/
def toDeMorgan (x : Σ n, Circuit Monotone.signature n 1 × BitString n) :
    Σ n, Circuit signature n 1 × BitString n :=
  ⟨x.1, x.2.1.mapOp Monotone.toDeMorgan, x.2.2⟩

theorem toDeMorgan_injective : Function.Injective toDeMorgan := by
  rintro ⟨n, c, x⟩ ⟨n', c', x'⟩ h
  simp only [toDeMorgan, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  obtain ⟨hc, hx⟩ := Prod.ext_iff.1 (eq_of_heq h)
  obtain rfl := Circuit.mapOp_injective _ Monotone.toDeMorgan_injective hc
  obtain rfl := hx
  rfl

/-- A monotone instance is a yes-instance exactly when its De Morgan reading is. -/
theorem mem_iff_toDeMorgan_mem {x : Σ n, Circuit Monotone.signature n 1 × BitString n} :
    x ∈ MonotoneCircuitValue ↔ toDeMorgan x ∈ CircuitValue := by
  rw [mem_MonotoneCircuitValue, mem_CircuitValue, toDeMorgan,
    Circuit.eval_mapOp (I := Monotone.interpretation)]

end MonotoneCircuitValue

/-- Instances of the monotone circuit value problem, encoded as the instances of the circuit value
problem with the same circuit read in the De Morgan basis (`encCircuitValue`). -/
def encMonotoneCircuitValue : (Σ n, Circuit Monotone.signature n 1 × BitString n) ↪ List Bool :=
  ⟨fun x => encCircuitValue (MonotoneCircuitValue.toDeMorgan x),
    encCircuitValue.injective.comp MonotoneCircuitValue.toDeMorgan_injective⟩

theorem encMonotoneCircuitValue_apply (x : Σ n, Circuit Monotone.signature n 1 × BitString n) :
    encMonotoneCircuitValue x = encCircuitValue (MonotoneCircuitValue.toDeMorgan x) :=
  rfl

namespace MonotoneCircuitValue

/-- **The monotone circuit value problem reduces to the circuit value problem** in logarithmic
space, indeed by the identity on encodings. -/
theorem logSpaceReducible_circuitValue :
    LogSpaceReducible encMonotoneCircuitValue encCircuitValue MonotoneCircuitValue CircuitValue :=
  ⟨toDeMorgan, by
    obtain ⟨t, c, k, State, hfin, tm, htm⟩ :=
      ComputableInLogSpace.id (encIn := encMonotoneCircuitValue)
    exact ⟨t, c, k, State, hfin, tm, fun x => htm x⟩,
    fun _ => mem_iff_toDeMorgan_mem⟩

/-- **The monotone circuit value problem is in `P`.** -/
theorem mem_P : MonotoneCircuitValue ∈ P encMonotoneCircuitValue :=
  logSpaceReducible_circuitValue.polyTimeReducible.mem_P CircuitValue.mem_P

end MonotoneCircuitValue

end Cslib.Complexity
