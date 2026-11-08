/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Evaluation
import Batteries.Data.Vector.Lemmas

/-!
# Materialized circuits for exhaustive compiled tests

Composition maps every wire of the inner circuit through the outer wiring, so compiled code for
a deeply composed circuit resolves a chain of wire maps each time it reads a wire. `materialize`
stores each line's wires and the outputs in arrays once; `materialize_eq` proves the circuit is
unchanged. Exhaustive `#eval` checks materialize once and then evaluate thousands of inputs.
-/

@[expose] public section

namespace ComplexityTests.CircuitMaterialize

open Cslib Cslib.Circuits

universe v

variable {σ : Signature.{v}} {n m : ℕ}

private theorem get_ofFn {α : Type*} {k : ℕ} (f : Fin k → α) : (Vector.ofFn f).get = f :=
  funext (Vector.get_ofFn f)

/-- Rebuild a program, storing the argument wires of each line in an array. -/
def materializeProgram : {g : ℕ} → Program σ n g → Program σ n g
  | _, .empty => .empty
  | _, .gate p line =>
    let wires := Vector.ofFn line.wires
    .gate (materializeProgram p) ⟨line.op, wires.get⟩

@[simp] theorem materializeProgram_eq {g : ℕ} (p : Program σ n g) : materializeProgram p = p := by
  induction p with
  | empty => rfl
  | gate p line ih =>
    simp only [materializeProgram, ih, get_ofFn]

/-- Rebuild a circuit, storing its line wires and outputs in arrays. -/
def materialize (c : Circuit σ n m) : Circuit σ n m :=
  let outputs := Vector.ofFn c.outputs
  ⟨materializeProgram c.program, outputs.get⟩

@[simp] theorem materialize_eq (c : Circuit σ n m) : materialize c = c := by
  simp only [materialize, materializeProgram_eq, get_ofFn]

end ComplexityTests.CircuitMaterialize
