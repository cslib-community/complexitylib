/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Quantum.Basic

/-! A shared one-qubit circuit fixture, exported for ordinary module clients. -/

public section

namespace CslibFrontierTests.QuantumCircuit

open Cslib.Quantum

/-- The Hadamard gate on the only qubit of a one-qubit register. -/
@[expose] noncomputable def h₀ : PlacedGate 1 := ⟨1, Gate.hadamard, Function.Embedding.refl _⟩

end CslibFrontierTests.QuantumCircuit
