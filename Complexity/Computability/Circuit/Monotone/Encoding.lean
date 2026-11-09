/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Encoding
public import Complexity.Computability.Circuit.Monotone.Basic
import Complexity.Computability.Circuit.Encoding.MapOp

/-!
# Encodings of monotone circuits

A monotone circuit is written down as the same circuit read in the De Morgan basis
(`Cslib.Circuits.Monotone.toDeMorgan`), the convention of the monotone circuit value problem
(`Cslib.Complexity.encMonotoneCircuitValue`). An operation is encoded by the number of its De Morgan
image in unary (`Cslib.Circuits.Monotone.encOp`); gates, codes and circuits are then encoded as
over any signature (`Cslib.Circuits.Circuit.encGate`, `Cslib.Circuits.Circuit.encCode`,
`Cslib.Circuits.Circuit.encCircuit`). So the encoding of the code of a monotone circuit is the
encoding of the code of its De Morgan reading (`Cslib.Circuits.Monotone.encCode_apply`,
`Cslib.Circuits.Monotone.encCircuit_apply`).

## Main definitions

* `Cslib.Circuits.Monotone.encOp`, `Cslib.Circuits.Monotone.encGate`,
  `Cslib.Circuits.Monotone.encCode`, `Cslib.Circuits.Monotone.encCircuit`: binary encodings of
  monotone circuits.

## Main results

* `Cslib.Circuits.Monotone.encCode_apply`, `Cslib.Circuits.Monotone.encCircuit_apply`: a monotone
  circuit is encoded as its De Morgan reading.
-/

@[expose] public section

namespace Cslib.Circuits.Monotone

open Turing.MultiTapeTM

/-- Operations of the monotone basis, encoded as their images in the De Morgan basis
(`Cslib.Circuits.Boolean.encOp`). -/
def encOp : Op ↪ List Bool :=
  ⟨fun op => Boolean.encOp (toDeMorgan op), Boolean.encOp.injective.comp toDeMorgan_injective⟩

/-- A gate of the monotone basis as data: its operation by `encOp`, then the framed binary numbers
of the wires it reads. -/
abbrev encGate : Op × List ℕ ↪ List Bool := Circuit.encGate encOp

/-- The code of a monotone circuit: its framed gates in program order, then its framed output
wires, all wire numbers in binary. -/
abbrev encCode : List (Op × List ℕ) × List ℕ ↪ List Bool := Circuit.encCode encOp

/-- **Binary encoding of monotone circuits** with `m` outputs and any number `n` of inputs: `n` in
unary, then the code of the circuit (`encCode`). -/
abbrev encCircuit (m : ℕ) : (Σ n, Circuit signature n m) ↪ List Bool :=
  Circuit.encCircuit (σ := signature) encOp m

/-- The code of a monotone circuit is encoded as the De Morgan code with the same wires and the
De Morgan images of its operations. -/
theorem encCode_apply (code : List (Op × List ℕ) × List ℕ) :
    encCode code = Boolean.encCode (code.1.map fun g => (toDeMorgan g.1, g.2), code.2) := by
  simp [encList, encPair, encOp, Function.comp_def, List.flatMap_map]

/-- A monotone circuit is encoded as its De Morgan reading. -/
theorem encCircuit_apply {m : ℕ} (c : Σ n, Circuit signature n m) :
    encCircuit m c = Boolean.encCircuit m ⟨c.1, c.2.mapOp toDeMorgan⟩ := by
  rw [Circuit.encCircuit_apply, Boolean.encCircuit_apply, Circuit.code_mapOp]
  simp only [encPair]
  exact congrArg _ (encCode_apply _)

end Cslib.Circuits.Monotone
