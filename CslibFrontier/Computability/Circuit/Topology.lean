/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.WireNumber
public import Cslib.Computability.Circuit.Basic
import CslibFrontier.Computability.Circuit.Program

/-!
# Circuit topologies

The topology of a circuit records, for each gate, its arity and the wires supplying its
arguments, together with the output wires, and forgets the gate operations. It is the part of a
circuit that a garbled circuit is allowed to reveal (topology side information in the sense of
[BellareHoangRogaway2012]).

A topology is *ordered* when every gate reads only wires of smaller wire number than its own
(`Circuit.Topology.IsOrdered`); the topology of every circuit is ordered
(`Circuit.isOrdered_topology`).

## Main definitions

* `Cslib.Circuits.Circuit.Topology`: arities, argument wires and output wires.
* `Cslib.Circuits.Circuit.topology`: the topology of a circuit.
* `Cslib.Circuits.Circuit.Topology.IsOrdered`: gates read only lower-numbered wires.

## Main results

* `Cslib.Circuits.Circuit.isOrdered_topology`: circuit topologies are ordered.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

@[expose] public section

namespace Cslib.Circuits

/-- The wiring of a circuit with `n` inputs, `m` outputs and `s` gates, without the gate
operations: each gate's arity and argument wires, and the output wires. -/
structure Circuit.Topology (n m s : ℕ) where
  /-- The arity of each gate. -/
  arity : Fin s → ℕ
  /-- The wire supplying each argument of each gate. -/
  wires : (g : Fin s) → Fin (arity g) → Wire n s
  /-- The wire carrying each output. -/
  outputs : Fin m → Wire n s

universe v

variable {σ : Signature.{v}} {n m s : ℕ}

/-- The topology of a circuit: the arities and argument wires of its lines and its output wires. -/
def Circuit.topology (C : Circuit σ n m) : Circuit.Topology n m C.size where
  arity g := σ.Arity (C.program.lines g).op
  wires g := (C.program.lines g).wires
  outputs := C.outputs

/-- Every gate reads only wires whose number is smaller than its own. -/
def Circuit.Topology.IsOrdered (τ : Circuit.Topology n m s) : Prop :=
  ∀ g k, (τ.wires g k).toNat < (Wire.gate g : Wire n s).toNat

/-- The topology of a circuit is ordered: its lines read only inputs and earlier gates. -/
theorem Circuit.isOrdered_topology (C : Circuit σ n m) : C.topology.IsOrdered := by
  intro g k
  rw [Wire.toNat_gate]
  cases hk : C.topology.wires g k with
  | input i =>
    rw [Wire.toNat_input]
    exact Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)
  | gate j =>
    rw [Wire.toNat_gate]
    exact Nat.add_lt_add_left (C.program.lt_of_lines_wires_eq_gate g k j hk) n

end Cslib.Circuits
