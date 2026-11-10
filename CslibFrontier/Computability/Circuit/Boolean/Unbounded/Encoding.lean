/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Encoding
public import CslibFrontier.Computability.Circuit.Boolean.Unbounded
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Encodings of circuits with unbounded fan-in

An operation of the unbounded fan-in basis is written as a number in unary: `0` for negation,
`2 m + 1` for the conjunction of `m` arguments and `2 m + 2` for their disjunction
(`Unbounded.Op.toNat`). Circuits are then encoded by the encoding of circuits over an arbitrary
signature (`Cslib.Circuits.Circuit.encCircuit`): the number of inputs in unary, the gates in program
order with wire numbers in binary, and the output wires. The arity of a gate is written in unary,
but a gate of a circuit lists as many wires as its arity, so the encoding of a circuit is at most a
constant factor longer than with the arity in binary.

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.Op.toNat`, `Cslib.Circuits.Boolean.Unbounded.encOp`: the
  operations in unary.
* `Cslib.Circuits.Boolean.Unbounded.encCircuit`: circuits over the unbounded fan-in basis.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.Op.toNat_injective`: the numbering is injective.
* `Cslib.Circuits.Boolean.Unbounded.computableInPolyTime_and`,
  `Cslib.Circuits.Boolean.Unbounded.computableInPolyTime_or`: writing a conjunction or disjunction
  of a given arity, in unary, is polynomial-time.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Unbounded

open Turing.MultiTapeTM

/-- The number of an operation: `0` for negation, `2 m + 1` for the conjunction of `m` arguments
and `2 m + 2` for their disjunction. -/
def Op.toNat : Op → ℕ
  | .not => 0
  | .and m => 2 * m + 1
  | .or m => 2 * m + 2

/-- The numbering `Op.toNat` is injective. -/
theorem Op.toNat_injective : Function.Injective Op.toNat := by
  rintro (_ | m | m) (_ | m' | m') h <;> simp only [Op.toNat] at h <;> first | rfl | omega |
    (congr 1; omega)

/-- Operations of the unbounded fan-in basis, encoded by their number `Op.toNat` in unary. -/
def encOp : Op ↪ List Bool :=
  ⟨fun op => encUnary op.toNat, encUnary.injective.comp Op.toNat_injective⟩

/-- **Binary encoding of circuits over the unbounded fan-in basis** with `m` outputs: the number of
inputs in unary, then the gates in program order and the output wires, with wire numbers in binary
(`Cslib.Circuits.Circuit.encCircuit`). -/
abbrev encCircuit (m : ℕ) : (Σ n, Circuit signature n m) ↪ List Bool :=
  Circuit.encCircuit (σ := signature) encOp m

/-- Writing the conjunction of `m` arguments is polynomial-time from `m` in unary. -/
theorem computableInPolyTime_and :
    ComputableInPolyTime (fun m : ℕ => (Op.and m : Op)) encUnary encOp :=
  ComputableInPolyTime.of_enc_eq (f := fun m : ℕ => 2 * m + 1) (by fun_prop) fun _ => rfl

/-- Writing the disjunction of `m` arguments is polynomial-time from `m` in unary. -/
theorem computableInPolyTime_or :
    ComputableInPolyTime (fun m : ℕ => (Op.or m : Op)) encUnary encOp :=
  ComputableInPolyTime.of_enc_eq (f := fun m : ℕ => 2 * m + 2) (by fun_prop) fun _ => rfl

end Cslib.Circuits.Boolean.Unbounded
