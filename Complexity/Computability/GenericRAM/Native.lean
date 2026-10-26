/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Native.Certificate
public import Complexity.Computability.GenericRAM.Defs
public import Complexity.Computability.Machines.Turing.MultiTape.Halting.Computable
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option

/-!
# Native certificates for RAM primitives

A `NativeCertificate` records arbitrary input-dependent time and space bounds, including the
encoded output size, for an actual finite native multi-tape machine. `Model.NativePrimitives`
collects these certificates for the scalar obligations of a RAM model. Configuration and all
operands are encoded runtime inputs; a single machine handles all of them for each fixed symbol.
Constants may depend on the symbol, and hence on a fixed finite source program. Symbols themselves
are not encoded inputs: this is not a uniform interpreter for arbitrary programs.

The semantic `Model` remains independent of finite encodings. In particular, this interface does
not require an exact real RAM to admit a bit representation. It also supplies neither a memory
representation nor a whole-machine simulation. Loads/stores still require charged lookup/update;
control, initialization and output require their own certificates. Deriving an input-only bound
from a configuration-and-input bound additionally requires charged, computable configuration
selection and an input-fit guarantee, rather than instance-dependent width advice.

## Main definitions

* `NativeCertificate`: native implementation with arbitrary resource bounds.
* `Model.Encoding`: selectable encodings of values, addresses and configuration.
* `Model.checkedConstant`, `Model.checkedOp`: include the result admissibility check.
* `Model.NativePrimitives`, `Model.NativePrimitives.IsPolynomial`: scalar obligations, including
  move and control-label validation, and their polynomiality predicate.

## Main results

* `NativeCertificate.nonempty_iff_isComputable`: arbitrary-bound certificates exist exactly for
  native computable functions.
* `NativeCertificate.isComputable`: forget the resource bounds.
* `NativeCertificate.polyTime`: obtain polynomial time under separate polynomial bounds.
* `NativeCertificate.comp`: compose certificates with input-dependent resource accounting.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.GenericRAM

open Turing.MultiTapeTM

namespace Model

/-- Finite bit representations are separate from the semantic model. Configuration encoding is
chosen explicitly; in particular, unary and binary widths have different resource costs. -/
structure Encoding (M : Model.{0, 0, 0, 0}) where
  /-- Encoding of register and memory values. -/
  value : M.Value ↪ List Bool
  /-- Encoding of memory addresses. -/
  address : M.Address ↪ List Bool
  /-- Encoding of runtime model parameters, including any word width. -/
  config : M.Config ↪ List Bool

variable {M : Model.{0, 0, 0, 0}}

/-- A fixed literal's result, including the admissibility check performed by `Data.put`. -/
def checkedConstant (M : Model) (c : M.Const) (k : M.Config) : Option M.Value := do
  let v ← M.constant k c
  if M.admissible k v then some v else none

/-- A fixed operation's result, including the admissibility check performed by `Data.put`.
A native implementation can reject overflow without materializing the unchecked result. -/
def checkedOp (M : Model) (op : M.operations.Op)
    (p : M.Config × (Fin (M.operations.Arity op) → M.Value)) : Option M.Value := do
  let v ← M.evalOp p.1 op p.2
  if M.admissible p.1 v then some v else none

/-- A constant instruction stores exactly the checked literal result, preserving faults. -/
theorem eval_const_eq_map_checkedConstant {r : ℕ} (k : M.Config) (x : Data M r)
    (d : Fin r) (c : M.Const) :
    (Op.const d c).eval k x = (M.checkedConstant c k).map (x.set d) := by
  cases h : M.constant k c with
  | none => simp [Op.eval, checkedConstant, h]
  | some v =>
    simp only [Op.eval, checkedConstant, h, bind, Option.bind_some, Data.put]
    split <;> rfl

/-- An ALU instruction stores exactly the checked operation result, preserving faults. -/
theorem eval_alu_eq_map_checkedOp {r : ℕ} (k : M.Config) (x : Data M r)
    (op : M.operations.Op) (d : Fin r) (args : Fin (M.operations.Arity op) → Fin r) :
    (Op.alu op d args).eval k x = (M.checkedOp op (k, x.regs ∘ args)).map (x.set d) := by
  cases h : M.evalOp k op (x.regs ∘ args) with
  | none => simp [Op.eval, checkedOp, h]
  | some v =>
    simp only [Op.eval, checkedOp, h, bind, Option.bind_some, Data.put]
    split <;> rfl

/-- Scalar certificates needed by a fixed-program RAM simulation. Memory lookup/update and
finite-program dispatch are additional obligations. There is no uniform symbol dispatcher here. -/
structure NativePrimitives (M : Model.{0, 0, 0, 0}) (enc : Encoding M) where
  /-- Literal symbols are fixed; configuration varies over every encoded input. -/
  constant : ∀ c, NativeCertificate (M.checkedConstant c) enc.config (encOption enc.value)
  /-- Operation symbols are fixed; configuration and all operands are runtime inputs. -/
  operation : ∀ op, NativeCertificate (M.checkedOp op)
    (encPair enc.config (encPi enc.value)) (encOption enc.value)
  /-- Tests preserve the distinction between fault, false and true. -/
  test : ∀ t, NativeCertificate (fun p => M.evalTest p.1 t p.2)
    (encPair enc.config (encPi enc.value)) (encOption encBool)
  /-- Address extraction can fault independently of move validation. -/
  address : NativeCertificate (fun p => M.address p.1 p.2)
    (encPair enc.config enc.value) (encOption enc.address)
  /-- Copy/load/store/halt validate existing values through this predicate. -/
  validMove : NativeCertificate (fun p => M.validMove p.1 p.2)
    (encPair enc.config enc.value) encBool
  /-- Current and continuing control labels both require validation. -/
  validPC : NativeCertificate (fun p => M.validPC p.1 p.2)
    (encPair enc.config encNat) encBool

/-- All six primitive certificates in a bundle have polynomial time and space bounds. -/
structure NativePrimitives.IsPolynomial {M : Model.{0, 0, 0, 0}} {enc : M.Encoding}
    (N : M.NativePrimitives enc) : Prop where
  /-- Every literal symbol's certificate has polynomial time and space bounds. -/
  constant : ∀ c, (N.constant c).IsPolynomial
  /-- Every ALU operation symbol's certificate has polynomial time and space bounds. -/
  operation : ∀ op, (N.operation op).IsPolynomial
  /-- Every test symbol's certificate has polynomial time and space bounds. -/
  test : ∀ t, (N.test t).IsPolynomial
  /-- The address extraction certificate has polynomial time and space bounds. -/
  address : N.address.IsPolynomial
  /-- The move validation certificate has polynomial time and space bounds. -/
  validMove : N.validMove.IsPolynomial
  /-- The control-label validation certificate has polynomial time and space bounds. -/
  validPC : N.validPC.IsPolynomial

end Model
end Cslib.GenericRAM
