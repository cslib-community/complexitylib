/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.GenericRAM.Native.Nat
public import Complexity.Computability.WordRAM.Native
import Complexity.Tactic.PolyTime
import Mathlib.Data.Fin.VecNotation

/-!
# Native RAM primitive certificates

Complete bundle nonvacuity, native computability without efficiency assumptions, polynomial
composition and automation, and distinct fault paths in checked scalar/instruction semantics.
-/

@[expose] public section

namespace ComplexityTests.GenericRAMNative

open Cslib.GenericRAM Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open BoundedNat

-- The bundle exists for an infinite runtime input domain, with every field polynomial.
/-- The complete scalar bundle has a concrete native implementation. -/
theorem nativePrimitives_nonempty : Nonempty (model.NativePrimitives encoding) := ⟨nativePrimitives⟩
example (c : ℕ) : (nativePrimitives.constant c).IsPolynomial :=
  nativePrimitives_isPolynomial.constant c
example (op : model.operations.Op) : (nativePrimitives.operation op).IsPolynomial :=
  nativePrimitives_isPolynomial.operation op
example (t : model.tests.Op) : (nativePrimitives.test t).IsPolynomial :=
  nativePrimitives_isPolynomial.test t
example : nativePrimitives.address.IsPolynomial :=
  nativePrimitives_isPolynomial.address
example : nativePrimitives.validMove.IsPolynomial :=
  nativePrimitives_isPolynomial.validMove
example : nativePrimitives.validPC.IsPolynomial :=
  nativePrimitives_isPolynomial.validPC

-- Pure native computability suffices for arbitrary-bound certification.
example {α β : Type} (f : α → β) (ei : α ↪ List Bool) (eo : β ↪ List Bool)
    (h : IsComputable f ei eo) : Nonempty (NativeCertificate f ei eo) :=
  NativeCertificate.nonempty_iff_isComputable.mpr h

-- Recover actual native machine existence, not a RAM implementation axiom.
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State),
    ∀ p, tm.Computes (encPair encNat encNat p) (encOption encNat (model.address p.1 p.2)) :=
  isComputable_iff.mp nativePrimitives.address.isComputable

-- Composition exposes the intermediate-dependent bounds and remains polynomial.
private noncomputable def present : NativeCertificate
    (fun x : Option ℕ => x.isSome) (encOption encNat) encBool :=
  .ofPolyTime (ComputableInPolyTime.optionIsSome (ComputableInPolyTime.of_eq fun _ => rfl))

private noncomputable def addressAccepted := present.comp nativePrimitives.address

example (p : ℕ × ℕ) : addressAccepted.time p =
    nativePrimitives.address.time p + present.time (model.address p.1 p.2) := rfl
example : addressAccepted.IsPolynomial :=
  present.comp_isPolynomial nativePrimitives.address
    (NativeCertificate.ofPolyTime_isPolynomial
      (ComputableInPolyTime.optionIsSome (ComputableInPolyTime.of_eq fun _ => rfl)))
    (nativePrimitives_isPolynomial.address)
example : IsComputable (fun p => (model.address p.1 p.2).isSome)
    (encPair encNat encNat) encBool := addressAccepted.isComputable

-- Named certificates are reused without unfolding their implementations (via both `polytime` and
-- `fun_prop`).
example : ComputableTidilyInPolyTime (model.checkedOp ())
    (encPair encNat (encPi encNat)) (encOption encNat) := by polytime
example : ComputableTidilyInPolyTime
    (fun k => (model.checkedConstant 7 k).getD 0) encNat encNat := by polytime
example : ComputableInPolyTime
    (Cslib.WordRAM.Basis.standard.genericModel.checkedOp (.bin .add))
    (encPair encUnary (encPi encNat)) (encOption encNat) := by polytime
example (op : Cslib.WordRAM.StandardOp) : ComputableInPolyTime
    (Cslib.WordRAM.Basis.standard.genericModel.checkedOp op)
    (encPair encUnary (encPi encNat)) (encOption encNat) := by polytime
example (op : Cslib.WordRAM.StandardOp) : ComputableInPolyTime
    (Cslib.WordRAM.Basis.exact.genericModel.checkedOp op)
    (encPair encUnary (encPi encNat)) (encOption encNat) := by polytime
example (op : Cslib.WordRAM.Basis.additive.Op) : ComputableInPolyTime
    (Cslib.WordRAM.Basis.additive.genericModel.checkedOp op)
    (encPair encUnary (encPi encNat)) (encOption encNat) := by polytime
example (op : Cslib.WordRAM.Basis.arithmetic.Op) : ComputableInPolyTime
    (Cslib.WordRAM.Basis.arithmetic.genericModel.checkedOp op)
    (encPair encUnary (encPi encNat)) (encOption encNat) := by polytime
example (B : Cslib.WordRAM.Basis) (c : ℕ) : ComputableInPolyTime
    (B.genericModel.checkedConstant c) encUnary (encOption encNat) := by polytime
example (B : Cslib.WordRAM.Basis) (c : ℕ) : ComputableInPolyTime
    (B.genericModel.checkedConstant c) encUnary (encOption encNat) := by fun_prop
example (B : Cslib.WordRAM.Basis) (t : Option Bool) : ComputableInPolyTime
    (fun p => B.genericModel.evalTest p.1 t p.2)
    (encPair encUnary (encPi encNat)) (encOption encBool) := by polytime
example (B : Cslib.WordRAM.Basis) : ComputableInPolyTime
    (fun p => B.genericModel.address p.1 p.2)
    (encPair encUnary encNat) (encOption encNat) := by polytime
example (B : Cslib.WordRAM.Basis) : ComputableInPolyTime
    (fun p => B.genericModel.validMove p.1 p.2)
    (encPair encUnary encNat) encBool := by polytime
example (B : Cslib.WordRAM.Basis) : ComputableInPolyTime
    (fun p => B.genericModel.validPC p.1 p.2)
    (encPair encUnary encNat) encBool := by polytime
example (op : Cslib.WordRAM.StandardOp) : ComputableInPolyTime
    (Cslib.WordRAM.Basis.standard.genericModel.checkedOp op)
    (encPair encUnary (encPi encNat)) (encOption encNat) := by fun_prop
example (op : Cslib.WordRAM.StandardOp) : ComputableInPolyTime
    (Cslib.WordRAM.Basis.exact.genericModel.checkedOp op)
    (encPair encUnary (encPi encNat)) (encOption encNat) := by fun_prop

-- Binary bitwise, right-shift, bit-length, and unary-capped minimum plain certificates.
example : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 &&& p.2)
    (encPair encNat encNat) encNat := by polytime
example : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 &&& p.2)
    (encPair encNat encNat) encNat := by fun_prop
example : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 ||| p.2)
    (encPair encNat encNat) encNat := by polytime
example : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 ^^^ p.2)
    (encPair encNat encNat) encNat := by polytime
example : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 >>> p.2)
    (encPair encNat encNat) encNat := by polytime
example : ComputableInPolyTime Nat.size encNat encUnary := by polytime
example : ComputableInPolyTime Nat.size encNat encUnary := by fun_prop
example : ComputableInPolyTime (fun p : ℕ × ℕ => min p.1 p.2)
    (encPair encUnary encNat) encUnary := by polytime
example : ComputableInPolyTime (fun p : ℕ × ℕ => min p.1 p.2)
    (encPair encUnary encNat) encUnary := by fun_prop
example : ComputableInPolyTime
    (fun p : List ℕ × ℕ => (p.1.foldl (fun acc _ => acc) p.2) &&& p.2)
    (encPair (encList encNat) encNat) encNat := by polytime

-- Literals, results, tests, addresses, moves and labels have live rejection paths.
example : model.checkedConstant 3 4 = some 3 := by decide
example : model.checkedConstant 4 4 = none := by decide
example : model.checkedConstant 0 0 = none := by decide
example : model.checkedOp () (8, ![3, 4]) = some 7 := by decide
example : model.checkedOp () (7, ![3, 4]) = none := by decide
example : model.evalTest 8 () ![3, 4] = some true := by decide
example : model.evalTest 8 () ![4, 3] = some false := by decide
example : model.evalTest 8 () ![8, 3] = none := by decide
example : model.evalTest 8 () ![3, 8] = none := by decide
example : model.address 4 3 = some 3 := by decide
example : model.address 4 4 = none := by decide
example : model.validMove 4 3 = true ∧ model.validMove 4 4 = false := by decide
example : model.validPC 4 3 = true ∧ model.validPC 4 4 = false := by decide

private def data (a v : ℕ) : Data model 2 := ⟨![a, v], fun _ => v⟩

-- Loads reject either failed address extraction or invalid loaded values.
example : (Op.load 1 0).eval (M := model) 4 (data 4 0) = none := rfl
example : (Op.load 1 0).eval (M := model) 4 (data 0 4) = none := rfl
-- Stores and copies validate their source; halt checks its output.
example : (Op.store 0 1).eval (M := model) 4 (data 0 4) = none := rfl
example : (Op.copy 0 1).eval (M := model) 4 (data 0 4) = none := rfl
example : Cslib.GenericRAM.step (M := model) 4 [.halt 1]
    (⟨0, data 0 4⟩ : State model 2) = .fault := rfl
-- Validate current PC and jump destination, and fault rather than take a false branch.
example : Cslib.GenericRAM.step (M := model) 0 [.halt 0]
    (⟨0, data 0 0⟩ : State model 2) = .fault := rfl
example : Cslib.GenericRAM.step (M := model) 4 [.jump 4]
    (⟨0, data 0 0⟩ : State model 2) = .fault := rfl
example : Cslib.GenericRAM.step (M := model) 4 [.branch (.test () ![0, 1]) 0]
    (⟨0, data 0 4⟩ : State model 2) = .fault := rfl
example : run (M := model) 4 [.branch (.test () ![0, 1]) 0, .halt 1] 2
    (⟨0, data 2 1⟩ : State model 2) = some (1, 2) := rfl

-- Constants and ALU checks are connected to the existing instruction semantics.
example (k : ℕ) (x : Data model 2) :
    (Op.alu () 0 ![0, 1]).eval k x =
      (model.checkedOp () (k, x.regs ∘ ![0, 1])).map (x.set 0) :=
  Model.eval_alu_eq_map_checkedOp ..

-- WordRAM uses an exclusive bound 2^w, so width zero still admits zero.
private abbrev word := Cslib.WordRAM.Basis.standard.genericModel
private abbrev exactWord := Cslib.WordRAM.Basis.exact.genericModel
example : word.checkedOp (.bin .add) (0, ![0, 0]) = some 0 := by decide
example : word.checkedOp (.bin .add) (0, ![0, 1]) = none := by decide
example : word.checkedOp (.bin .add) (2, ![1, 2]) = some 3 := by decide
example : word.checkedOp (.bin .add) (2, ![2, 2]) = none := by decide
example : word.checkedOp (.bin .add) (3, ![2, 2]) = some 4 := by decide
example : word.checkedOp .width (0, ![]) = some 0 := by decide
example : word.checkedOp .width (1, ![]) = some 1 := by decide
example : word.checkedOp .width (2, ![]) = some 2 := by decide
example : word.checkedOp (.bin .and) (2, ![3, 1]) = some 1 := by decide
example : word.checkedOp (.bin .or) (2, ![2, 1]) = some 3 := by decide
example : word.checkedOp (.bin .xor) (2, ![3, 1]) = some 2 := by decide
example : word.checkedOp (.bin .shiftRight) (2, ![6, 1]) = some 3 := by decide
example : word.checkedOp (.bin .shiftRight) (1, ![6, 1]) = none := by decide
example : word.checkedOp (.bin .shiftLeft) (3, ![1, 2]) = some 4 := by decide
example : word.checkedOp (.bin .shiftLeft) (2, ![1, 2]) = none := by decide
-- Large shift counts y > w preserve zero and reject nonzero left shifts.
example : word.checkedOp (.bin .shiftLeft) (2, ![0, 100]) = some 0 := by decide
example : word.checkedOp (.bin .shiftLeft) (2, ![1, 100]) = none := by decide
-- Standard saturating/zero-default arithmetic vs. exact partial arithmetic on underflow/zero-div.
example : word.checkedOp (.bin .sub) (2, ![2, 3]) = some 0 := by decide
example : exactWord.checkedOp (.bin .sub) (2, ![2, 3]) = none := by decide
example : exactWord.checkedOp (.bin .sub) (2, ![3, 2]) = some 1 := by decide
example : word.checkedOp (.bin .div) (2, ![3, 0]) = some 0 := by decide
example : exactWord.checkedOp (.bin .div) (2, ![3, 0]) = none := by decide
example : exactWord.checkedOp (.bin .div) (2, ![3, 2]) = some 1 := by decide
example : word.checkedOp (.bin .mod) (2, ![3, 0]) = some 3 := by decide
example : exactWord.checkedOp (.bin .mod) (2, ![3, 0]) = none := by decide
example : exactWord.checkedOp (.bin .mod) (2, ![3, 2]) = some 1 := by decide

-- Complete native primitive bundles for standard, additive, arithmetic, and exact bases.
example : Cslib.WordRAM.checkedAddCertificate.IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial Cslib.WordRAM.checkedAdd_polyTime
example : Cslib.WordRAM.Basis.standard.nativePrimitives.IsPolynomial :=
  Cslib.WordRAM.Basis.standard.nativePrimitives_isPolynomial
example : Cslib.WordRAM.Basis.additive.nativePrimitives.IsPolynomial :=
  Cslib.WordRAM.Basis.additive.nativePrimitives_isPolynomial
example : Cslib.WordRAM.Basis.arithmetic.nativePrimitives.IsPolynomial :=
  Cslib.WordRAM.Basis.arithmetic.nativePrimitives_isPolynomial
example : Cslib.WordRAM.Basis.exact.nativePrimitives.IsPolynomial :=
  Cslib.WordRAM.Basis.exact.nativePrimitives_isPolynomial

end ComplexityTests.GenericRAMNative
