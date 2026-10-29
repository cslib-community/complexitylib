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
example (c : ℕ) (op : model.operations.Op) (t : model.tests.Op) :
    (nativePrimitives.constant c).IsPolynomial ∧
    (nativePrimitives.operation op).IsPolynomial ∧
    (nativePrimitives.test t).IsPolynomial ∧
    nativePrimitives.address.IsPolynomial ∧
    nativePrimitives.validMove.IsPolynomial ∧
    nativePrimitives.validPC.IsPolynomial :=
  ⟨nativePrimitives_isPolynomial.constant c,
   nativePrimitives_isPolynomial.operation op,
   nativePrimitives_isPolynomial.test t,
   nativePrimitives_isPolynomial.address,
   nativePrimitives_isPolynomial.validMove,
   nativePrimitives_isPolynomial.validPC⟩

-- Pure native computability suffices for arbitrary-bound certification and recovers actual native
-- machine existence, not a RAM implementation axiom.
example :
    Nonempty (NativeCertificate (fun p => model.address p.1 p.2)
      (encPair encNat encNat) (encOption encNat)) ∧
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State),
      ∀ p, tm.Computes (encPair encNat encNat p) (encOption encNat (model.address p.1 p.2)) :=
  ⟨NativeCertificate.nonempty_iff_isComputable.mpr nativePrimitives.address.isComputable,
   isComputable_iff.mp nativePrimitives.address.isComputable⟩

-- Composition exposes the intermediate-dependent bounds and remains polynomial.
private noncomputable def present : NativeCertificate
    (fun x : Option ℕ => x.isSome) (encOption encNat) encBool :=
  .ofPolyTime (ComputableInPolyTime.optionIsSome (ComputableInPolyTime.of_eq fun _ => rfl))

private noncomputable def addressAccepted := present.comp nativePrimitives.address

example (p : ℕ × ℕ) :
    addressAccepted.time p =
      nativePrimitives.address.time p + present.time (model.address p.1 p.2) ∧
    addressAccepted.IsPolynomial ∧
    IsComputable (fun p => (model.address p.1 p.2).isSome)
      (encPair encNat encNat) encBool :=
  ⟨rfl,
   present.comp_isPolynomial nativePrimitives.address
     (NativeCertificate.ofPolyTime_isPolynomial
       (ComputableInPolyTime.optionIsSome (ComputableInPolyTime.of_eq fun _ => rfl)))
     nativePrimitives_isPolynomial.address,
   addressAccepted.isComputable⟩

-- Named certificates are reused without unfolding their implementations (via both `polytime` and
-- `fun_prop`).
example (op : Cslib.WordRAM.StandardOp) (opAdd : Cslib.WordRAM.Basis.additive.Op)
    (opArith : Cslib.WordRAM.Basis.arithmetic.Op) :
    ComputableTidilyInPolyTime (model.checkedOp ())
      (encPair encNat (encPi encNat)) (encOption encNat) ∧
    ComputableTidilyInPolyTime
      (fun k => (model.checkedConstant 7 k).getD 0) encNat encNat ∧
    ComputableInPolyTime
      (Cslib.WordRAM.Basis.standard.genericModel.checkedOp (.bin .add))
      (encPair encUnary (encPi encNat)) (encOption encNat) ∧
    ComputableInPolyTime
      (Cslib.WordRAM.Basis.standard.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat) ∧
    ComputableInPolyTime
      (Cslib.WordRAM.Basis.exact.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat) ∧
    ComputableInPolyTime
      (Cslib.WordRAM.Basis.additive.genericModel.checkedOp opAdd)
      (encPair encUnary (encPi encNat)) (encOption encNat) ∧
    ComputableInPolyTime
      (Cslib.WordRAM.Basis.arithmetic.genericModel.checkedOp opArith)
      (encPair encUnary (encPi encNat)) (encOption encNat) :=
  ⟨by polytime, by polytime, by polytime, by polytime, by polytime, by polytime, by polytime⟩

example (B : Cslib.WordRAM.Basis) (c : ℕ) (t : Option Bool) (op : Cslib.WordRAM.StandardOp) :
    ComputableInPolyTime (B.genericModel.checkedConstant c) encUnary (encOption encNat) ∧
    ComputableInPolyTime (B.genericModel.checkedConstant c) encUnary (encOption encNat) ∧
    ComputableInPolyTime (fun p => B.genericModel.evalTest p.1 t p.2)
      (encPair encUnary (encPi encNat)) (encOption encBool) ∧
    ComputableInPolyTime (fun p => B.genericModel.address p.1 p.2)
      (encPair encUnary encNat) (encOption encNat) ∧
    ComputableInPolyTime (fun p => B.genericModel.validMove p.1 p.2)
      (encPair encUnary encNat) encBool ∧
    ComputableInPolyTime (fun p => B.genericModel.validPC p.1 p.2)
      (encPair encUnary encNat) encBool ∧
    ComputableInPolyTime
      (Cslib.WordRAM.Basis.standard.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat) ∧
    ComputableInPolyTime
      (Cslib.WordRAM.Basis.exact.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat) :=
  ⟨by polytime, by fun_prop, by polytime, by polytime, by polytime, by polytime,
   by fun_prop, by fun_prop⟩

-- Binary bitwise, right-shift, bit-length, and unary-capped minimum plain certificates.
example :
    ComputableInPolyTime (fun p : ℕ × ℕ => p.1 &&& p.2) (encPair encNat encNat) encNat ∧
    ComputableInPolyTime (fun p : ℕ × ℕ => p.1 &&& p.2) (encPair encNat encNat) encNat ∧
    ComputableInPolyTime (fun p : ℕ × ℕ => p.1 ||| p.2) (encPair encNat encNat) encNat ∧
    ComputableInPolyTime (fun p : ℕ × ℕ => p.1 ^^^ p.2) (encPair encNat encNat) encNat ∧
    ComputableInPolyTime (fun p : ℕ × ℕ => p.1 >>> p.2) (encPair encNat encNat) encNat ∧
    ComputableInPolyTime Nat.size encNat encUnary ∧
    ComputableInPolyTime Nat.size encNat encUnary ∧
    ComputableInPolyTime (fun p : ℕ × ℕ => min p.1 p.2) (encPair encUnary encNat) encUnary ∧
    ComputableInPolyTime (fun p : ℕ × ℕ => min p.1 p.2) (encPair encUnary encNat) encUnary ∧
    ComputableInPolyTime
      (fun p : List ℕ × ℕ => (p.1.foldl (fun acc _ => acc) p.2) &&& p.2)
      (encPair (encList encNat) encNat) encNat :=
  ⟨by polytime, by fun_prop, by polytime, by polytime, by polytime,
   by polytime, by fun_prop, by polytime, by fun_prop, by polytime⟩

-- Literals, results, tests, addresses, moves and labels have live rejection paths.
example :
    model.checkedConstant 3 4 = some 3 ∧
    model.checkedConstant 4 4 = none ∧
    model.checkedConstant 0 0 = none ∧
    model.checkedOp () (8, ![3, 4]) = some 7 ∧
    model.checkedOp () (7, ![3, 4]) = none ∧
    model.evalTest 8 () ![3, 4] = some true ∧
    model.evalTest 8 () ![4, 3] = some false ∧
    model.evalTest 8 () ![8, 3] = none ∧
    model.evalTest 8 () ![3, 8] = none ∧
    model.address 4 3 = some 3 ∧
    model.address 4 4 = none ∧
    (model.validMove 4 3 = true ∧ model.validMove 4 4 = false) ∧
    (model.validPC 4 3 = true ∧ model.validPC 4 4 = false) := by
  decide

private def data (a v : ℕ) : Data model 2 := ⟨![a, v], fun _ => v⟩

-- Loads reject either failed address extraction or invalid loaded values; stores and copies
-- validate their source; halt checks its output; and step/run validate current PC, jump
-- destination, and branch test failure.
example :
    (Op.load 1 0).eval (M := model) 4 (data 4 0) = none ∧
    (Op.load 1 0).eval (M := model) 4 (data 0 4) = none ∧
    (Op.store 0 1).eval (M := model) 4 (data 0 4) = none ∧
    (Op.copy 0 1).eval (M := model) 4 (data 0 4) = none ∧
    Cslib.GenericRAM.step (M := model) 4 [.halt 1] (⟨0, data 0 4⟩ : State model 2) = .fault ∧
    Cslib.GenericRAM.step (M := model) 0 [.halt 0] (⟨0, data 0 0⟩ : State model 2) = .fault ∧
    Cslib.GenericRAM.step (M := model) 4 [.jump 4] (⟨0, data 0 0⟩ : State model 2) = .fault ∧
    Cslib.GenericRAM.step (M := model) 4 [.branch (.test () ![0, 1]) 0]
      (⟨0, data 0 4⟩ : State model 2) = .fault ∧
    run (M := model) 4 [.branch (.test () ![0, 1]) 0, .halt 1] 2
      (⟨0, data 2 1⟩ : State model 2) = some (1, 2) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Constants and ALU checks are connected to the existing instruction semantics.
example :
    (Op.alu () 0 ![0, 1]).eval (M := model) 8 (data 3 4) =
      (model.checkedOp () (8, (data 3 4).regs ∘ ![0, 1])).map ((data 3 4).set 0) ∧
    (Op.alu () 0 ![0, 1]).eval (M := model) 8 (data 3 4) = some ((data 3 4).set 0 7) :=
  ⟨Model.eval_alu_eq_map_checkedOp .., rfl⟩

-- WordRAM uses an exclusive bound 2^w, so width zero still admits zero; large shift counts y > w
-- preserve zero and reject nonzero left shifts; and standard saturating/zero-default arithmetic
-- contrasts with exact partial arithmetic on underflow/zero-div.
private abbrev word := Cslib.WordRAM.Basis.standard.genericModel
private abbrev exactWord := Cslib.WordRAM.Basis.exact.genericModel
example :
    word.checkedOp (.bin .add) (0, ![0, 0]) = some 0 ∧
    word.checkedOp (.bin .add) (0, ![0, 1]) = none ∧
    word.checkedOp (.bin .add) (2, ![1, 2]) = some 3 ∧
    word.checkedOp (.bin .add) (2, ![2, 2]) = none ∧
    word.checkedOp (.bin .add) (3, ![2, 2]) = some 4 ∧
    word.checkedOp .width (0, ![]) = some 0 ∧
    word.checkedOp .width (1, ![]) = some 1 ∧
    word.checkedOp .width (2, ![]) = some 2 ∧
    word.checkedOp (.bin .and) (2, ![3, 1]) = some 1 ∧
    word.checkedOp (.bin .or) (2, ![2, 1]) = some 3 ∧
    word.checkedOp (.bin .xor) (2, ![3, 1]) = some 2 ∧
    word.checkedOp (.bin .shiftRight) (2, ![6, 1]) = some 3 ∧
    word.checkedOp (.bin .shiftRight) (1, ![6, 1]) = none ∧
    word.checkedOp (.bin .shiftLeft) (3, ![1, 2]) = some 4 ∧
    word.checkedOp (.bin .shiftLeft) (2, ![1, 2]) = none ∧
    word.checkedOp (.bin .shiftLeft) (2, ![0, 100]) = some 0 ∧
    word.checkedOp (.bin .shiftLeft) (2, ![1, 100]) = none ∧
    word.checkedOp (.bin .sub) (2, ![2, 3]) = some 0 ∧
    exactWord.checkedOp (.bin .sub) (2, ![2, 3]) = none ∧
    exactWord.checkedOp (.bin .sub) (2, ![3, 2]) = some 1 ∧
    word.checkedOp (.bin .div) (2, ![3, 0]) = some 0 ∧
    exactWord.checkedOp (.bin .div) (2, ![3, 0]) = none ∧
    exactWord.checkedOp (.bin .div) (2, ![3, 2]) = some 1 ∧
    word.checkedOp (.bin .mod) (2, ![3, 0]) = some 3 ∧
    exactWord.checkedOp (.bin .mod) (2, ![3, 0]) = none ∧
    exactWord.checkedOp (.bin .mod) (2, ![3, 2]) = some 1 := by
  decide

-- Complete native primitive bundles for standard, additive, arithmetic, and exact bases.
example :
    Cslib.WordRAM.checkedAddCertificate.IsPolynomial ∧
    Cslib.WordRAM.Basis.standard.nativePrimitives.IsPolynomial ∧
    Cslib.WordRAM.Basis.additive.nativePrimitives.IsPolynomial ∧
    Cslib.WordRAM.Basis.arithmetic.nativePrimitives.IsPolynomial ∧
    Cslib.WordRAM.Basis.exact.nativePrimitives.IsPolynomial :=
  ⟨NativeCertificate.ofPolyTime_isPolynomial Cslib.WordRAM.checkedAdd_polyTime,
   Cslib.WordRAM.Basis.standard.nativePrimitives_isPolynomial,
   Cslib.WordRAM.Basis.additive.nativePrimitives_isPolynomial,
   Cslib.WordRAM.Basis.arithmetic.nativePrimitives_isPolynomial,
   Cslib.WordRAM.Basis.exact.nativePrimitives_isPolynomial⟩

end ComplexityTests.GenericRAMNative
