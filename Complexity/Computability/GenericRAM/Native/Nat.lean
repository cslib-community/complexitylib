/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Native
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Tactic.PolyTime.Init

/-!
# A certified RAM of bounded natural numbers

This small model has one binary addition operation and one strict-order test. Its runtime
configuration is an exclusive upper bound on values, addresses and control labels. All three
sorts are encoded in binary. Literals and addition results are checked against the bound; tests
reject either out-of-range operand; moves, address extraction and control also check the bound.
The model is intentionally small, to demonstrate every scalar certificate with both accepting
and rejecting inputs. The configuration is a bound, not a binary-encoded word width.

Every certificate handles all configurations and operands with one fixed native machine. This is
a certificate of scalar primitives, not of memory, complete RAM steps or runs.

## Main definitions

* `model`: checked addition RAM with a runtime exclusive bound.
* `encoding`: binary encodings of all three sorts.
* `nativePrimitives`: a complete scalar certificate bundle.

## Main results

* `constant_polyTime`, `operation_polyTime`, `test_polyTime`, `address_polyTime`,
  `validMove_polyTime`, `validPC_polyTime`, `nativePrimitives_isPolynomial`: native
  polynomial-time implementations and bundle polynomiality.

## References

Uses Christian Reitwiessner's binary natural encodings and native machine arithmetic through the
library's plain polynomial-time calculus.
-/

@[expose] public section

namespace Cslib.GenericRAM.BoundedNat

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- Addition and strict comparison with an exclusive bound on values, addresses and labels. -/
abbrev model : Model where
  Value := ℕ
  Address := ℕ
  Config := ℕ
  Const := ℕ
  operations := ⟨Unit, fun _ => 2⟩
  tests := ⟨Unit, fun _ => 2⟩
  constant _ c := some c
  evalOp _ _ args := some (args 0 + args 1)
  evalTest k _ args :=
    if args 0 < k then
      if args 1 < k then some (decide (args 0 < args 1)) else none
    else none
  admissible k v := decide (v < k)
  address k v := if v < k then some v else none
  validMove k v := decide (v < k)
  validPC k pc := decide (pc < k)

/-- Binary encodings of the exclusive bound, stored values and addresses. -/
def encoding : Model.Encoding model := ⟨encNat, encNat, encNat⟩

/-- A literal is checked at every runtime bound, including zero. -/
@[program_certificate]
theorem constant_polyTime (c : ℕ) :
    ComputableInPolyTime (model.checkedConstant c) encNat (encOption encNat) := by
  change ComputableInPolyTime
    (fun k => if decide (c < k) then some c else none) _ _
  simpa only [decide_eq_true_eq, Function.comp_def] using
    (binary_lt.comp ((const c).prod (of_eq (encIn := encNat) fun _ => rfl))).ite_decide
      (const (some c)) (const none)

/-- Addition checks its result before accepting it. -/
@[program_certificate]
theorem operation_polyTime (op : model.operations.Op) :
    ComputableInPolyTime (model.checkedOp op)
      (encPair encNat (encPi encNat)) (encOption encNat) := by
  have hx := (pi_apply encNat (0 : Fin 2)).comp (snd encNat (encPi encNat))
  have hy := (pi_apply encNat (1 : Fin 2)).comp (snd encNat (encPi encNat))
  have hadd := binary_add.comp (hx.prod hy)
  change ComputableInPolyTime
    (fun p : ℕ × (Fin 2 → ℕ) => if decide (p.2 0 + p.2 1 < p.1)
      then some (p.2 0 + p.2 1) else none)
    (encPair encNat (encPi encNat (Index := Fin 2))) (encOption encNat)
  simp only [decide_eq_true_eq]
  exact (binary_lt.comp (hadd.prod (fst encNat (encPi encNat)))).ite_decide
      ((optionSome encNat).comp hadd) (const none)

/-- Tests distinguish a false result from rejection of either invalid operand. -/
theorem test_polyTime (t : model.tests.Op) :
    ComputableInPolyTime (fun p => model.evalTest p.1 t p.2)
      (encPair encNat (encPi encNat)) (encOption encBool) := by
  have hx := (pi_apply encNat (0 : Fin 2)).comp (snd encNat (encPi encNat))
  have hy := (pi_apply encNat (1 : Fin 2)).comp (snd encNat (encPi encNat))
  have hk := fst encNat (encPi encNat (Index := Fin 2))
  exact (binary_lt.comp (hx.prod hk)).ite_decide
    ((binary_lt.comp (hy.prod hk)).ite_decide
      ((optionSome encBool).comp (binary_lt.comp (hx.prod hy))) (const none)) (const none)

/-- Address extraction checks the runtime bound. -/
theorem address_polyTime :
    ComputableInPolyTime (fun p => model.address p.1 p.2)
      (encPair encNat encNat) (encOption encNat) :=
  (binary_lt.comp ((snd encNat encNat).prod (fst encNat encNat))).ite_decide
    ((optionSome encNat).comp (snd encNat encNat)) (const none)

/-- Existing values are checked independently of newly produced values. -/
theorem validMove_polyTime :
    ComputableInPolyTime (fun p => model.validMove p.1 p.2)
      (encPair encNat encNat) encBool :=
  binary_lt.comp ((snd encNat encNat).prod (fst encNat encNat))

/-- Both current and continuing control labels use this checked predicate. -/
theorem validPC_polyTime :
    ComputableInPolyTime (fun p => model.validPC p.1 p.2)
      (encPair encNat encNat) encBool :=
  binary_lt.comp ((snd encNat encNat).prod (fst encNat encNat))

/-- Complete native scalar evidence; no field assumes a RAM simulator. -/
noncomputable def nativePrimitives : model.NativePrimitives encoding where
  constant c := .ofPolyTime (constant_polyTime c)
  operation op := .ofPolyTime (operation_polyTime op)
  test t := .ofPolyTime (test_polyTime t)
  address := .ofPolyTime address_polyTime
  validMove := .ofPolyTime validMove_polyTime
  validPC := .ofPolyTime validPC_polyTime

/-- The bounded-natural primitive bundle has polynomial resource bounds in all fields. -/
theorem nativePrimitives_isPolynomial : nativePrimitives.IsPolynomial where
  constant c := NativeCertificate.ofPolyTime_isPolynomial (constant_polyTime c)
  operation op := NativeCertificate.ofPolyTime_isPolynomial (operation_polyTime op)
  test t := NativeCertificate.ofPolyTime_isPolynomial (test_polyTime t)
  address := NativeCertificate.ofPolyTime_isPolynomial address_polyTime
  validMove := NativeCertificate.ofPolyTime_isPolynomial validMove_polyTime
  validPC := NativeCertificate.ofPolyTime_isPolynomial validPC_polyTime

end Cslib.GenericRAM.BoundedNat
