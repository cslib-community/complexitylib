/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.VOLE.NativeCircuit.Basic
public import Complexity.Crypto.Protocols.VOLE.Circuit
import Mathlib.Data.List.NodupEquivFin

/-!
# Canonical arithmetic-code layout for native VOLE

The public validator is exactly the existing circuit decoder's acceptance condition. Typed
circuits are serialized with their existing code, and multiplication gates retain actual code
order through a filtered finite list, not an arbitrary finite-type enumeration.

## Main definitions

* `NativeCircuit.inputOfCircuit`: the existing typed circuit as runtime input.
* `NativeCircuit.mulIndices`: multiplication gate indices in code order.
* `NativeCircuit.mulIndexEquiv`: the code-order bijection to existing multiplication gates.

## Main results

* `NativeCircuit.validInput_iff`: exact existing decoder acceptance.
* `NativeCircuit.validInput_inputOfCircuit`: every serialized typed circuit is accepted.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.VOLE.NativeCircuit

open Circuits

variable {F : Type} {p k m : ℕ}

/-- The executable predicate is precisely the existing decoder's accepted raw circuit codes. -/
theorem validInput_iff (input : Input F) :
    validInput input = true ↔
      (Circuit.ofCode (inputCount input) input.2.2.2.1.length input.2.1 :
        Option (Circuit (arithSignature F) _ _)).isSome := by
  rw [Circuit.isSome_ofCode_iff]
  simp only [validInput, Bool.and_eq_true, codeCheck_eq_true_iff, List.all_eq_true, wireCount,
    decide_eq_true_eq, and_assoc]

/-- Serialize the existing circuit and public statement, retaining runtime auxiliary input. -/
def inputOfCircuit (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool) : Input F :=
  (k, C.code, List.ofFn x, List.ofFn y, z)

@[simp] theorem inputCount_inputOfCircuit (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool) :
    inputCount (inputOfCircuit C x y z) = p + k := by
  simp [inputCount, inputOfCircuit]

@[simp] theorem wireCount_inputOfCircuit (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool) :
    wireCount (inputOfCircuit C x y z) = p + k + C.size := by
  simp only [wireCount, inputOfCircuit, inputCount, List.length_ofFn]
  rw [Circuit.length_code_fst C]

@[simp] theorem rowCount_inputOfCircuit (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool) :
    rowCount (inputOfCircuit C x y z) = p + C.size + m := by
  simp only [rowCount, inputOfCircuit, List.length_ofFn]
  rw [Circuit.length_code_fst C]

/-- Correct serialization passes public validation without assuming a satisfying witness. -/
theorem validInput_inputOfCircuit (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool) :
    validInput (inputOfCircuit C x y z) = true := by
  rw [validInput_iff]
  simp only [inputOfCircuit, inputCount, List.length_ofFn]
  rw [Circuit.ofCode_code C]
  rfl

private def isMul : ArithOp F → Bool
  | .mul => true
  | _ => false

/-- Multiplication indices filtered from the actual increasing list of gate indices. -/
def mulIndices (C : Circuit (arithSignature F) (p + k) m) : List (Fin C.size) :=
  (List.finRange C.size).filter fun i => isMul (C.program.lines i).op

@[simp] theorem mem_mulIndices (C : Circuit (arithSignature F) (p + k) m) (i : Fin C.size) :
    i ∈ mulIndices C ↔ (C.program.lines i).op = .mul := by
  cases he : (C.program.lines i).op <;> simp [mulIndices, isMul, he]

/-- Filtering gate order introduces no duplicate gate occurrences. -/
theorem nodup_mulIndices (C : Circuit (arithSignature F) (p + k) m) :
    (mulIndices C).Nodup :=
  (List.nodup_finRange C.size).filter _

/-- Existing list-index/element equivalence, restricted to multiplication gates. Both directions
use the actual filtered code order, independently of any `Fintype` enumeration of the subtype. -/
def mulIndexEquiv (C : Circuit (arithSignature F) (p + k) m) :
    Fin (mulIndices C).length ≃ CircuitMulGate C :=
  (List.Nodup.getEquiv (mulIndices C) (nodup_mulIndices C)).trans
    (Equiv.subtypeEquivRight (mem_mulIndices C))

end Cslib.Crypto.Protocols.VOLE.NativeCircuit
