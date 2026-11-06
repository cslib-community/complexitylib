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
  constructor
  · rintro ⟨hc, hl, hb⟩
    exact ⟨hc, hl, fun i hi => of_decide_eq_true (hb i hi)⟩
  · rintro ⟨hc, hl, hb⟩
    exact ⟨hc, hl, fun i hi => decide_eq_true (hb i hi)⟩

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
  change (Circuit.ofCode ((List.ofFn x).length + k) (List.ofFn y).length C.code).isSome = true
  rw [List.length_ofFn, List.length_ofFn, Circuit.ofCode_code C]
  rfl

/-- Multiplication indices filtered from the actual increasing list of gate indices. -/
def mulIndices (C : Circuit (arithSignature F) (p + k) m) : List (Fin C.size) :=
  (List.finRange C.size).filter fun i => match (C.program.lines i).op with
    | .mul => true
    | _ => false

@[simp] theorem mem_mulIndices (C : Circuit (arithSignature F) (p + k) m) (i : Fin C.size) :
    i ∈ mulIndices C ↔ (C.program.lines i).op = .mul := by
  cases he : (C.program.lines i).op <;> simp [mulIndices, he]

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

private def rawTriple (C : Circuit (arithSignature F) (p + k) m) (i : Fin C.size) :
    ℕ × ℕ × ℕ :=
  ((C.program.lines i).code.2.getD 0 0, (C.program.lines i).code.2.getD 1 0, p + k + i.val)

private theorem code_zipIdx (C : Circuit (arithSignature F) (p + k) m) :
    C.code.1.zipIdx = (List.finRange C.size).map
      (fun i => ((C.program.lines i).code, i.val)) := by
  simp only [Circuit.code, Program.code_eq_ofFn_lines]
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp

private theorem layout_gates (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool) :
    (layout (inputOfCircuit C x y z)).2.1 = (mulIndices C).map (rawTriple C) := by
  change (C.code.1.zipIdx.filterMap fun (gate, i) => match gate.1 with
      | .mul => some (gate.2.getD 0 0, gate.2.getD 1 0,
          inputCount (inputOfCircuit C x y z) + i)
      | _ => none) = _
  rw [inputCount_inputOfCircuit, code_zipIdx, List.filterMap_map]
  rw [mulIndices, ← List.filterMap_eq_map, List.filterMap_filter]
  apply List.filterMap_congr
  intro i hi
  cases he : (C.program.lines i).op <;> simp [Line.code, he, rawTriple]

private theorem rawTriple_eq (C : Circuit (arithSignature F) (p + k) m)
    (i : CircuitMulGate C) :
    rawTriple C i.val = ((circuitMulInput C i 0).val, (circuitMulInput C i 1).val,
      (circuitMulOutput C i).val) := by
  rcases he : C.program.lines i.val with ⟨op, wires⟩
  have hop := i.property
  rw [he] at hop
  cases op with
  | add => cases hop
  | const c => cases hop
  | mul => simp [rawTriple, circuitMulInput, circuitMulOutput, he, Line.code, Wire.toNat,
      Wire.equivFin, Wire.equiv]

/-- The native layout enumerates exactly the existing typed multiplication gates in code order. -/
theorem layout_inputOfCircuit (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool) :
    layout (inputOfCircuit C x y z) = Native.inputOfMaps
      (fun i => circuitMulInput C (mulIndexEquiv C i) 0)
      (fun i => circuitMulInput C (mulIndexEquiv C i) 1)
      (fun i => circuitMulOutput C (mulIndexEquiv C i)) z := by
  apply Prod.ext
  · exact wireCount_inputOfCircuit C x y z
  apply Prod.ext
  · rw [layout_gates]
    change (mulIndices C).map (rawTriple C) = List.ofFn _
    conv_lhs => rw [← List.ofFn_get (mulIndices C), List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact rawTriple_eq C (mulIndexEquiv C i)
  · rfl

end Cslib.Crypto.Protocols.VOLE.NativeCircuit
