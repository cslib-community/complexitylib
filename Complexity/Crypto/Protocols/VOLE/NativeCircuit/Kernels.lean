/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.VOLE.NativeCircuit.Layout
public import Complexity.Crypto.Protocols.VOLE.CircuitPrivacy

/-!
# Agreement of native and typed circuit kernels

The existing typed circuit code supplies the trace and sparse-row interpretation. These kernel
identities do not assume that the claimed public output is correct. Only reconstruction of
honest linear openings for simulation uses the satisfying trace relation.

## Main definitions

* `NativeCircuit.rowsToList`: public-input, gate and output rows in the transmitted list order.

## Main results

* `NativeCircuit.trace_inputOfCircuit`: actual native trace equals the typed trace.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.VOLE.NativeCircuit

open Circuits
open scoped Matrix

variable {F : Type} {p k m : ℕ} [CommRing F]

/-- The existing sum-indexed rows in public-input, gate and public-output order. -/
def rowsToList {g : ℕ} (rows : (Fin p ⊕ Fin g ⊕ Fin m) → F) : List F :=
  List.ofFn (fun i => rows (.inl i)) ++ List.ofFn (fun i => rows (.inr (.inl i))) ++
    List.ofFn (fun i => rows (.inr (.inr i)))

/-- Runtime native evaluation is the existing typed trace, with no true-output hypothesis. -/
theorem trace_inputOfCircuit (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool) (w : Fin k → F) :
    trace (inputOfCircuit C x y z) (List.ofFn w) = List.ofFn (circuitTrace C x w) := by
  simp only [trace, inputOfCircuit, Circuit.code, ← List.ofFn_fin_append]
  rw [Program.evalCode_code]
  conv_rhs => rw [List.ofFn_add]
  apply congrArg₂ List.append
  · apply congrArg List.ofFn
    funext i
    change Fin.append x w i = circuitTrace C x w (Fin.castAdd C.size i)
    simp [circuitTrace, Wire.equiv, Program.trace]
  · apply congrArg List.ofFn
    funext i
    simp [circuitTrace, Wire.equiv, Program.trace]

/-- The public target list is the existing target vector in transmitted row order. -/
theorem targets_inputOfCircuit (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool) :
    targets (inputOfCircuit C x y z) = rowsToList (circuitLinearTargets C x y) := by
  simp only [targets, inputOfCircuit, rowsToList, circuitLinearTargets, Circuit.code,
    Program.code_eq_ofFn_lines, Line.code, List.map_ofFn]
  rfl

/-- Sparse row evaluation agrees whenever the actual list has the specified values on all
circuit wires. Extra trailing values, such as the fresh mask coordinate, are never read. -/
theorem linearValues_eq (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool)
    (a : Fin (p + k + C.size) → F) (values : List F)
    (hvalues : ∀ i : Fin (p + k + C.size), values.getD i.val 0 = a i) :
    linearValues (inputOfCircuit C x y z) values =
      rowsToList (circuitLinearCoeffs C *ᵥ a) := by
  have hwire (w : Wire (p + k) C.size) :
      values.getD w.toNat 0 = a (Wire.equivFin (p + k) C.size w) :=
    hvalues (Wire.equivFin (p + k) C.size w)
  simp only [linearValues, inputOfCircuit, List.length_ofFn, rowsToList]
  apply congrArg₂ List.append
  · apply congrArg₂ List.append
    · rw [Native.weights_eq_ofFn]
      apply congrArg List.ofFn
      funext i
      simpa [circuitLinearCoeffs, Matrix.mulVec, Wire.equiv] using
        hvalues (Fin.castAdd C.size (Fin.castAdd k i))
    · simp only [Circuit.code, Program.code_eq_ofFn_lines]
      apply List.ext_getElem (by simp)
      intro i hi hi'
      simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_ofFn]
      rcases he : C.program.lines ⟨i, by simpa using hi'⟩ with ⟨op, wires⟩
      have hout := hwire (.gate ⟨i, by simpa using hi'⟩)
      simp only [Wire.toNat_gate, Wire.equivFin_gate, List.getD_eq_getElem?_getD] at hout
      cases op with
      | add =>
        have h₀ := hwire (wires 0)
        have h₁ := hwire (wires 1)
        simp only [Wire.toNat, Wire.equivFin, Equiv.trans_apply, Wire.equiv,
          List.getD_eq_getElem?_getD] at h₀ h₁
        simpa [Line.code, circuitLinearCoeffs, he, Matrix.mulVec, inputCount,
          hout, Wire.toNat, Wire.equivFin, Wire.equiv, dotProduct,
          Finset.sum_add_distrib, Finset.sum_sub_distrib, add_mul, sub_mul, Pi.single_apply]
          using congrArg₂ (· + ·) h₀ h₁
      | mul => simp [Line.code, circuitLinearCoeffs, he, Matrix.mulVec]
      | const c =>
        simp [Line.code, circuitLinearCoeffs, he, Matrix.mulVec, inputCount, hout,
          Wire.equiv, dotProduct, Pi.single_apply]
  · simp only [Circuit.code, List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    simpa [circuitLinearCoeffs, Matrix.mulVec, Wire.equivFin] using hwire (C.outputs i)

end Cslib.Crypto.Protocols.VOLE.NativeCircuit
