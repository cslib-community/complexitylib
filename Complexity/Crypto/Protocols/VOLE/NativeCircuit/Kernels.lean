/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.VOLE.NativeCircuit.Layout
public import Complexity.Crypto.Protocols.VOLE.CircuitPrivacy
import Complexity.Foundations.Data.List.OfFn

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

/-- List representation of the actual first message, including every linear mask opening. -/
def firstToLists (C : Circuit (arithSignature F) (p + k) m)
    (first : (Fin (p + k + C.size) → F) × ((Fin p ⊕ Fin C.size ⊕ Fin m) → F)) : First F :=
  (List.ofFn first.1, rowsToList first.2)

/-- Sender-local first-message agreement for every assignment and masks. No output relation or
receiver key is used. The fresh final mask coordinate is omitted from the corrections. -/
theorem senderFirst_inputOfCircuit (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool) (a : Fin (p + k + C.size) → F)
    (u v : Fin (p + k + C.size + 1) → F) :
    senderFirst (inputOfCircuit C x y z) (List.ofFn a) (List.ofFn u, List.ofFn v) =
      firstToLists C (voleCommitWitness a (Fin.init u), circuitLinearCoeffs C *ᵥ Fin.init v) := by
  apply Prod.ext
  · change List.zipWith (· - ·) (List.ofFn a) (List.ofFn u) = _
    apply List.ext_getElem (by simp [firstToLists])
    intro i hi hi'
    simp only [firstToLists, List.getElem_zipWith, List.getElem_ofFn, voleCommitWitness,
      Pi.sub_apply, Fin.init]
    rfl
  · exact linearValues_eq C x y z (Fin.init v) (List.ofFn v) fun i => by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
        Nat.lt_succ_of_lt i.isLt, ↓reduceDIte, Option.getD_some, Fin.init]
      rfl

/-- Correctly sized typed inputs and sender shares pass native initialization for every witness. -/
theorem senderInit_inputOfCircuit (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool) (w : Fin k → F)
    (u v : Fin (p + k + C.size + 1) → F) :
    senderInit (inputOfCircuit C x y z) (List.ofFn w) (List.ofFn u, List.ofFn v) =
      some (List.ofFn (circuitTrace C x w),
        firstToLists C (voleCommitWitness (circuitTrace C x w) (Fin.init u),
          circuitLinearCoeffs C *ᵥ Fin.init v)) := by
  have hvalid : (validInput (inputOfCircuit C x y z) &&
      decide ((List.ofFn w).length = (inputOfCircuit C x y z).1) &&
      decide ((List.ofFn u).length = wireCount (inputOfCircuit C x y z) + 1) &&
      decide ((List.ofFn v).length = wireCount (inputOfCircuit C x y z) + 1)) = true := by
    rw [validInput_inputOfCircuit, wireCount_inputOfCircuit]
    simp [inputOfCircuit]
  rw [senderInit, ite_eq_left hvalid, trace_inputOfCircuit C x y z w]
  dsimp only
  rw [senderFirst_inputOfCircuit C x y z]

/-- The receiver's adjusted tags agree with the existing finite-vector correction operation. -/
theorem adjusted_inputOfCircuit (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool) (delta : F)
    (q : Fin (p + k + C.size + 1) → F) (d : Fin (p + k + C.size) → F) :
    adjusted (inputOfCircuit C x y z) (delta, List.ofFn q) (List.ofFn d) =
      List.ofFn (voleAdjustReceiver (Fin.init q) d delta) := by
  simp only [adjusted, wireCount_inputOfCircuit]
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp only [List.getElem_zipWith, List.getElem_take, List.getElem_ofFn,
    voleAdjustReceiver, Fin.init]
  rfl

/-- The witness-free native reconstruction is the existing public first-message map. -/
theorem publicFirst_inputOfCircuit (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool) (delta : F)
    (q : Fin (p + k + C.size + 1) → F) (d : Fin (p + k + C.size) → F) :
    publicFirst (inputOfCircuit C x y z) (delta, List.ofFn q) (List.ofFn d) =
      firstToLists C (circuitPublicFirst C (x, y) (delta, q) d) := by
  apply Prod.ext
  · rfl
  change List.zipWith (fun value target => value - target * delta)
    (linearValues (inputOfCircuit C x y z)
      (adjusted (inputOfCircuit C x y z) (delta, List.ofFn q) (List.ofFn d)))
    (targets (inputOfCircuit C x y z)) = _
  rw [adjusted_inputOfCircuit, targets_inputOfCircuit]
  rw [linearValues_eq C x y z (voleAdjustReceiver (Fin.init q) d delta) _ (fun i => by simp)]
  simp [firstToLists, circuitPublicFirst, rowsToList, List.zipWith_append, List.zipWith_ofFn]

/-- The native reply implements the existing affine-mask reply, with weights in code order.
This identity holds for every assignment, including false multiplication claims. -/
theorem senderReply_inputOfCircuit (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool) (a : Fin (p + k + C.size) → F)
    (u v : Fin (p + k + C.size + 1) → F) (r : CircuitMulGate C → F) :
    senderReply (inputOfCircuit C x y z) (List.ofFn a) (List.ofFn u, List.ofFn v)
      (List.ofFn (r ∘ mulIndexEquiv C)) =
      maskedMulCheckReply (fun i => circuitMulInput C i 0) (fun i => circuitMulInput C i 1)
        (circuitMulOutput C) a u v r := by
  have ha (i : Fin (p + k + C.size)) : (List.ofFn a).getD i.val 0 = a i := by simp
  have hv (i : Fin (p + k + C.size)) :
      (List.ofFn v).getD i.val 0 = v i.castSucc := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      Nat.lt_succ_of_lt i.isLt, ↓reduceDIte, Option.getD_some]
    rfl
  have hlast (v : Fin (p + k + C.size + 1) → F) :
      (List.ofFn v).getD (p + k + C.size) 0 = v (Fin.last _) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      Nat.lt_succ_self, ↓reduceDIte, Option.getD_some]
    rfl
  simp only [senderReply, layout_inputOfCircuit, Native.inputOfMaps, List.length_ofFn,
    Native.weights_ofFn, List.zip_eq_zipWith, List.zipWith_ofFn, List.map_ofFn, List.sum_ofFn,
    wireCount_inputOfCircuit, Function.comp_apply, ha, hv, hlast, maskedMulCheckReply]
  apply Prod.ext
  · dsimp only
    congr 1
    exact (mulIndexEquiv C).sum_comp (fun i => r i *
      voleMulCrossTerm (a (circuitMulInput C i 0)) (v (circuitMulInput C i 0).castSucc)
        (a (circuitMulInput C i 1)) (v (circuitMulInput C i 1).castSucc)
        (v (circuitMulOutput C i).castSucc))
  · dsimp only
    congr 1
    exact (mulIndexEquiv C).sum_comp (fun i => r i *
      voleMulConstTerm (v (circuitMulInput C i 0).castSucc) (v (circuitMulInput C i 1).castSucc))

/-- The list check is the typed multiplication check after the same code-order reindexing. -/
theorem checkValue_inputOfCircuit (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool) (delta : F)
    (q : Fin (p + k + C.size + 1) → F) (d : Fin (p + k + C.size) → F)
    (r : CircuitMulGate C → F) :
    Native.checkValue (layout (inputOfCircuit C x y z)) (delta, List.ofFn q)
      (List.ofFn d) (List.ofFn (r ∘ mulIndexEquiv C)) =
      maskedMulCheckValue (fun i => circuitMulInput C i 0) (fun i => circuitMulInput C i 1)
        (circuitMulOutput C) delta q d r := by
  rw [layout_inputOfCircuit, Native.checkValue_ofFn]
  simp only [maskedMulCheckValue, Function.comp_apply]
  congr 1
  exact (mulIndexEquiv C).sum_comp (fun i => r i *
    ((voleAdjustReceiver (Fin.init q) d delta) (circuitMulInput C i 0) *
        (voleAdjustReceiver (Fin.init q) d delta) (circuitMulInput C i 1) -
      (voleAdjustReceiver (Fin.init q) d delta) (circuitMulOutput C i) * delta))

variable [DecidableEq F]

private theorem rowsToList_all_iff {g : ℕ}
    (a b c : (Fin p ⊕ Fin g ⊕ Fin m) → F) (delta : F) :
    (((rowsToList a).zip (rowsToList b)).zip (rowsToList c)).all
      (fun (row, mask) => decide (row.1 = row.2 * delta + mask)) = true ↔
        ∀ i, a i = b i * delta + c i := by
  simp [rowsToList, List.zipWith_append, List.zip_eq_zipWith, List.zipWith_ofFn,
    List.all_eq_true, Sum.forall]

/-- The native receiver checks the exact existing verifier, including its public linear rows,
for every well-formed typed transcript; no satisfying-witness premise is needed. -/
theorem verify_inputOfCircuit [Finite F] (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool) (delta : F)
    (q : Fin (p + k + C.size + 1) → F)
    (first : (Fin (p + k + C.size) → F) × ((Fin p ⊕ Fin C.size ⊕ Fin m) → F))
    (r : CircuitMulGate C → F) (reply : F × F) :
    verify (inputOfCircuit C x y z) (delta, List.ofFn q) (firstToLists C first)
      (List.ofFn (r ∘ mulIndexEquiv C)) reply =
        circuitVerify C (x, y) (delta, q) first r reply := by
  let _ := Fintype.ofFinite F
  have hrows : (rowsToList first.2).length = p + C.size + m := by simp [rowsToList, Nat.add_assoc]
  have hgates : (layout (inputOfCircuit C x y z)).2.1.length = (mulIndices C).length := by
    rw [layout_inputOfCircuit]
    simp [Native.inputOfMaps]
  rw [Bool.eq_iff_iff]
  simp only [verify, firstToLists, validInput_inputOfCircuit, wireCount_inputOfCircuit,
    rowCount_inputOfCircuit, List.length_ofFn, hrows, hgates, decide_true, Bool.true_and,
    Bool.and_eq_true, decide_eq_true_eq, adjusted_inputOfCircuit, targets_inputOfCircuit,
    checkValue_inputOfCircuit]
  rw [linearValues_eq C x y z (voleAdjustReceiver (Fin.init q) first.1 delta) _ (fun i => by simp),
    rowsToList_all_iff]
  simp only [circuitVerify]
  rw [decide_eq_true_eq]
  simp only [voleVerifyOpening, Function.comp_apply]
  apply and_congr _ Iff.rfl
  exact ((Equiv.sumCongr (Equiv.refl (Fin p)) finSumFinEquiv).trans
    finSumFinEquiv).forall_congr_left

end Cslib.Crypto.Protocols.VOLE.NativeCircuit
