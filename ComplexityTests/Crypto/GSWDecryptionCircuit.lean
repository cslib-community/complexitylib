/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.GSW.DecryptionCircuit.Parameters
import Complexity.Crypto.Computational.Homomorphic.GSW.DecryptionCircuit.PolyTime
import Complexity.Computability.Circuit.Boolean.Layered.Compile.Correctness
import Complexity.Computability.Circuit.Boolean.Layered.Compile.Size

/-! Total raw-input decryption, decoder ties, modular wraparound and uniform native generators. -/

namespace ComplexityTests.Crypto.GSWDecryptionCircuit

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Crypto.Homomorphic
open Cslib.Crypto.Homomorphic.GSW
open Turing.MultiTapeTM

-- A shifted partial product can be prepared for the carry-save reducer through plain APIs.
example : ComputableInPolyTime (fun p : ℕ × ℕ =>
    pairWithZeroCode (p.1 + p.1) p.1 (Modular.partialProductCode p.1 p.2))
    (encPair encUnary encUnary) encCode :=
  computableInPolyTime_pairWithZeroCode (by fun_prop) (by fun_prop)
    Modular.computableInPolyTime_partialProductCode

-- The reducer charges a runtime-supplied complete leaf list and a binary input arity.
example : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × List (List (Op × List ℕ) × List ℕ) =>
      sumPairsCode p.1.1 p.1.2 p.2)
    (encPair (encPair encNat encUnary) (encList encCode)) encCode :=
  computableInPolyTime_sumPairsCode
    ((ComputableInPolyTime.fst encNat encUnary).comp
      (ComputableInPolyTime.fst _ _))
    ((ComputableInPolyTime.snd encNat encUnary).comp
      (ComputableInPolyTime.fst _ _))
    (ComputableInPolyTime.snd _ _)

private def secret : List Bool := [true, false]
-- Selected row is row 1. Its words are 3 and 2; secret 1 gives phase 1 (the lower tie).
private def lowerTie : List Bool :=
  [false, false, false, false, true, true, false, true,
    false, false, false, false, false, false, false, false]
-- Words 1 and 2 give phase -1 = 3 modulo 4 (the excluded upper tie).
private def upperTie : List Bool :=
  [false, false, false, false, true, false, false, true,
    false, false, false, false, false, false, false, false]

example : (DecryptionCircuit.circuit 1 2).eval interpretation
    (BitString.ofList 18 (secret ++ lowerTie)) 0 = true := by
  rw [DecryptionCircuit.correct 1 2 secret lowerTie rfl rfl]
  decide

example : (DecryptionCircuit.circuit 1 2).eval interpretation
    (BitString.ofList 18 (secret ++ upperTie)) 0 = false := by
  rw [DecryptionCircuit.correct 1 2 secret upperTie rfl rfl]
  decide

-- Width one uses the sole phase bit, and zero width has the actual total false semantics.
example : (DecryptionCircuit.circuit 1 1).eval interpretation
    (BitString.ofList 5 ([false] ++ [true, true, false, false])) 0 = true := by
  rw [DecryptionCircuit.correct 1 1 [false] [true, true, false, false] rfl rfl]
  decide

example : (DecryptionCircuit.circuit 4 0).eval interpretation (BitString.ofList 0 []) 0 =
    false := by
  rw [show ([] : List Bool) = [] ++ [] from rfl,
    DecryptionCircuit.correct 4 0 [] [] rfl rfl]
  decide

example : (BitString.equivFin 2 ((Modular.multiply 2).eval interpretation
    (Fin.append ![true, true] ![true, true])) : ℕ) = 1 := by
  rw [Modular.val_eval_multiply]
  decide

example : (BitString.equivFin 2 ((Modular.subtract 2).eval interpretation
    (Fin.append ![true, false] ![false, true])) : ℕ) = 3 := by
  rw [Modular.val_eval_subtract]
  decide

-- Empty and zero-width arrays are included in the same arithmetic theorem.
example : (BitString.equivFin 3 ((Modular.innerProduct 0 3).eval interpretation
    (Fin.append Fin.elim0 Fin.elim0)) : ℕ) = 0 := by
  rw [Modular.val_eval_innerProduct]
  simp

example : ComputableInPolyTime (fun security =>
    DecryptionCircuit.code (Parameters.dimension security) (DepthParameters.width security))
    encUnary encCode := by
  change ComputableInPolyTime
    ((fun p : ℕ × ℕ => DecryptionCircuit.code p.1 p.2) ∘
      fun security => (Parameters.dimension security, DepthParameters.width security))
    encUnary encCode
  exact DecryptionCircuit.computableInPolyTime_code.comp
    (Parameters.computableInPolyTime_dimension.prod
      DepthParameters.computableInPolyTime_width)

example :
    DecryptionCircuit.code 1 2 = (DecryptionCircuit.circuit 1 2).code ∧
      (Layered.compile
        (DecryptionCircuit.inputWidth (Parameters.dimension 2) (DepthParameters.width 2) +
          DecryptionCircuit.inputWidth (Parameters.dimension 2) (DepthParameters.width 2))
        (augmentNand (DecryptionCircuit.circuit (Parameters.dimension 2)
          (DepthParameters.width 2))).code).1.length ≤ DepthParameters.depthBudget 2 :=
  ⟨DecryptionCircuit.code_eq_code 1 2, DecryptionCircuit.layers_augment_le_depthBudget 2⟩

example : Layered.select (Layered.eval (secret ++ lowerTie)
    (Layered.compile 18 (DecryptionCircuit.circuit 1 2).code).1)
    (Layered.compile 18 (DecryptionCircuit.circuit 1 2).code).2 = [true] := by
  have h := Layered.select_eval_compile (DecryptionCircuit.circuit 1 2)
    (BitString.ofList 18 (secret ++ lowerTie))
  have hv : (DecryptionCircuit.circuit 1 2).eval interpretation
      (BitString.ofList 18 (secret ++ lowerTie)) 0 = true := by
    rw [DecryptionCircuit.correct 1 2 secret lowerTie rfl rfl]
    decide
  have he : List.ofFn (BitString.ofList (DecryptionCircuit.inputWidth 1 2)
      (secret ++ lowerTie)) = secret ++ lowerTie := BitString.ofFn_ofList rfl
  rw [he] at h
  simpa only [List.ofFn_succ, List.ofFn_zero, List.map_nil, List.cons_append,
    List.nil_append, hv] using h

-- The compiler's full encoded-size bound applies to the actual augmented circuit, not a
-- supplied bound field. Its depth and gate count have the independent explicit bounds above.
example :
    let D := augmentNand (DecryptionCircuit.circuit 1 2)
    let width := DecryptionCircuit.inputWidth 1 2 + DecryptionCircuit.inputWidth 1 2 + 3 * D.size
    let bits := Nat.log2 width + 1
    (Layered.encCompiled (Layered.compile
      (DecryptionCircuit.inputWidth 1 2 + DecryptionCircuit.inputWidth 1 2) D.code)).length ≤
      4 * D.depth * (2 * width * (6 * bits + 21) + 1) + (2 * bits + 1) + 1 :=
  by simpa only [one_mul] using
    Layered.length_encCompiled_compile_le (augmentNand (DecryptionCircuit.circuit 1 2))

end ComplexityTests.Crypto.GSWDecryptionCircuit
