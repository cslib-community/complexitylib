/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.SIS.ModuleEncryption.Native
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode

/-! One certified implementation handles actual structured key-generation inputs and edges. -/

namespace ComplexityTests.Crypto.ModuleKeyGenNative

open Cslib Cslib.Crypto Turing.MultiTapeTM
open scoped Matrix

private def matrix : Matrix (Fin 2) (Fin 2) (Fin 2 → ZMod 6) :=
  !![![1, 2], ![3, 1]; ![2, 1], ![1, 1]]

private def secret : Fin 2 → Fin 2 → ℤ := ![![-1, 2], ![3, -2]]
private def error : Fin 2 → Fin 2 → ℤ := ![![1, -1], ![-2, 3]]

/-- The expanded codec retains negacyclic off-diagonal blocks; signed wraps are nonzero. -/
example : moduleLWEKeyGen matrix (fun j i => (secret j i : ZMod 6))
    (fun j i => (error j i : ZMod 6)) = (matrix, ![![1, 2], ![5, 1]]) := by decide

/-- All five canonical calls use the same obtained runtime function and certificate. -/
example : ∃ run : (((ℕ × ℕ) × ℕ) × List Bool × List Bool × List Bool) → List Bool,
    ComputableInPolyTime run
      (encPair (encPair (encPair encUnary encUnary) encNat)
        (encPair encBits (encPair encBits encBits))) encBits ∧
    run (((2, 2), 6), (ModuleSIS.encodeMatrix matrix,
      (ModuleSIS.encodeVec secret, ModuleSIS.encodeVec error))) =
      ModuleLWE.encodeSample (matrix, ![![1, 2], ![5, 1]]) ∧
    run (((2, 2), 1), (ModuleSIS.encodeMatrix (0 : Matrix (Fin 2) (Fin 2) (Fin 2 → ZMod 1)),
      (ModuleSIS.encodeVec secret, ModuleSIS.encodeVec error))) =
      ModuleLWE.encodeSample ((0 : Matrix (Fin 2) (Fin 2) (Fin 2 → ZMod 1)), 0) ∧
    run (((0, 2), 6), (ModuleSIS.encodeMatrix (0 : Matrix (Fin 0) (Fin 0) (Fin 2 → ZMod 6)),
      (ModuleSIS.encodeVec (0 : Fin 0 → Fin 2 → ℤ), ModuleSIS.encodeVec (0 : Fin 0 → Fin 2 → ℤ)))) =
      ModuleLWE.encodeSample ((0 : Matrix (Fin 0) (Fin 0) (Fin 2 → ZMod 6)), 0) ∧
    run (((2, 0), 6), (ModuleSIS.encodeMatrix (0 : Matrix (Fin 2) (Fin 2) (Fin 0 → ZMod 6)),
      (ModuleSIS.encodeVec (0 : Fin 2 → Fin 0 → ℤ), ModuleSIS.encodeVec (0 : Fin 2 → Fin 0 → ℤ)))) =
      ModuleLWE.encodeSample ((0 : Matrix (Fin 2) (Fin 2) (Fin 0 → ZMod 6)), 0) ∧
    run (((1, 1), 2 ^ 128 + 1),
      (ModuleSIS.encodeMatrix (0 : Matrix (Fin 1) (Fin 1) (Fin 1 → ZMod (2 ^ 128 + 1))),
        (ModuleSIS.encodeVec (![![2 ^ 128]]), ModuleSIS.encodeVec (![![-1]])))) =
      ModuleLWE.encodeSample
        ((0 : Matrix (Fin 1) (Fin 1) (Fin 1 → ZMod (2 ^ 128 + 1))), ![![-1]]) := by
  obtain ⟨run, hnative, hrun⟩ := exists_computableInPolyTime_moduleLWEKeyGen
  refine ⟨run, hnative, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun 2 2 6 (by decide)]
    congr 1
    decide
  · rw [hrun 2 2 1 (by decide)]
    congr 1
    decide
  · rw [hrun 0 2 6 (by decide)]
    congr 1
  · rw [hrun 2 0 6 (by decide)]
    congr 1
  · rw [hrun 1 1 (2 ^ 128 + 1) (by decide)]
    congr 1
    decide

/-- The reused total framing/number parsers do not assert canonical-input rejection. -/
example : frames [true] = [[]] := by simp [frames, unframe, dropFrame]
example : decodeIntBin [true, false, false] = 0 := by decide
example : (Decoder.list Decoder.nat).decode [true, true] = [1] := by
  change (frames [true, true]).map Decoder.nat.decode = [1]
  rw [frames_of_ne_nil (by decide)]
  simp only [unframe, dropFrame, frames_nil, List.map_cons, List.map_nil]
  rfl

end ComplexityTests.Crypto.ModuleKeyGenNative
