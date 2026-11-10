/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SIS.ModuleEncryption.Native
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode

/-!
# Native Module-LWE Decryption Tests

Concrete evaluations and edge cases for the certified total Module-LWE decryption witness
`exists_computableInPolyTime_moduleLWEDecrypt`.
-/

namespace CslibFrontierTests.Crypto.ModuleEncryptionNative

open Cslib Cslib.Crypto Turing.MultiTapeTM
open scoped Matrix

/-! ### 1. End-to-end decryption with honest encryption -/

private abbrev rlweA : Matrix (Fin 1) (Fin 1) (Fin 2 → ZMod 29) :=
  !![![11, 7]]

private def rlweS : Fin 1 → Fin 2 → ℤ := ![![1, -1]]
private def rlweE : Fin 1 → Fin 2 → ℤ := ![![1, 0]]
private def rlweR : Fin 1 → Fin 2 → ℤ := ![![-1, 1]]
private def rlweE₁ : Fin 1 → Fin 2 → ℤ := ![![0, -1]]
private def rlweE₂ : Fin 2 → ℤ := ![1, -1]

private def rlweCt (m : Fin 2 → Bool) : ModuleLWECiphertext 1 2 29 :=
  moduleLWEEncrypt
    (moduleLWEKeyGen rlweA (fun j i => (rlweS j i : ZMod 29)) (fun j i => (rlweE j i : ZMod 29)))
    (fun j i => (rlweR j i : ZMod 29))
    (fun j i => (rlweE₁ j i : ZMod 29))
    (fun i => (rlweE₂ i : ZMod 29))
    m

/-- Native decryption matches `moduleLWEDecrypt` on honest `k = 1, n = 2, q = 29` ciphertexts. -/
example (m : Fin 2 → Bool) :
    ∃ run : (((ℕ × ℕ) × ℕ) × List Bool × List Bool) → List Bool,
      ComputableInPolyTime run
        (encPair (encPair (encPair encUnary encUnary) encNat)
          (encPair encBits encBits)) encBits ∧
      run (((1, 2), 29), (ModuleSIS.encodeVec rlweS,
        GeneralSIS.encodeMatrix (extendCiphertext (rlweCt m)))) =
        List.ofFn m := by
  obtain ⟨run, hnative, hrun⟩ := exists_computableInPolyTime_moduleLWEDecrypt
  refine ⟨run, hnative, ?_⟩
  rw [hrun 1 2 29 (by decide)]
  have hdec : moduleLWEDecrypt (fun j i => (rlweS j i : ZMod 29)) (rlweCt m) = m := by
    apply moduleLWEDecrypt_moduleLWEEncrypt_eq (B_s := 1) (B_r := 1) (B_e := 1)
      (le_refl 1) (by decide) rlweA (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [hdec]

private abbrev mlweA : Matrix (Fin 2) (Fin 2) (Fin 2 → ZMod 41) :=
  !![![13, 4], ![7, 22]; ![5, 19], ![31, 2]]

private def mlweS : Fin 2 → Fin 2 → ℤ := ![![1, -1], ![1, 0]]
private def mlweE : Fin 2 → Fin 2 → ℤ := ![![0, 1], ![-1, 1]]
private def mlweR : Fin 2 → Fin 2 → ℤ := ![![1, 1], ![-1, 0]]
private def mlweE₁ : Fin 2 → Fin 2 → ℤ := ![![1, 0], ![0, -1]]
private def mlweE₂ : Fin 2 → ℤ := ![-1, 1]

private def mlweCt : ModuleLWECiphertext 2 2 41 :=
  moduleLWEEncrypt
    (moduleLWEKeyGen mlweA (fun j i => (mlweS j i : ZMod 41)) (fun j i => (mlweE j i : ZMod 41)))
    (fun j i => (mlweR j i : ZMod 41))
    (fun j i => (mlweE₁ j i : ZMod 41))
    (fun i => (mlweE₂ i : ZMod 41))
    ![true, false]

example :
    ∃ run : (((ℕ × ℕ) × ℕ) × List Bool × List Bool) → List Bool,
      ComputableInPolyTime run
        (encPair (encPair (encPair encUnary encUnary) encNat)
          (encPair encBits encBits)) encBits ∧
      run (((2, 2), 41), (ModuleSIS.encodeVec mlweS,
        GeneralSIS.encodeMatrix (extendCiphertext mlweCt))) =
        [true, false] := by
  obtain ⟨run, hnative, hrun⟩ := exists_computableInPolyTime_moduleLWEDecrypt
  refine ⟨run, hnative, ?_⟩
  rw [hrun 2 2 41 (by decide)]
  have hdec : moduleLWEDecrypt (fun j i => (mlweS j i : ZMod 41)) mlweCt = ![true, false] := by
    apply moduleLWEDecrypt_moduleLWEEncrypt_eq (B_s := 1) (B_r := 1) (B_e := 1)
      (le_refl 1) (by decide) mlweA (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [hdec]
  rfl

/-! ### 2. Canonical edge dimensions and parameters -/

/-- Rank zero: no public polynomials; decryption evaluates centered threshold on `ct.2`. -/
example :
    ∃ run : (((ℕ × ℕ) × ℕ) × List Bool × List Bool) → List Bool,
      ComputableInPolyTime run
        (encPair (encPair (encPair encUnary encUnary) encNat)
          (encPair encBits encBits)) encBits ∧
      run (((0, 2), 29), (ModuleSIS.encodeVec (0 : Fin 0 → Fin 2 → ℤ),
        GeneralSIS.encodeMatrix (extendCiphertext ((0, ![0, 14]) : ModuleLWECiphertext 0 2 29)))) =
        [false, true] ∧
      run (((1, 0), 29), (ModuleSIS.encodeVec (0 : Fin 1 → Fin 0 → ℤ),
        GeneralSIS.encodeMatrix (extendCiphertext ((0, 0) : ModuleLWECiphertext 1 0 29)))) =
        [] ∧
      run (((1, 2), 1), (ModuleSIS.encodeVec (![![0, 0]]),
        GeneralSIS.encodeMatrix (extendCiphertext ((0, 0) : ModuleLWECiphertext 1 2 1)))) =
        [false, false] := by
  obtain ⟨run, hnative, hrun⟩ := exists_computableInPolyTime_moduleLWEDecrypt
  refine ⟨run, hnative, ?_, ?_, ?_⟩
  · rw [hrun 0 2 29 (by decide)]
    decide
  · rw [hrun 1 0 29 (by decide)]
    rfl
  · rw [hrun 1 2 1 (by decide)]
    decide

/-! ### 3. Threshold edge cases -/

/-- For `q = 29`, `29 / 4 = 7`. A centered difference of `7` decodes to `false`,
while `8` decodes to `true`. -/
example :
    ∃ run : (((ℕ × ℕ) × ℕ) × List Bool × List Bool) → List Bool,
      ComputableInPolyTime run
        (encPair (encPair (encPair encUnary encUnary) encNat)
          (encPair encBits encBits)) encBits ∧
      run (((0, 2), 29), (ModuleSIS.encodeVec (0 : Fin 0 → Fin 2 → ℤ),
        GeneralSIS.encodeMatrix (extendCiphertext ((0, ![7, 8]) : ModuleLWECiphertext 0 2 29)))) =
        [false, true] := by
  obtain ⟨run, hnative, hrun⟩ := exists_computableInPolyTime_moduleLWEDecrypt
  refine ⟨run, hnative, ?_⟩
  rw [hrun 0 2 29 (by decide)]
  decide

/-! ### 4. Malformed and incomplete decoder fallbacks -/

/-- Incomplete framing and noncanonical sign/magnitude words decode safely via total fallbacks. -/
example : decodeIntBin [] = 0 := by decide
example : decodeIntBin [true] = 0 := by decide
example : decodeIntBin [true, false, false] = 0 := by decide

end CslibFrontierTests.Crypto.ModuleEncryptionNative
