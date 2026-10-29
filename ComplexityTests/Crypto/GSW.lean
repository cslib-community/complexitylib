/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.GSW.Basic

/-!
Deterministic GSW regressions with modulus 64, one secret coordinate, one public row, and
nonzero noise. Kernel computations check actual ciphertext products independently of the
general correctness theorems. The same fixture satisfies their explicit noise margins.
These tests do not assert sampling, efficiency, security or bootstrappability.
-/

namespace ComplexityTests.GSW

open Cslib.Crypto.Homomorphic.GSW
open scoped Matrix

private def secret : Fin 1 → ZMod (2 ^ 6) := fun _ => 5

private def publicPart : Matrix (Fin 1) (Fin 1) (ZMod (2 ^ 6)) := fun _ _ => 3

private def error : Fin 1 → ℤ := fun _ => 1

private def coins : Matrix (Fin 2 × Fin 6) (Fin 1) Bool := fun _ _ => true

private def ciphertext (μ : Bool) : Ciphertext 1 6 :=
  encryptWithCoins (publicMatrix publicPart secret error) μ coins

private def inputs : List (Bool × Bool) :=
  [(false, false), (false, true), (true, false), (true, true)]

-- The public row is [16, 3], and the secret vector is [1, -5].
example : (publicMatrix publicPart secret error 0 0).val = 16 ∧
    (publicMatrix publicPart secret error 0 1).val = 3 ∧
    (secretVector secret 0).val = 1 ∧ (secretVector secret 1).val = 59 := by
  decide +kernel

-- Actual fresh products at the selected coordinate are the encoded bits plus one.
example : [false, true].map (fun μ =>
    ((bitMatrix (ZMod (2 ^ 6)) (ciphertext μ) *ᵥ
      powersOfTwo 6 (secretVector secret)) (0, 5)).val) = [1, 33] := by
  decide +kernel

example : [false, true].map (fun μ => decrypt secret (ciphertext μ)) = [false, true] := by
  decide +kernel

-- Every coordinate, rather than just the selected one, has the claimed fresh integer error.
example : ∀ i, encryptionError coins error i = 1 := by decide +kernel

example (μ : Bool) : decrypt secret (ciphertext μ) = μ :=
  decrypt_encryptWithCoins (bound := 1) publicPart secret error μ coins
    (by decide) (by decide +kernel) (by decide)

-- This table is computed from the actual matrix NAND and flattening algorithms.
example : inputs.map (fun (μ₁, μ₂) =>
    ((bitMatrix (ZMod (2 ^ 6)) (nand (ciphertext μ₁) (ciphertext μ₂)) *ᵥ
      powersOfTwo 6 (secretVector secret)) (0, 5)).val) = [29, 28, 28, 59] := by
  decide +kernel

example : inputs.map (fun (μ₁, μ₂) =>
    decrypt secret (nand (ciphertext μ₁) (ciphertext μ₂))) =
      [true, true, true, false] := by
  decide +kernel

-- The true/true result has negative error -5; its canonical residue wraps to 59.
example : inputs.map (fun (μ₁, μ₂) =>
    nandError (ciphertext μ₁) μ₂ (encryptionError coins error)
      (encryptionError coins error) (0, 5)) = [-3, -4, -4, -5] := by
  decide +kernel

-- The generic coarse bound is 1 + 12 * 1 = 13 at every coordinate for all four inputs.
example (μ₁ μ₂ : Bool) (i : Fin 2 × Fin 6) :
    (nandError (ciphertext μ₁) μ₂ (encryptionError coins error)
      (encryptionError coins error) i).natAbs ≤ 13 := by
  simpa using nandError_natAbs_le (ciphertext μ₁) μ₂
    (encryptionError coins error) (encryptionError coins error)
    (bound₁ := 1) (bound₂ := 1) (by decide +kernel) (by decide +kernel) i

example : 4 * 13 < 2 ^ 6 := by decide

example (μ₁ μ₂ : Bool) :
    decrypt secret (nand (ciphertext μ₁) (ciphertext μ₂)) = !(μ₁ && μ₂) :=
  decrypt_nand (bound₁ := 1) (bound₂ := 1) secret (ciphertext μ₁) (ciphertext μ₂)
    μ₁ μ₂ (encryptionError coins error) (encryptionError coins error)
    (encryptWithCoins_hasError publicPart secret error μ₁ coins)
    (encryptWithCoins_hasError publicPart secret error μ₂ coins)
    (by decide) (by decide +kernel) (by decide +kernel) (by decide)

-- Negative fresh noise wraps zero to 63 and moves the encoded one to 31.
example : [false, true].map (fun μ =>
    ((bitMatrix (ZMod (2 ^ 6))
      (encryptWithCoins (publicMatrix publicPart secret (fun _ => -1)) μ coins) *ᵥ
        powersOfTwo 6 (secretVector secret)) (0, 5)).val) = [63, 31] := by
  decide +kernel

example : [false, true].map (fun μ => decrypt secret
    (encryptWithCoins (publicMatrix publicPart secret (fun _ => -1)) μ coins)) =
      [false, true] := by
  decide +kernel

-- Both quarter boundaries are explicit: the lower tie is included, the upper tie excluded.
example : ([1, 2, 5, 6] : List (ZMod (2 ^ 3))).map (decode 3) =
    [false, true, true, false] := by
  decide +kernel

example (μ : Bool) : decode 1
    (((μ.toNat : ℤ) * 2 ^ (1 - 1) + 0 : ℤ) : ZMod (2 ^ 1)) = μ :=
  decode_eq_of_error (w := 1) (by decide) μ 0 (by decide)

example : ([0, 1] : List (ZMod (2 ^ 1))).map (decode 1) = [false, true] := by
  decide +kernel

-- Width zero is a valid algebraic case, but its decoder deliberately always returns false.
example :
    bitCompose 0 (fun j => ((bitDecomp 0 (fun _ : Fin 1 => (0 : ZMod (2 ^ 0))) j).toNat :
      ZMod (2 ^ 0))) = (fun _ => 0) ∧
    decode 0 (0 : ZMod (2 ^ 0)) = false :=
  ⟨bitCompose_bitDecomp 0 (fun _ => 0), by decide +kernel⟩

example (μ : Bool) : decrypt (n := 0) (w := 0) (fun _ => 0)
    (encryptWithCoins (m := 0) (fun _ _ => 0) μ (fun _ _ => false)) = false := rfl

-- Flattening must accept arbitrary modular coefficients, not just zero and one.
private def nonbinary : Matrix (Fin 1) (Fin 1 × Fin 3) (ZMod (2 ^ 3)) :=
  fun _ j => if j.2 = 0 then 3 else if j.2 = 1 then 5 else 7

example : [0, 1, 2].map (fun j : Fin 3 => flattenMatrix 3 nonbinary 0 (0, j)) =
    [true, false, false] := by
  decide +kernel

example : (bitMatrix (ZMod (2 ^ 3)) (flattenMatrix 3 nonbinary) *ᵥ
    powersOfTwo 3 (fun _ : Fin 1 => 3)) 0 = 3 ∧
    (nonbinary *ᵥ powersOfTwo 3 (fun _ : Fin 1 => 3)) 0 = 3 ∧
    bitMatrix (ZMod (2 ^ 3)) (flattenMatrix 3 nonbinary) *ᵥ
      powersOfTwo 3 (fun _ : Fin 1 => 3) =
      nonbinary *ᵥ powersOfTwo 3 (fun _ : Fin 1 => 3) := by
  refine ⟨?_, ?_, flattenMatrix_mulVec 3 nonbinary (fun _ => 3)⟩ <;> decide +kernel

end ComplexityTests.GSW
