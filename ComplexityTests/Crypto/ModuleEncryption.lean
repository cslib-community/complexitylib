/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.SIS.ModuleEncryption
import Complexity.Probability.PMF

/-!
# Tests for Ring-LWE and Module-LWE Public-Key Encryption

Concrete evaluations and nonvacuity checks for:
1. Commutativity and associativity of `negacyclicMul`, `rotMatrix_negacyclicMul`, and the
   ring-bilinearity identities `innerPoly_moduleSISMap_eq` and `innerPoly_moduleSISMap_add_sub`.
2. Polynomial message encoding `encodePolyMsg` and centered-lift rounding `decodePolyMsg`,
   including bounded-error recovery `decodePolyMsg_encodePolyMsg_add_noise` and an explicit
   decryption-failure witness when noise exceeds `q / 4`.
3. End-to-end Ring-LWE and Module-LWE key generation, encryption and decryption
   (`moduleLWEKeyGen`, `moduleLWEEncrypt`, `moduleLWEDecrypt`) and the bounded-noise correctness
   theorem `moduleLWEDecrypt_moduleLWEEncrypt_eq`.
4. Embedding of public keys and ciphertexts into `(k + 1) × k` Module-LWE instances
   (`extendPublicKeyMatrix`, `extendCiphertext`, `extendCiphertext_moduleLWEEncrypt`) and the
   two-hop security reduction bounds (`uniformKeyEncryptionLaw_eq_sampleLaw_map`,
   `uniformSample_mask_eq_uniform`, `advantage_realEncryptionView_uniform_le`,
   `advantage_realEncryptionView_msg_le`).
-/

namespace ComplexityTests.Crypto.ModuleEncryption

open Cslib Cslib.Crypto Cslib.Probability
open scoped _root_.Matrix ENNReal NNReal

/-! ### 1. Negacyclic commutativity, associativity and ring bilinearity -/

/-- Concrete check of `negacyclicMul_comm` in `ℤ[X] / (X⁴ + 1)`. -/
example :
    negacyclicMul (![1, 2, -1, 3] : Fin 4 → ℤ) ![2, 0, 1, -2] =
      negacyclicMul (![2, 0, 1, -2] : Fin 4 → ℤ) ![1, 2, -1, 3] := by
  decide

/-- Concrete check of `rotMatrix_negacyclicMul` and `negacyclicMul_assoc` in `ℤ[X] / (X³ + 1)`. -/
example :
    rotMatrix (negacyclicMul (![1, -2, 3] : Fin 3 → ℤ) ![2, 1, -1]) =
      rotMatrix (![1, -2, 3] : Fin 3 → ℤ) * rotMatrix (![2, 1, -1] : Fin 3 → ℤ) := by
  decide

example :
    negacyclicMul (negacyclicMul (![1, -2, 3] : Fin 3 → ℤ) ![2, 1, -1]) ![0, 1, 2] =
      negacyclicMul (![1, -2, 3] : Fin 3 → ℤ)
        (negacyclicMul (![2, 1, -1] : Fin 3 → ℤ) ![0, 1, 2]) := by
  decide

/-- Concrete check of the adjoint identity `innerPoly_moduleSISMap_eq` for a `2 × 2` module matrix
over `ℤ_17[X] / (X² + 1)`. -/
abbrev testMat : Matrix (Fin 2) (Fin 2) (Fin 2 → ZMod 17) :=
  !![![3, 5], ![2, 11]; ![7, 1], ![4, 9]]

abbrev testSecret : Fin 2 → Fin 2 → ZMod 17 :=
  ![![1, -1], ![0, 1]]

abbrev testRandom : Fin 2 → Fin 2 → ZMod 17 :=
  ![![1, 1], ![-1, 0]]

example :
    innerPoly (moduleSISMap testMat testSecret) testRandom =
      innerPoly (moduleSISMap testMat.transpose testRandom) testSecret := by
  decide

/-! ### 2. Polynomial message encoding and centered-lift rounding -/

/-- Over `ZMod 17` (`q / 2 = 8`, `q / 4 = 4`), `encodePolyMsg 17 ![false, true, true, false]`
is `![0, 8, 8, 0]`, and adding error `![3, -3, 3, -2]` (bounded by `B = 3`, with
`4 * 3 + 2 = 14 < 17`) still decodes to `![false, true, true, false]`. -/
example :
    encodePolyMsg 17 ![false, true, true, false] = (![0, 8, 8, 0] : Fin 4 → ZMod 17) := by
  decide

example :
    decodePolyMsg
      (encodePolyMsg 17 ![false, true, true, false] +
        fun i => ((![3, -3, 3, -2] : Fin 4 → ℤ) i : ZMod 17)) =
      ![false, true, true, false] :=
  decodePolyMsg_encodePolyMsg_add_noise (B := 3) (by decide)
    ![false, true, true, false] (by decide)

/-- Boundary failure witness: when the error reaches `5 > 17 / 4 = 4`, an encoded `false` bit (`0`)
is perturbed to `5` and decodes to `true`. -/
example :
    decodePolyMsg (encodePolyMsg 17 ![false] + ![5]) = ![true] := by
  decide

/-! ### 3. End-to-end Ring-LWE / Module-LWE encryption and bounded-noise correctness -/

/-- Concrete parameters with module rank `k = 1`, ring degree `n = 2`, modulus `q = 29`, and
norm bounds `B_s = B_r = B_e = 1`, satisfying `4 * (2 * 1 * 2 * 1 * 1 + 1) + 2 = 22 < 29`. -/
abbrev rlweA : Matrix (Fin 1) (Fin 1) (Fin 2 → ZMod 29) :=
  !![![11, 7]]

abbrev rlweS : Fin 1 → Fin 2 → ZMod 29 := ![![1, -1]]
abbrev rlweE : Fin 1 → Fin 2 → ZMod 29 := ![![1, 0]]
abbrev rlweR : Fin 1 → Fin 2 → ZMod 29 := ![![-1, 1]]
abbrev rlweE₁ : Fin 1 → Fin 2 → ZMod 29 := ![![0, -1]]
abbrev rlweE₂ : Fin 2 → ZMod 29 := ![1, -1]

/-- Checked application of `moduleLWEDecrypt_moduleLWEEncrypt_eq` for all four `2`-bit messages
over `ℤ_29[X] / (X² + 1)`. -/
example (m : Fin 2 → Bool) :
    moduleLWEDecrypt rlweS
      (moduleLWEEncrypt (moduleLWEKeyGen rlweA rlweS rlweE) rlweR rlweE₁ rlweE₂ m) = m :=
  moduleLWEDecrypt_moduleLWEEncrypt_eq (B_s := 1) (B_r := 1) (B_e := 1)
    (le_refl 1) (by decide) rlweA (by decide) (by decide) (by decide) (by decide) (by decide) m

/-- Concrete `k = 2, n = 2, q = 41` Module-LWE instance
(`4 * (2 * 2 * 2 * 1 * 1 + 1) + 2 = 38 < 41`). -/
abbrev mlweA : Matrix (Fin 2) (Fin 2) (Fin 2 → ZMod 41) :=
  !![![13, 4], ![7, 22]; ![5, 19], ![31, 2]]

abbrev mlweS : Fin 2 → Fin 2 → ZMod 41 := ![![1, -1], ![1, 0]]
abbrev mlweE : Fin 2 → Fin 2 → ZMod 41 := ![![0, 1], ![-1, 1]]
abbrev mlweR : Fin 2 → Fin 2 → ZMod 41 := ![![1, 1], ![-1, 0]]
abbrev mlweE₁ : Fin 2 → Fin 2 → ZMod 41 := ![![1, 0], ![0, -1]]
abbrev mlweE₂ : Fin 2 → ZMod 41 := ![-1, 1]

example :
    moduleLWEDecrypt mlweS
      (moduleLWEEncrypt (moduleLWEKeyGen mlweA mlweS mlweE)
        mlweR mlweE₁ mlweE₂ ![true, false]) = ![true, false] :=
  moduleLWEDecrypt_moduleLWEEncrypt_eq (B_s := 1) (B_r := 1) (B_e := 1)
    (le_refl 1) (by decide) mlweA (by decide) (by decide) (by decide) (by decide) (by decide)
    ![true, false]

/-! ### 4. `(k + 1) × k` Module-LWE embedding and security reduction checks -/

/-- Concrete check of `extendCiphertext_moduleLWEEncrypt` on the `k = 2, n = 2, q = 41` instance. -/
example :
    let pk := moduleLWEKeyGen mlweA mlweS mlweE
    extendCiphertext (moduleLWEEncrypt pk mlweR mlweE₁ mlweE₂ ![true, false]) =
      ModuleLWE.sample (extendPublicKeyMatrix pk) mlweR (Fin.cons mlweE₂ mlweE₁) +
        Fin.cons (encodePolyMsg 41 ![true, false]) 0 := by
  decide

/-- Checked instantiation of the public-key indistinguishability reduction
`publicKey_indistinguishable_of_decisionModuleLWE`, the `(k + 1) × k` ciphertext embedding
reduction `uniformKeyEncryptionLaw_eq_sampleLaw_map`, and the two-hop CPA security bounds
`advantage_realEncryptionView_uniform_le` and `advantage_realEncryptionView_msg_le`. -/
example (k n q : ℕ → ℕ) [∀ κ, NeZero (q κ)]
    (noise : (κ : ℕ) → PMF (Fin (n κ) → ZMod (q κ)))
    (hMLWE : DecisionModuleLWE k k n q noise) :
    ComputationallyIndistinguishable
      (fun s => (moduleLWEPublicKeyLaw (k s) (n s) (q s) (noise s)).map ModuleLWE.encodeSample)
      (ModuleLWE.uniformEnsemble k k n q) :=
  publicKey_indistinguishable_of_decisionModuleLWE k n q noise hMLWE

example {k n q : ℕ} [NeZero q] (noise : PMF (Fin n → ZMod q)) (m : Fin n → Bool) :
    uniformKeyEncryptionLaw k n q noise m =
      (ModuleLWE.sampleLaw (k + 1) k n q noise).map (maskExtendedSampleEquiv m) :=
  uniformKeyEncryptionLaw_eq_sampleLaw_map k n q noise m

example {k n q : ℕ} [NeZero q] (noise : PMF (Fin n → ZMod q))
    (m₀ m₁ : Fin n → Bool)
    (D : ModuleLWEPublicKey k n q × ModuleLWECiphertext k n q → Game) :
    Game.advantage
      ((realEncryptionView k n q noise m₀).bind D)
      ((realEncryptionView k n q noise m₁).bind D) ≤
    Game.advantage
      ((realEncryptionView k n q noise m₀).bind D)
      ((uniformEncryptionView k n q).bind D) +
    Game.advantage
      ((realEncryptionView k n q noise m₁).bind D)
      ((uniformEncryptionView k n q).bind D) :=
  advantage_realEncryptionView_msg_le noise m₀ m₁ D

end ComplexityTests.Crypto.ModuleEncryption
