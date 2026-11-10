/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Computational.SIS.MLKEM.Security
import CslibFrontier.Crypto.Protocols.KEM.MLKEM

/-!
# Tests for ML-KEM and K-PKE

1. The three FIPS 203 parameter sets and their numeric constraints.
2. Compression at `q = 3329`: `Compress_d ∘ Decompress_d` is the identity, the rounding error
   bound is attained, and one-bit decoding fails once the error passes `q / 4`.
3. A toy K-PKE instance (`n = 2`, `q = 17`, `k = 1`) on which the noise hypothesis of
   `decrypt_encrypt_eq_of_noise_le` holds and decryption recovers both messages.
4. The ML-KEM wrapper on the toy instance: honest decapsulation returns the encapsulated key, a
   tampered ciphertext is implicitly rejected, and the hypotheses of
   `kemDecaps_encrypt_of_noise_le` are satisfiable.
-/

namespace CslibFrontierTests.Crypto.MLKEM

open Cslib Cslib.Crypto Cslib.Crypto.MLKEM Cslib.Crypto.Protocols

/-! ### 1. Parameter sets -/

example : mlkem512.IsStandard ∧ mlkem768.IsStandard ∧ mlkem1024.IsStandard := by decide

example : mlkem1024.k = 4 ∧ mlkem1024.du = 11 ∧ mlkem1024.dv = 5 := by decide

/-- A non-standard rank is rejected. -/
example : ¬ ({ k := 5, η₁ := 2, η₂ := 2, du := 11, dv := 5 } : Params).IsStandard := by decide

example : 2 ^ mlkem768.du < mlkem768.q := by
  obtain ⟨-, -, h, -⟩ := Params.IsStandard.bounds (P := mlkem768) (by decide)
  exact h

/-! ### 2. Compression at `q = 3329` -/

/-- `Compress_1` is `0` up to `832 = ⌊q / 4⌋`, `1` from `833` to `2496`, and `0` again from
`2497`. -/
example : compress 3329 1 832 = 0 ∧ compress 3329 1 833 = 1 ∧ compress 3329 1 2496 = 1 ∧
    compress 3329 1 2497 = 0 := by decide

/-- `Decompress_1(1) = ⌈3329 / 2⌋ = 1665`, rounding up, unlike `encodePolyMsg`'s `1664`. -/
example : decompress 3329 1 1 = 1665 := by decide

example : compress 3329 4 (decompress 3329 4 11) = 11 :=
  compress_decompress (by norm_num) 11

/-- The rounding error bound `⌈3329 / 32⌋ = 104` for `d = 4` is attained at `x = 104`. -/
example : roundDiv 3329 (2 ^ (4 + 1)) = 104 ∧
    (decompress 3329 4 (compress 3329 4 104) - 104).valMinAbs.natAbs = 104 := by decide

example : (decompress 3329 4 (compress 3329 4 2000) - 2000).valMinAbs.natAbs ≤ 104 :=
  natAbs_valMinAbs_decompress_compress_sub_le 4 2000

/-- One-bit decoding tolerates the error `831`, the largest `B` with `4 * B + 2 < 3329` ... -/
example : compress 3329 1 (decompress 3329 1 1 + 831) = 1 :=
  compress_one_decompress_one_add (B := 831) (by norm_num) 1 (by decide)

/-- ... and fails for the errors `832` and `-833`, so the hypothesis cannot be relaxed to
`4 * B < q + 2` at `q = 3329`. -/
example : compress 3329 1 (decompress 3329 1 1 + 832) = 0 ∧
    compress 3329 1 (decompress 3329 1 1 - 833) = 0 := by decide

/-! ### 3. A toy K-PKE instance -/

/-- Toy parameters: `n = 2`, `q = 17`, `k = 1`, `d_u = 4`, `d_v = 3`. -/
def toy : Params := { n := 2, q := 17, k := 1, η₁ := 1, η₂ := 1, du := 4, dv := 3 }

instance : NeZero toy.q := ⟨by decide⟩

def toyA : Matrix (Fin toy.k) (Fin toy.k) (Fin toy.n → ZMod toy.q) := fun _ _ => ![3, 2]
def toyS : SecretKey toy := fun _ => ![1, 0]
def toyE : Fin toy.k → Fin toy.n → ZMod toy.q := fun _ => ![0, 1]
def toyR : Fin toy.k → Fin toy.n → ZMod toy.q := fun _ => ![1, 0]
def toyE₁ : Fin toy.k → Fin toy.n → ZMod toy.q := fun _ => ![0, 1]
def toyE₂ : Fin toy.n → ZMod toy.q := ![1, 0]
def toyPK : PublicKey toy := moduleLWEKeyGen toyA toyS toyE

/-- The noise hypothesis of `decrypt_encrypt_eq_of_noise_le` holds with `B = 3`
(`4 * 3 + 2 < 17`) for both messages. -/
theorem toy_noise_le (m : Fin toy.n → Bool) (i : Fin toy.n) :
    (decryptionNoise toy toyA toyS toyE toyR toyE₁ toyE₂ m i).valMinAbs.natAbs ≤ 3 := by
  revert m i
  decide

example (m : Fin toy.n → Bool) :
    decrypt toy toyS (encrypt toy toyPK m (toyR, toyE₁, toyE₂)) = m :=
  decrypt_encrypt_eq_of_noise_le toy (B := 3) (by decide) toyA toyS toyE toyR toyE₁ toyE₂ m
    (toy_noise_le m)

def toyM : Fin toy.n → Bool := ![true, false]

/-- The same round trip, checked by evaluation. -/
example : ∀ i, decrypt toy toyS (encrypt toy toyPK toyM (toyR, toyE₁, toyE₂)) i = toyM i := by
  decide

/-- Decryption under the wrong secret key fails on this instance. -/
example : ¬ ∀ i, decrypt toy (fun _ => ![0, 1]) (encrypt toy toyPK toyM (toyR, toyE₁, toyE₂)) i =
    toyM i := by
  decide

/-! ### 4. The ML-KEM wrapper on the toy instance -/

/-- A toy `G` that ignores its input apart from the message and returns fixed coins. -/
def toyG : (Fin toy.n → Bool) × (Fin 256 → Bool) → (Fin 256 → Bool) × Coins toy :=
  fun x => (fun i => decide (i.val < 2) && x.1 ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩,
    (toyR, toyE₁, toyE₂))

def toyH : PublicKey toy → Fin 256 → Bool := fun _ _ => false

def toyJ : (Fin 256 → Bool) × Ciphertext toy → Fin 256 → Bool := fun x => x.1

def toyDK : MLKEM.DecapsKey toy :=
  { sk := toyS, pk := toyPK, pkHash := toyH toyPK, seed := fun _ => true }

/-- Honest decapsulation returns the encapsulated key. -/
example (m : Fin toy.n → Bool) :
    kemDecaps toy toyG toyJ toyDK (encrypt toy toyPK m (toyG (m, toyH toyPK)).2) =
      (toyG (m, toyH toyPK)).1 :=
  kemDecaps_encrypt_of_noise_le toy (B := 3) (by decide) toyG toyH toyJ toyA toyS toyE
    (fun _ => true) m toyR toyE₁ toyE₂ rfl (toy_noise_le m)

/-- A tampered ciphertext fails the re-encryption check and decapsulates to `J(z ‖ c)`. -/
example :
    let c : Ciphertext toy := (fun _ => ![0, 0], ![0, 0])
    kemDecaps toy toyG toyJ toyDK c = toyJ (toyDK.seed, c) := by
  intro c
  refine MLKEMTransform.decapsWith_of_reencrypt_ne _ _ _ _ _ ?_
  intro m' _
  revert m'
  decide

end CslibFrontierTests.Crypto.MLKEM
