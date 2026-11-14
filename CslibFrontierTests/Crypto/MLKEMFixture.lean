/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.KEM.MLKEM

/-! Shared toy K-PKE and ML-KEM fixtures, extracted without changing their definitions or
noise theorem from `CslibFrontierTests.Crypto.MLKEM` by Karn Seth. -/

public section

namespace CslibFrontierTests.Crypto.MLKEM

open Cslib Cslib.Crypto Cslib.Crypto.MLKEM Cslib.Crypto.Protocols

/-- Toy parameters: `n = 2`, `q = 17`, `k = 1`, `d_u = 4`, `d_v = 3`. -/
@[expose] def toy : Params := { n := 2, q := 17, k := 1, η₁ := 1, η₂ := 1, du := 4, dv := 3 }

instance : NeZero toy.q := ⟨by decide⟩

@[expose] def toyA : Matrix (Fin toy.k) (Fin toy.k) (Fin toy.n → ZMod toy.q) := fun _ _ => ![3, 2]
@[expose] def toyS : SecretKey toy := fun _ => ![1, 0]
@[expose] def toyE : Fin toy.k → Fin toy.n → ZMod toy.q := fun _ => ![0, 1]
@[expose] def toyR : Fin toy.k → Fin toy.n → ZMod toy.q := fun _ => ![1, 0]
@[expose] def toyE₁ : Fin toy.k → Fin toy.n → ZMod toy.q := fun _ => ![0, 1]
@[expose] def toyE₂ : Fin toy.n → ZMod toy.q := ![1, 0]
@[expose] def toyPK : PublicKey toy := moduleLWEKeyGen toyA toyS toyE

/-- The noise hypothesis of `decrypt_encrypt_eq_of_noise_le` holds with `B = 3`
(`4 * 3 + 2 < 17`) for both messages. -/
theorem toy_noise_le (m : Fin toy.n → Bool) (i : Fin toy.n) :
    (decryptionNoise toy toyA toyS toyE toyR toyE₁ toyE₂ m i).valMinAbs.natAbs ≤ 3 := by
  revert m i
  decide

@[expose] def toyM : Fin toy.n → Bool := ![true, false]

/-- The all-zero ciphertext used by the implicit-rejection regression. -/
@[expose] def toyTampered : Ciphertext toy := (fun _ => ![0, 0], ![0, 0])

/-- No message re-encrypts to the tampered ciphertext under the shared toy coins. -/
theorem toy_encrypt_ne_tampered (m : Fin toy.n → Bool) :
    encrypt toy toyPK m (toyR, toyE₁, toyE₂) ≠ toyTampered := by
  revert m
  decide

/-- A toy `G` that ignores its input apart from the message and returns fixed coins. -/
@[expose] def toyG : (Fin toy.n → Bool) × (Fin 256 → Bool) → (Fin 256 → Bool) × Coins toy :=
  fun x => (fun i => decide (i.val < 2) && x.1 ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩,
    (toyR, toyE₁, toyE₂))

@[expose] def toyH : PublicKey toy → Fin 256 → Bool := fun _ _ => false

@[expose] def toyJ : (Fin 256 → Bool) × Ciphertext toy → Fin 256 → Bool := fun x => x.1

@[expose] def toyDK : MLKEM.DecapsKey toy :=
  { sk := toyS, pk := toyPK, pkHash := toyH toyPK, seed := fun _ => true }

end CslibFrontierTests.Crypto.MLKEM
