/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.PauliTwirl

/-!
# The quantum one-time pad

Alice and Bob share a uniformly random key `(a, b)` of `2n` bits. To send an `n`-qubit state `ρ`
over a public quantum channel, Alice applies the Pauli string `X^a Z^b` and sends
`X^a Z^b ρ (X^a Z^b)ᴴ` (`Cslib.Crypto.Protocols.Quantum.OneTimePad.encrypt`); Bob undoes it with
`(X^a Z^b)ᴴ` (`Cslib.Crypto.Protocols.Quantum.OneTimePad.decrypt_encrypt`). An eavesdropper who
does not know the key holds the key-averaged state, which is the maximally mixed state `1 / 2ⁿ`
whatever `ρ` is (`Cslib.Crypto.Protocols.Quantum.OneTimePad.averageCiphertext_eq`), by the Pauli
twirl (`Cslib.Quantum.sum_pauliTwirl`). So the channel reveals nothing about `ρ`
(`Cslib.Crypto.Protocols.Quantum.OneTimePad.averageCiphertext_eq_averageCiphertext`): `2n` bits of
key suffice to hide `n` qubits ([Ambainis, Mosca, Tapp, de Wolf][AmbainisMoscaTappdeWolf2000],
Theorem 4.1, without ancilla; [de Wolf][deWolf2019], Chapter 18, Exercise 5(b), for one qubit).
AMTW apply a uniformly random tensor product of `I, X, Y, Z`; since `Y = i X Z`, each such
operator equals some `X^a Z^b` up to a global phase, which cancels in the conjugation, so the two
encryptions are the same channel.

Secrecy survives entanglement: if the plaintext register is part of a joint state `ρ` with a
reference system that Eve may also hold, her key-averaged state is `1 / 2ⁿ ⊗ Tr_A ρ`
(`Cslib.Crypto.Protocols.Quantum.OneTimePad.averageCiphertextWith_eq`), so it depends only on the
reference system's own state, and not on the plaintext or its correlations with the reference.
This product form (full decoupling) is a standard strengthening of the remark in the proof of
Theorem 4.1 that the twirled qubit is maximally mixed "no matter if it is entangled with other
qubits".

Only the sufficiency of `2n` key bits is formalized; the matching lower bound (`2n` bits of key
entropy are necessary, [Ambainis, Mosca, Tapp, de Wolf][AmbainisMoscaTappdeWolf2000],
Corollary 5.4) is not.

## Main definitions

* `Cslib.Crypto.Protocols.Quantum.OneTimePad.encrypt`, `.decrypt`: conjugation by `X^a Z^b` and
  by its adjoint.
* `Cslib.Crypto.Protocols.Quantum.OneTimePad.averageCiphertext`: the ciphertext averaged over a
  uniformly random key, the eavesdropper's state.
* `Cslib.Crypto.Protocols.Quantum.OneTimePad.averageCiphertextWith`: the same with a reference
  system.

## Main results

* `Cslib.Crypto.Protocols.Quantum.OneTimePad.decrypt_encrypt`: decryption is exact.
* `Cslib.Crypto.Protocols.Quantum.OneTimePad.isDensityMatrix_encrypt`: ciphertexts are states.
* `Cslib.Crypto.Protocols.Quantum.OneTimePad.averageCiphertext_eq`: the average ciphertext of a
  state is maximally mixed.
* `Cslib.Crypto.Protocols.Quantum.OneTimePad.averageCiphertext_eq_averageCiphertext`: perfect
  secrecy.
* `Cslib.Crypto.Protocols.Quantum.OneTimePad.averageCiphertextWith_eq`: secrecy against an
  eavesdropper holding a reference system.

## References

* [Ambainis, Mosca, Tapp, de Wolf, *Private Quantum Channels*][AmbainisMoscaTappdeWolf2000]
* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019]
-/

public section

namespace Cslib.Crypto.Protocols.Quantum.OneTimePad

open Matrix Finset Cslib.Quantum
open scoped Kronecker

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- The plaintext and ciphertext space: matrices on `n = |ι|` qubits. -/
abbrev Op (ι : Type*) := Matrix (ι → Bool) (ι → Bool) ℂ

/-- **Encryption** with the key `(a, b)`: `ρ ↦ X^a Z^b ρ (X^a Z^b)ᴴ`. -/
noncomputable def encrypt : (ι → Bool) × (ι → Bool) → Op ι → Op ι
  | (a, b), ρ => pauliString a b * ρ * (pauliString a b)ᴴ

/-- **Decryption** with the key `(a, b)`: `σ ↦ (X^a Z^b)ᴴ σ X^a Z^b`. -/
noncomputable def decrypt : (ι → Bool) × (ι → Bool) → Op ι → Op ι
  | (a, b), σ => (pauliString a b)ᴴ * σ * pauliString a b

theorem encrypt_def (a b : ι → Bool) (ρ : Op ι) :
    encrypt (a, b) ρ = pauliString a b * ρ * (pauliString a b)ᴴ := by
  rfl

theorem decrypt_def (a b : ι → Bool) (σ : Op ι) :
    decrypt (a, b) σ = (pauliString a b)ᴴ * σ * pauliString a b := by
  rfl

/-- **Correctness**: decryption with the same key recovers the plaintext. -/
theorem decrypt_encrypt (k : (ι → Bool) × (ι → Bool)) (ρ : Op ι) :
    decrypt k (encrypt k ρ) = ρ := by
  obtain ⟨a, b⟩ := k
  have hU := pauliString_mem_unitaryGroup a b
  have h1 : (pauliString a b)ᴴ * pauliString a b = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.mp hU
  simp only [decrypt, encrypt, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [Matrix.mul_assoc, h1, Matrix.mul_one]

/-- Ciphertexts of states are states. -/
theorem isDensityMatrix_encrypt {ρ : Op ι} (hρ : IsDensityMatrix ρ)
    (k : (ι → Bool) × (ι → Bool)) : IsDensityMatrix (encrypt k ρ) :=
  let (a, b) := k
  hρ.conj_unitary (pauliString_mem_unitaryGroup a b)

/-- The ciphertext averaged over a uniformly random key of `2n` bits: the state of an
eavesdropper who does not know the key. -/
noncomputable def averageCiphertext (ρ : Op ι) : Op ι :=
  (Fintype.card ((ι → Bool) × (ι → Bool)) : ℂ)⁻¹ • ∑ k, encrypt k ρ

theorem card_key : Fintype.card ((ι → Bool) × (ι → Bool)) = 4 ^ Fintype.card ι := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, ← mul_pow]
  norm_num

/-- The average ciphertext is `tr ρ / 2ⁿ • 1`. -/
theorem averageCiphertext_eq_trace_smul (ρ : Op ι) :
    averageCiphertext ρ = (ρ.trace / 2 ^ Fintype.card ι) • (1 : Op ι) := by
  rw [averageCiphertext, card_key, Fintype.sum_prod_type]
  simp only [encrypt]
  rw [sum_pauliTwirl, smul_smul]
  congr 1
  push_cast
  rw [show (4 : ℂ) ^ Fintype.card ι = 2 ^ Fintype.card ι * 2 ^ Fintype.card ι by
    rw [← mul_pow]; norm_num]
  field_simp

/-- The average ciphertext of any state is the **maximally mixed state** `1 / 2ⁿ`. -/
theorem averageCiphertext_eq {ρ : Op ι} (hρ : IsDensityMatrix ρ) :
    averageCiphertext ρ = (2 ^ Fintype.card ι : ℂ)⁻¹ • (1 : Op ι) := by
  rw [averageCiphertext_eq_trace_smul, hρ.trace_eq_one, one_div]

/-- **Perfect secrecy**: the eavesdropper's state is the same for every plaintext state. -/
theorem averageCiphertext_eq_averageCiphertext {ρ ρ' : Op ι} (hρ : IsDensityMatrix ρ)
    (hρ' : IsDensityMatrix ρ') : averageCiphertext ρ = averageCiphertext ρ' := by
  rw [averageCiphertext_eq hρ, averageCiphertext_eq hρ']

/-! ### Secrecy with a reference system -/

/-- Encryption of the first register of a joint state with a reference system `κ`:
`ρ ↦ (X^a Z^b ⊗ 1) ρ (X^a Z^b ⊗ 1)ᴴ`. -/
noncomputable def encryptWith [Fintype κ] [DecidableEq κ] :
    (ι → Bool) × (ι → Bool) → Matrix ((ι → Bool) × κ) ((ι → Bool) × κ) ℂ →
      Matrix ((ι → Bool) × κ) ((ι → Bool) × κ) ℂ
  | (a, b), ρ => (pauliString a b ⊗ₖ (1 : Matrix κ κ ℂ)) * ρ * (pauliString a b ⊗ₖ 1)ᴴ

theorem encryptWith_def [Fintype κ] [DecidableEq κ] (a b : ι → Bool)
    (ρ : Matrix ((ι → Bool) × κ) ((ι → Bool) × κ) ℂ) :
    encryptWith (a, b) ρ =
      (pauliString a b ⊗ₖ (1 : Matrix κ κ ℂ)) * ρ * (pauliString a b ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ := by
  rfl

/-- Joint ciphertexts of joint states are states. -/
theorem isDensityMatrix_encryptWith [Fintype κ] [DecidableEq κ]
    {ρ : Matrix ((ι → Bool) × κ) ((ι → Bool) × κ) ℂ} (hρ : IsDensityMatrix ρ)
    (k : (ι → Bool) × (ι → Bool)) : IsDensityMatrix (encryptWith k ρ) :=
  let (a, b) := k
  hρ.conj_unitary (kronecker_mem_unitary (pauliString_mem_unitaryGroup a b) (one_mem _))

/-- The key-averaged joint state of the ciphertext and the reference system. -/
noncomputable def averageCiphertextWith [Fintype κ] [DecidableEq κ]
    (ρ : Matrix ((ι → Bool) × κ) ((ι → Bool) × κ) ℂ) :
    Matrix ((ι → Bool) × κ) ((ι → Bool) × κ) ℂ :=
  (Fintype.card ((ι → Bool) × (ι → Bool)) : ℂ)⁻¹ • ∑ k, encryptWith k ρ

/-- **Secrecy with a reference system**: the key-averaged joint state is `1 / 2ⁿ ⊗ Tr_A ρ`, a
product of the maximally mixed state with the reference system's own state. -/
theorem averageCiphertextWith_eq [Fintype κ] [DecidableEq κ]
    (ρ : Matrix ((ι → Bool) × κ) ((ι → Bool) × κ) ℂ) :
    averageCiphertextWith ρ =
      ((2 ^ Fintype.card ι : ℂ)⁻¹ • (1 : Op ι)) ⊗ₖ partialTraceLeft ρ := by
  rw [averageCiphertextWith, card_key, Fintype.sum_prod_type]
  simp only [encryptWith]
  rw [sum_pauliTwirl_kronecker_one, smul_smul, smul_kronecker]
  congr 1
  push_cast
  rw [show (4 : ℂ) ^ Fintype.card ι = 2 ^ Fintype.card ι * 2 ^ Fintype.card ι by
    rw [← mul_pow]; norm_num]
  field_simp

/-- The eavesdropper's joint state with the reference system depends only on the reference
system's own state `Tr_A ρ`: plaintexts with the same reduced state on the reference system are
indistinguishable, even given the reference system. -/
theorem averageCiphertextWith_eq_of_partialTraceLeft_eq [Fintype κ] [DecidableEq κ]
    {ρ ρ' : Matrix ((ι → Bool) × κ) ((ι → Bool) × κ) ℂ}
    (h : partialTraceLeft ρ = partialTraceLeft ρ') :
    averageCiphertextWith ρ = averageCiphertextWith ρ' := by
  rw [averageCiphertextWith_eq, averageCiphertextWith_eq, h]

end Cslib.Crypto.Protocols.Quantum.OneTimePad
