/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.MLKEM.Compress
public import CslibFrontier.Crypto.Computational.SIS.ModuleEncryption
public import CslibFrontier.Crypto.Protocols.PKE.ExplicitCoin
public import CslibFrontier.Languages.Probabilistic.CenteredBinomial
public import CslibFrontier.Languages.Probabilistic.Vector

/-!
# K-PKE, the public-key encryption scheme inside ML-KEM

K-PKE ([NIST, Section 5, Algorithms 13–15][NISTFIPS203]) is Module-LWE encryption over
`R_q = ℤ_q[X] / (X^n + 1)` with centered-binomial secrets and errors and lossy ciphertext
compression:

* key generation samples `A ∈ R_q^{k×k}`, `s, e ← CBD_{η₁}^k` and publishes `(A, A s + e)`;
* encryption of `m ∈ {0,1}^n` with coins `r ← CBD_{η₁}^k`, `e₁ ← CBD_{η₂}^k`, `e₂ ← CBD_{η₂}`
  computes `u = Aᵀ r + e₁` and `v = bᵀ r + e₂ + Decompress_1(m)` and outputs
  `(Compress_{d_u}(u), Compress_{d_v}(v))`;
* decryption outputs `Compress_1(v' - sᵀ u')` for the decompressed `(u', v')`.

The uncompressed ciphertext is the existing `moduleLWEEncrypt` ciphertext of the all-zero message
shifted by the FIPS 203 message polynomial (`encryptRaw_eq_moduleLWEEncrypt_add`); the two encodings
differ because FIPS 203 rounds `q / 2` up. Public keys reuse `ModuleLWEPublicKey`, and the scheme is
packaged through the shared `ExplicitCoinPKE` interface (`toExplicitCoinPKE`) for later use by the
Fujisaki–Okamoto layer.

Correctness is deterministic: decryption recovers `m` whenever every coefficient of the decryption
noise `decryptionNoise`, which collects the Module-LWE error terms and both compression errors, has
centered magnitude at most `B` with `4 * B + 2 < q` (`decrypt_encrypt_eq_of_noise_le`). The
compression errors are bounded by `natAbs_valMinAbs_decompress_compress_sub_le`.

## Model differences

* The matrix `A` is sampled uniformly rather than expanded from a seed by `SampleNTT`, and the
  secrets and errors are sampled by `sampleCenteredBinomial` rather than derived from a seed by
  `PRF`; byte encodings are omitted.
* Polynomials are in coefficient form and multiplied with `negacyclicMul`; FIPS 203 stores them in
  the NTT domain, which is a ring isomorphism and does not change the scheme.
* The ring degree `n` and modulus `q` are parameters (FIPS 203 fixes `n = 256`, `q = 3329`), so
  small instances can be checked by evaluation.

## Main definitions

* `Cslib.Crypto.MLKEM.Params`, `Cslib.Crypto.MLKEM.mlkem512`, `Cslib.Crypto.MLKEM.mlkem768`,
  `Cslib.Crypto.MLKEM.mlkem1024`: parameter sets of [NIST, Section 8, Table 2][NISTFIPS203].
* `Cslib.Crypto.MLKEM.encryptRaw`, `Cslib.Crypto.MLKEM.encrypt`, `Cslib.Crypto.MLKEM.decrypt`:
  deterministic K-PKE encryption (before and after compression) and decryption.
* `Cslib.Crypto.MLKEM.samplePolyCBD`, `Cslib.Crypto.MLKEM.keyGen`,
  `Cslib.Crypto.MLKEM.sampleCoins`: centered-binomial sampling programs.
* `Cslib.Crypto.MLKEM.toExplicitCoinPKE`: K-PKE as an explicit-coin public-key scheme.

## Main results

* `Cslib.Crypto.MLKEM.decrypt_encrypt_phase`: the decryption phase is the message polynomial plus
  `decryptionNoise`.
* `Cslib.Crypto.MLKEM.decrypt_encrypt_eq_of_noise_le`: bounded-noise decryption correctness.

## References

* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*][NISTFIPS203]
-/

@[expose] public section

namespace Cslib.Crypto.MLKEM

open Probability Cslib.Crypto.Protocols

/-! ### Parameters -/

/-- ML-KEM parameters: ring degree `n`, modulus `q`, module rank `k`, centered-binomial widths
`η₁` (secrets and encryption randomness) and `η₂` (encryption errors), and compression widths
`d_u`, `d_v`. The degree and modulus default to the FIPS 203 values `256` and `3329`. -/
structure Params where
  /-- Ring degree `n`. -/
  n : ℕ := 256
  /-- Modulus `q`. -/
  q : ℕ := 3329
  /-- Module rank `k`. -/
  k : ℕ
  /-- Centered-binomial width `η₁` of the secret, key error and encryption randomness. -/
  η₁ : ℕ
  /-- Centered-binomial width `η₂` of the encryption errors. -/
  η₂ : ℕ
  /-- Compression width `d_u` of the vector part of a ciphertext. -/
  du : ℕ
  /-- Compression width `d_v` of the scalar part of a ciphertext. -/
  dv : ℕ
  deriving DecidableEq

/-- ML-KEM-512 ([NIST, Section 8, Table 2][NISTFIPS203]): `k = 2`, `η₁ = 3`, `η₂ = 2`,
`d_u = 10`, `d_v = 4`. -/
def mlkem512 : Params := { k := 2, η₁ := 3, η₂ := 2, du := 10, dv := 4 }

/-- ML-KEM-768 ([NIST, Section 8, Table 2][NISTFIPS203]): `k = 3`, `η₁ = 2`, `η₂ = 2`,
`d_u = 10`, `d_v = 4`. -/
def mlkem768 : Params := { k := 3, η₁ := 2, η₂ := 2, du := 10, dv := 4 }

/-- ML-KEM-1024 ([NIST, Section 8, Table 2][NISTFIPS203]): `k = 4`, `η₁ = 2`, `η₂ = 2`,
`d_u = 11`, `d_v = 5`. -/
def mlkem1024 : Params := { k := 4, η₁ := 2, η₂ := 2, du := 11, dv := 5 }

/-- The parameter sets approved by FIPS 203. -/
def Params.IsStandard (P : Params) : Prop :=
  P = mlkem512 ∨ P = mlkem768 ∨ P = mlkem1024

instance (P : Params) : Decidable P.IsStandard :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- Every approved parameter set has `n = 256`, `q = 3329` and compression widths below
`log₂ q`, so `compress_decompress` applies to both ciphertext parts. -/
theorem Params.IsStandard.bounds {P : Params} (h : P.IsStandard) :
    P.n = 256 ∧ P.q = 3329 ∧ 2 ^ P.du < P.q ∧ 2 ^ P.dv < P.q := by
  rcases h with rfl | rfl | rfl <;> decide

/-! ### Keys, ciphertexts and deterministic algorithms -/

/-- K-PKE public keys `(A, b)` are Module-LWE public keys. -/
abbrev PublicKey (P : Params) : Type := ModuleLWEPublicKey P.k P.n P.q

/-- K-PKE secret keys `s ∈ R_q^k`. -/
abbrev SecretKey (P : Params) : Type := Fin P.k → Fin P.n → ZMod P.q

/-- Encryption coins `(r, e₁, e₂) ∈ R_q^k × R_q^k × R_q`. -/
abbrev Coins (P : Params) : Type :=
  (Fin P.k → Fin P.n → ZMod P.q) × (Fin P.k → Fin P.n → ZMod P.q) × (Fin P.n → ZMod P.q)

/-- Compressed ciphertexts `(c₁, c₂)` with `d_u`-bit coefficients in `c₁ ∈ (ℤ_{2^{d_u}}^n)^k` and
`d_v`-bit coefficients in `c₂ ∈ ℤ_{2^{d_v}}^n`. -/
abbrev Ciphertext (P : Params) : Type :=
  (Fin P.k → Fin P.n → ZMod (2 ^ P.du)) × (Fin P.n → ZMod (2 ^ P.dv))

/-- The message polynomial `Decompress_1(m)`: bit `1` becomes `⌈q / 2⌋` and bit `0` becomes `0`. -/
def messagePoly (P : Params) (m : Fin P.n → Bool) : Fin P.n → ZMod P.q :=
  decompressPoly P.q 1 fun i => if m i then 1 else 0

/-- Uncompressed K-PKE encryption `(Aᵀ r + e₁, bᵀ r + e₂ + Decompress_1(m))`. -/
def encryptRaw (P : Params) (pk : PublicKey P) (r e₁ : Fin P.k → Fin P.n → ZMod P.q)
    (e₂ : Fin P.n → ZMod P.q) (m : Fin P.n → Bool) : ModuleLWECiphertext P.k P.n P.q :=
  (moduleSISMap pk.1.transpose r + e₁, innerPoly pk.2 r + e₂ + messagePoly P m)

/-- Compress both parts of an uncompressed ciphertext. -/
def compressCiphertext (P : Params) (ct : ModuleLWECiphertext P.k P.n P.q) : Ciphertext P :=
  (fun j => compressPoly P.q P.du (ct.1 j), compressPoly P.q P.dv ct.2)

/-- Decompress both parts of a ciphertext. -/
def decompressCiphertext (P : Params) (ct : Ciphertext P) : ModuleLWECiphertext P.k P.n P.q :=
  (fun j => decompressPoly P.q P.du (ct.1 j), decompressPoly P.q P.dv ct.2)

/-- Deterministic K-PKE encryption `K-PKE.Encrypt(pk, m; (r, e₁, e₂))`
([NIST, Section 5, Algorithm 14][NISTFIPS203]), with explicit coins. -/
def encrypt (P : Params) (pk : PublicKey P) (m : Fin P.n → Bool) (coins : Coins P) :
    Ciphertext P :=
  match coins with
  | (r, e₁, e₂) => compressCiphertext P (encryptRaw P pk r e₁ e₂ m)

/-- K-PKE decryption `K-PKE.Decrypt(s, c) = Compress_1(v' - sᵀ u')`
([NIST, Section 5, Algorithm 15][NISTFIPS203]), reading coefficient `1` as the bit `true`. -/
def decrypt (P : Params) (s : SecretKey P) (ct : Ciphertext P) : Fin P.n → Bool :=
  fun i => decide (compress P.q 1
    (((decompressCiphertext P ct).2 - innerPoly (decompressCiphertext P ct).1 s) i) = 1)

/-- The existing Module-LWE encoding of the all-zero message is zero. -/
@[simp] theorem encodePolyMsg_false {n : ℕ} (q : ℕ) :
    encodePolyMsg q (fun _ : Fin n => false) = 0 := by
  funext i
  simp

/-- **Relation to `moduleLWEEncrypt`**: uncompressed K-PKE encryption is Module-LWE encryption of
the all-zero message, shifted by the FIPS 203 message polynomial. -/
theorem encryptRaw_eq_moduleLWEEncrypt_add (P : Params) (pk : PublicKey P)
    (r e₁ : Fin P.k → Fin P.n → ZMod P.q) (e₂ : Fin P.n → ZMod P.q) (m : Fin P.n → Bool) :
    encryptRaw P pk r e₁ e₂ m =
      moduleLWEEncrypt pk r e₁ e₂ (fun _ => false) + (0, messagePoly P m) := by
  simp [encryptRaw, moduleLWEEncrypt]

/-! ### Bounded-noise correctness -/

/-- The decryption noise of an honest encryption: the Module-LWE error
`eᵀ r - sᵀ e₁ + e₂`, plus the scalar compression error `c_v`, minus `sᵀ c_u` for the vector
compression error `c_u`. -/
def decryptionNoise (P : Params) (A : Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))
    (s e r e₁ : Fin P.k → Fin P.n → ZMod P.q) (e₂ : Fin P.n → ZMod P.q) (m : Fin P.n → Bool) :
    Fin P.n → ZMod P.q :=
  let raw := encryptRaw P (moduleLWEKeyGen A s e) r e₁ e₂ m
  let cu := (decompressCiphertext P (compressCiphertext P raw)).1 - raw.1
  let cv := (decompressCiphertext P (compressCiphertext P raw)).2 - raw.2
  innerPoly e r - innerPoly e₁ s + e₂ + cv - innerPoly cu s

/-- **Decryption phase**: for an honest key and encryption, `v' - sᵀ u'` equals the message
polynomial plus `decryptionNoise`. -/
theorem decrypt_encrypt_phase (P : Params) (A : Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))
    (s e r e₁ : Fin P.k → Fin P.n → ZMod P.q) (e₂ : Fin P.n → ZMod P.q) (m : Fin P.n → Bool) :
    let ct := decompressCiphertext P (encrypt P (moduleLWEKeyGen A s e) m (r, e₁, e₂))
    ct.2 - innerPoly ct.1 s = messagePoly P m + decryptionNoise P A s e r e₁ e₂ m := by
  intro ct
  set raw := encryptRaw P (moduleLWEKeyGen A s e) r e₁ e₂ m with hraw
  have hphase := moduleLWEDecrypt_phase_eq A s e r e₁ e₂ (fun _ => false)
  rw [encodePolyMsg_false, zero_add] at hphase
  have hct : ct = decompressCiphertext P (compressCiphertext P raw) := rfl
  have h₁ : raw.1 = (moduleLWEEncrypt (moduleLWEKeyGen A s e) r e₁ e₂ fun _ => false).1 := by
    rw [hraw, encryptRaw_eq_moduleLWEEncrypt_add]
    simp
  have h₂ : raw.2 = (moduleLWEEncrypt (moduleLWEKeyGen A s e) r e₁ e₂ fun _ => false).2 +
      messagePoly P m := by
    rw [hraw, encryptRaw_eq_moduleLWEEncrypt_add]
    simp
  simp only [decryptionNoise, ← hraw, ← hct]
  rw [← hphase, innerPoly_sub_left, h₂, h₁]
  abel

/-- **Bounded-noise correctness of K-PKE**: if every coefficient of `decryptionNoise` has centered
magnitude at most `B` and `4 * B + 2 < q`, decryption of an honest encryption recovers the
message. -/
theorem decrypt_encrypt_eq_of_noise_le (P : Params) {B : ℕ} (hB : 4 * B + 2 < P.q)
    (A : Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))
    (s e r e₁ : Fin P.k → Fin P.n → ZMod P.q) (e₂ : Fin P.n → ZMod P.q) (m : Fin P.n → Bool)
    (hnoise : ∀ i, (decryptionNoise P A s e r e₁ e₂ m i).valMinAbs.natAbs ≤ B) :
    decrypt P s (encrypt P (moduleLWEKeyGen A s e) m (r, e₁, e₂)) = m := by
  funext i
  have hphase := congrFun (decrypt_encrypt_phase P A s e r e₁ e₂ m) i
  simp only [Pi.add_apply] at hphase
  simp only [decrypt, hphase, messagePoly, decompressPoly_apply,
    compress_one_decompress_one_add hB _ (hnoise i)]
  cases m i <;> decide

/-! ### Centered-binomial sampling programs -/

/-- `SamplePolyCBD_η` ([NIST, Section 4.2.2, Algorithm 8][NISTFIPS203]) as a program: `n`
independent centered-binomial coefficients of width `η`, reduced modulo `q`. -/
noncomputable def samplePolyCBD (n q η : ℕ) : ProbComp (Fin n → ZMod q) := do
  let coeffs ← OracleComp.replicateFin n (ProbComp.sampleCenteredBinomial η)
  return fun i => (coeffs i : ZMod q)

/-- A vector of `k` independent `SamplePolyCBD_η` polynomials. -/
noncomputable def sampleVecCBD (k n q η : ℕ) : ProbComp (Fin k → Fin n → ZMod q) :=
  OracleComp.replicateFin k (samplePolyCBD n q η)

/-- K-PKE key generation ([NIST, Section 5, Algorithm 13][NISTFIPS203]) with a uniform matrix:
`A` uniform, `s, e ← CBD_{η₁}^k`, output `((A, A s + e), s)`. -/
noncomputable def keyGen (P : Params) [NeZero P.q] : ProbComp (PublicKey P × SecretKey P) := do
  let A ← ProbComp.uniform (Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))
  let s ← sampleVecCBD P.k P.n P.q P.η₁
  let e ← sampleVecCBD P.k P.n P.q P.η₁
  return (moduleLWEKeyGen A s e, s)

/-- K-PKE encryption coins ([NIST, Section 5, Algorithm 14][NISTFIPS203]):
`r ← CBD_{η₁}^k`, `e₁ ← CBD_{η₂}^k`, `e₂ ← CBD_{η₂}`. -/
noncomputable def sampleCoins (P : Params) : ProbComp (Coins P) := do
  let r ← sampleVecCBD P.k P.n P.q P.η₁
  let e₁ ← sampleVecCBD P.k P.n P.q P.η₂
  let e₂ ← samplePolyCBD P.n P.q P.η₂
  return (r, e₁, e₂)

/-- K-PKE as an explicit-coin public-key encryption scheme. Decryption never fails. -/
noncomputable def toExplicitCoinPKE (P : Params) [NeZero P.q] :
    ExplicitCoinPKE (PublicKey P) (SecretKey P) (Fin P.n → Bool) (Coins P) (Ciphertext P) where
  keyGen := keyGen P
  sampleCoins := sampleCoins P
  encDet := encrypt P
  dec s ct := some (decrypt P s ct)

end Cslib.Crypto.MLKEM
