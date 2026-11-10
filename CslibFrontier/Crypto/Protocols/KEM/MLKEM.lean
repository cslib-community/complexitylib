/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.MLKEM.KPKE

/-!
# ML-KEM: the FIPS 203 implicit-rejection wrapper

ML-KEM turns K-PKE into a key-encapsulation mechanism by a Fujisaki–Okamoto-style transform with
implicit rejection ([NIST, Section 6, Algorithms 16–18][NISTFIPS203]):

* key generation stores the decapsulation key `dk = (dk_PKE, ek, H(ek), z)` with a secret seed `z`;
* encapsulation samples `m`, derives `(K, r) = G(m ‖ H(ek))` and outputs `c = Enc(ek, m; r)` and
  the shared key `K`;
* decapsulation decrypts `m' = Dec(dk_PKE, c)`, derives `(K', r') = G(m' ‖ h)`, and returns `K'`
  if `Enc(ek, m'; r') = c` and the rejection key `J(z ‖ c)` otherwise.

The wrapper is stated for any `ExplicitCoinPKE`, and the re-encryption check is the existing
`FujisakiOkamoto.decT` with coin function `m ↦ (G(m ‖ h)).2` (`decapsWith_eq`). Unlike
`FujisakiOkamoto.Scheme.decapsNotBot`, which derives keys as `H(false, m, c)` and rejection keys
from a message-space seed, ML-KEM takes the shared key from `G` without hashing `c`, binds the
public key into `G` through `H(ek)`, and derives rejection keys from an independent seed `z`.

`G`, `H` and `J` are arbitrary functions; no random-oracle security statement is made here. `G`
returns the encryption coins directly, where FIPS 203 returns a seed expanded by `PRF` and
`SamplePolyCBD`. The input checks of FIPS 203, Section 7 (encapsulation-key modulus check,
decapsulation-key hash check `H(ek) = h`, length checks) are not modelled; the typed keys make the
length and modulus checks vacuous, but the hash check is simply omitted.

## Main definitions

* `Cslib.Crypto.Protocols.MLKEMTransform.DecapsKey`: decapsulation keys `(sk, pk, H(pk), z)`.
* `Cslib.Crypto.Protocols.MLKEMTransform.keyGenWith`,
  `Cslib.Crypto.Protocols.MLKEMTransform.encapsWith`,
  `Cslib.Crypto.Protocols.MLKEMTransform.decapsWith`: the transform over an `ExplicitCoinPKE`.
* `Cslib.Crypto.MLKEM.kemKeyGen`, `Cslib.Crypto.MLKEM.kemEncaps`, `Cslib.Crypto.MLKEM.kemDecaps`:
  ML-KEM, the transform applied to K-PKE with uniform `n`-bit messages (`n = 256` for the
  standard sets) and 256-bit seeds.

## Main results

* `Cslib.Crypto.Protocols.MLKEMTransform.decapsWith_encT`: honest decapsulation returns the
  encapsulated key whenever the underlying decryption is correct.
* `Cslib.Crypto.Protocols.MLKEMTransform.decapsWith_of_reencrypt_ne`: implicit rejection.
* `Cslib.Crypto.MLKEM.kemDecaps_encrypt_of_noise_le`: ML-KEM correctness from the bounded-noise
  correctness of K-PKE.

## References

* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, Sections 6 and 7][NISTFIPS203]
* [Hofheinz, Hövelmanns, Kiltz, *A Modular Analysis of the Fujisaki–Okamoto Transformation*]
  [HofheinzHoevelmannsKiltz2017]
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.MLKEMTransform

open FujisakiOkamoto

/-- An ML-KEM decapsulation key: the PKE secret key, the public key, its hash `H(pk)` and the
implicit-rejection seed `z`. -/
structure DecapsKey (PK SK Hk Z : Type) where
  /-- PKE secret key `dk_PKE`. -/
  sk : SK
  /-- Public (encapsulation) key `ek`, kept for the re-encryption check. -/
  pk : PK
  /-- Stored hash `h = H(ek)`. -/
  pkHash : Hk
  /-- Implicit-rejection seed `z`. -/
  seed : Z
  deriving DecidableEq

variable {PK SK M R CT Hk Z K : Type}

/-- Key generation: run the PKE key generation, sample the seed `z`, and store `H(pk)`. -/
def keyGenWith (pke : ExplicitCoinPKE PK SK M R CT) (sampleSeed : ProbComp Z) (H : PK → Hk) :
    ProbComp (PK × DecapsKey PK SK Hk Z) := do
  let (pk, sk) ← pke.keyGen
  let z ← sampleSeed
  return (pk, { sk := sk, pk := pk, pkHash := H pk, seed := z })

/-- Encapsulation: sample `m`, derive `(K, r) = G(m ‖ H(pk))`, and output `(Enc(pk, m; r), K)`. -/
def encapsWith (pke : ExplicitCoinPKE PK SK M R CT) (sampleMsg : ProbComp M)
    (G : M × Hk → K × R) (H : PK → Hk) (pk : PK) : ProbComp (CT × K) := do
  let m ← sampleMsg
  let derived := G (m, H pk)
  return (pke.encDet pk m derived.2, derived.1)

/-- Decapsulation with implicit rejection: accept `m'` through the re-encryption check `decT` with
coins `(G(m' ‖ h)).2` and return `(G(m' ‖ h)).1`, or return `J(z ‖ c)` on rejection. -/
def decapsWith [DecidableEq CT] (pke : ExplicitCoinPKE PK SK M R CT) (G : M × Hk → K × R)
    (J : Z × CT → K) (dk : DecapsKey PK SK Hk Z) (c : CT) : K :=
  match decT pke (fun m => (G (m, dk.pkHash)).2) dk.pk dk.sk c with
  | some m' => (G (m', dk.pkHash)).1
  | none => J (dk.seed, c)

/-- **FIPS 203 form of decapsulation** ([NIST, Section 6, Algorithm 18][NISTFIPS203]): after
`m' = Dec(sk, c)`, return `K'` if re-encrypting `m'` with `r'` gives `c`, and `J(z ‖ c)`
otherwise, where `(K', r') = G(m' ‖ h)`. -/
theorem decapsWith_eq [DecidableEq CT] (pke : ExplicitCoinPKE PK SK M R CT) (G : M × Hk → K × R)
    (J : Z × CT → K) (dk : DecapsKey PK SK Hk Z) (c : CT) {m' : M}
    (hdec : pke.dec dk.sk c = some m') :
    decapsWith pke G J dk c =
      if pke.encDet dk.pk m' (G (m', dk.pkHash)).2 = c then (G (m', dk.pkHash)).1
      else J (dk.seed, c) := by
  unfold decapsWith decT encT
  rw [hdec]
  by_cases h : pke.encDet dk.pk m' (G (m', dk.pkHash)).2 = c <;> simp [h]

/-- **Correctness**: if the PKE decrypts the honest ciphertext `Enc(pk, m; (G(m ‖ h)).2)`, then
decapsulation returns the encapsulated key `(G(m ‖ h)).1`. -/
theorem decapsWith_encT [DecidableEq CT] (pke : ExplicitCoinPKE PK SK M R CT) (G : M × Hk → K × R)
    (J : Z × CT → K) (dk : DecapsKey PK SK Hk Z) (m : M)
    (hdec : pke.dec dk.sk (pke.encDet dk.pk m (G (m, dk.pkHash)).2) = some m) :
    decapsWith pke G J dk (pke.encDet dk.pk m (G (m, dk.pkHash)).2) = (G (m, dk.pkHash)).1 := by
  rw [decapsWith_eq pke G J dk _ hdec]
  simp

/-- **Implicit rejection**: a ciphertext that fails the re-encryption check decapsulates to the
rejection key `J(z ‖ c)`. -/
theorem decapsWith_of_reencrypt_ne [DecidableEq CT] (pke : ExplicitCoinPKE PK SK M R CT)
    (G : M × Hk → K × R) (J : Z × CT → K) (dk : DecapsKey PK SK Hk Z) (c : CT)
    (hbad : ∀ m', pke.dec dk.sk c = some m' → pke.encDet dk.pk m' (G (m', dk.pkHash)).2 ≠ c) :
    decapsWith pke G J dk c = J (dk.seed, c) := by
  unfold decapsWith
  rw [decT_eq_none_of_reencrypt_ne pke _ dk.pk dk.sk c hbad]

/-- Every key pair produced by `keyGenWith` stores the public key and its hash. -/
theorem mem_support_keyGenWith (pke : ExplicitCoinPKE PK SK M R CT) (sampleSeed : ProbComp Z)
    (H : PK → Hk) {pk : PK} {dk : DecapsKey PK SK Hk Z}
    (h : (pk, dk) ∈ (ProbComp.eval (keyGenWith pke sampleSeed H)).support) :
    dk.pk = pk ∧ dk.pkHash = H pk ∧ (pk, dk.sk) ∈ (ProbComp.eval pke.keyGen).support := by
  simp only [keyGenWith, ProbComp.eval_bind, ProbComp.eval_pure, PMF.support_bind,
    PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff, Prod.mk.injEq] at h
  obtain ⟨⟨pk', sk'⟩, hkey, z, -, rfl, rfl⟩ := h
  exact ⟨rfl, rfl, hkey⟩

end Cslib.Crypto.Protocols.MLKEMTransform

namespace Cslib.Crypto.MLKEM

open Cslib.Crypto.Protocols Cslib.Crypto.Protocols.MLKEMTransform

/-- ML-KEM decapsulation keys over K-PKE, with 256-bit public-key hashes and seeds. -/
abbrev DecapsKey (P : Params) : Type :=
  MLKEMTransform.DecapsKey (PublicKey P) (SecretKey P) (Fin 256 → Bool) (Fin 256 → Bool)

variable (P : Params)

/-- `ML-KEM.KeyGen` ([NIST, Section 7, Algorithm 19][NISTFIPS203]) with a uniform seed `z`. -/
noncomputable def kemKeyGen [NeZero P.q] (H : PublicKey P → Fin 256 → Bool) :
    ProbComp (PublicKey P × DecapsKey P) :=
  keyGenWith (toExplicitCoinPKE P) (ProbComp.uniform (Fin 256 → Bool)) H

/-- `ML-KEM.Encaps` ([NIST, Section 7, Algorithm 20][NISTFIPS203]) with a uniform message
`m ∈ {0,1}^n`. -/
noncomputable def kemEncaps [NeZero P.q] (G : (Fin P.n → Bool) × (Fin 256 → Bool) →
      (Fin 256 → Bool) × Coins P) (H : PublicKey P → Fin 256 → Bool) (pk : PublicKey P) :
    ProbComp (Ciphertext P × (Fin 256 → Bool)) :=
  encapsWith (toExplicitCoinPKE P) (ProbComp.uniform (Fin P.n → Bool)) G H pk

/-- `ML-KEM.Decaps` ([NIST, Section 7, Algorithm 21][NISTFIPS203]). -/
noncomputable def kemDecaps [NeZero P.q] (G : (Fin P.n → Bool) × (Fin 256 → Bool) →
      (Fin 256 → Bool) × Coins P) (J : (Fin 256 → Bool) × Ciphertext P → Fin 256 → Bool)
    (dk : DecapsKey P) (c : Ciphertext P) : Fin 256 → Bool :=
  decapsWith (toExplicitCoinPKE P) G J dk c

/-- **Correctness of ML-KEM**: for an honest key `pk = (A, A s + e)` and a message `m` whose
derived coins `(G(m ‖ H(pk))).2 = (r, e₁, e₂)` keep every coefficient of the K-PKE decryption
noise within `B`, where `4 * B + 2 < q`, decapsulating the honest ciphertext
`Enc(pk, m; (G(m ‖ H(pk))).2)` produced by `kemEncaps` on message `m` returns its key. -/
theorem kemDecaps_encrypt_of_noise_le [NeZero P.q] {B : ℕ} (hB : 4 * B + 2 < P.q)
    (G : (Fin P.n → Bool) × (Fin 256 → Bool) → (Fin 256 → Bool) × Coins P)
    (H : PublicKey P → Fin 256 → Bool)
    (J : (Fin 256 → Bool) × Ciphertext P → Fin 256 → Bool)
    (A : Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q)) (s e : Fin P.k → Fin P.n → ZMod P.q)
    (z : Fin 256 → Bool) (m : Fin P.n → Bool)
    (r e₁ : Fin P.k → Fin P.n → ZMod P.q) (e₂ : Fin P.n → ZMod P.q)
    (hG : (G (m, H (moduleLWEKeyGen A s e))).2 = (r, e₁, e₂))
    (hnoise : ∀ i, (decryptionNoise P A s e r e₁ e₂ m i).valMinAbs.natAbs ≤ B) :
    let pk := moduleLWEKeyGen A s e
    let dk : DecapsKey P := { sk := s, pk := pk, pkHash := H pk, seed := z }
    kemDecaps P G J dk (encrypt P pk m (G (m, H pk)).2) = (G (m, H pk)).1 := by
  intro pk dk
  refine decapsWith_encT (toExplicitCoinPKE P) G J dk m ?_
  change some (decrypt P s (encrypt P (moduleLWEKeyGen A s e) m
    (G (m, H (moduleLWEKeyGen A s e))).2)) = some m
  rw [hG, decrypt_encrypt_eq_of_noise_le P hB A s e r e₁ e₂ m hnoise]

end Cslib.Crypto.MLKEM
