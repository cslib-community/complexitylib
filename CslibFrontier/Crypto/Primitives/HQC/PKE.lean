/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.HQC.Syndrome
public import CslibFrontier.Crypto.Protocols.PKE.ExplicitCoin
import CslibFrontier.Foundations.Data.BitString.Circulant
import CslibFrontier.Probability.PMF.Support

/-!
# The ideal algebraic HQC public-key encryption core

This file formalizes the binary algebra of HQC-PKE after its seeds and XOF streams have been
expanded. It follows [HQC2026], §3.6, Algorithms `HQC-PKE.Keygen`, `HQC-PKE.Encrypt` and
`HQC-PKE.Decrypt`, pp. 38–40. The public ring is represented by bit strings and multiplication by
Mathlib's circulant matrix-vector product, consistently with the HQC syndrome distributions.

The ideal key generator draws `y`, then `x`, uniformly at fixed weight `ω`, followed by uniform `h`;
it publishes `(h, s = x + h * y)` and retains `y` as the secret key. Encryption draws `(r₂, e, r₁)`
at weights `(ωᵣ, ωₑ, ωᵣ)` in the source order and returns
`(u, v) = (r₁ + h * r₂, Encode(m) + Truncate(s * r₂ + e, ℓ))`. Here `Truncate(_, ℓ)` removes
the last `ℓ` coordinates, so its result has length `n - ℓ`. Decryption applies `Decode` to
`v - Truncate(u * y, ℓ)`; subtraction is addition in the Boolean ring.

The decryption phase is the encoded message plus the retained prefix of
`e' = x * r₂ - r₁ * y + e`. Consequently any decoder that corrects every error of weight at most
`Δ` recovers the message whenever that retained error has weight at most `Δ`.

This is an ideal expanded-value model, not the byte-level scheme. In particular, it does not
model seed splitting, XOF state, byte encodings, the concrete concatenated Reed–Muller/Reed–Solomon
code, primitive-prime admissibility, the decryption-failure rate, or any PKE/KEM security claim.

## Main definitions

* `Cslib.Crypto.HQC.PKEParams`: ideal algebraic parameters and their finite support bounds.
* `Cslib.Crypto.HQC.pkeKeyGen`, `Cslib.Crypto.HQC.pkeSampleCoins`: the ideal expanded samplers.
* `Cslib.Crypto.HQC.pkeEncrypt`, `Cslib.Crypto.HQC.pkeDecrypt`: deterministic HQC-PKE.
* `Cslib.Crypto.HQC.DecoderCorrects`: bounded-error correction for plain encoder/decoder functions.
* `Cslib.Crypto.HQC.toExplicitCoinPKE`: the core as an explicit-coin PKE.

## Main results

* `Cslib.Crypto.HQC.pkeDecryptInput_encrypt`: the exact retained-error phase identity.
* `Cslib.Crypto.HQC.pkeDecrypt_encrypt_eq_of_weight_le`: deterministic bounded-error correctness.
* `Cslib.Crypto.HQC.pkeKeyGen_support`, `Cslib.Crypto.HQC.pkeSampleCoins_support`: sampled keys and
  coins have exactly the source's fixed weights.

## References

* [HQC specification, version 5.1][HQC2026], §3.6, pp. 38–40.
-/

public section

namespace Cslib.Crypto.HQC

open Matrix BitString Probability Cslib.Crypto.Protocols

/-- Parameters of the ideal algebraic HQC-PKE core. The source uses positive values and
`0 < ℓ < n`; this finite model also admits boundary cases, while retaining all sampling bounds
needed to define the fixed-weight laws. -/
structure PKEParams where
  /-- Length `n` of vectors in the quasi-cyclic ring. -/
  n : ℕ
  /-- Message length `k`. -/
  k : ℕ
  /-- Number `ℓ` of trailing coordinates removed from ring words. -/
  ell : ℕ
  /-- Secret-vector weight `ω`. -/
  omega : ℕ
  /-- Encryption-vector weight `ωᵣ`. -/
  omegaR : ℕ
  /-- Encryption-error weight `ωₑ`. -/
  omegaE : ℕ
  /-- Number `Δ` of retained errors corrected by the code. -/
  delta : ℕ
  /-- Truncation cannot remove more than the complete ring word. -/
  ell_le_n : ell ≤ n
  /-- Secret supports fit in the ring word. -/
  omega_le_n : omega ≤ n
  /-- Encryption-vector supports fit in the ring word. -/
  omegaR_le_n : omegaR ≤ n
  /-- Encryption-error supports fit in the ring word. -/
  omegaE_le_n : omegaE ≤ n

namespace PKEParams

/-- Length `n - ℓ` of the codeword and second ciphertext component. -/
abbrev codeLen (P : PKEParams) : ℕ := P.n - P.ell

theorem codeLen_add_ell (P : PKEParams) : P.codeLen + P.ell = P.n := by
  exact Nat.sub_add_cancel P.ell_le_n

end PKEParams

/-- A ring word in the ideal HQC algebra. -/
abbrev RingWord (P : PKEParams) := BitString P.n

/-- An HQC-PKE message. -/
abbrev PKEMessage (P : PKEParams) := BitString P.k

/-- A word in the image space of the inner error-correcting code. -/
abbrev Codeword (P : PKEParams) := BitString P.codeLen

/-- An expanded HQC-PKE public key `(h, s)`. -/
structure PKEPublicKey (P : PKEParams) where
  /-- Generator `h` of the public circulant. -/
  h : RingWord P
  /-- Syndrome `s = x + h * y`. -/
  s : RingWord P
  deriving DecidableEq

/-- The expanded HQC-PKE secret key is the fixed-weight word `y`. The key-generation witness `x`
is intentionally not part of the decryption key. -/
abbrev PKESecretKey (P : PKEParams) := RingWord P

/-- Explicit HQC-PKE encryption coins, in the source's sampling order `(r₂, e, r₁)`. -/
structure PKECoins (P : PKEParams) where
  /-- Second random fixed-weight ring word. -/
  r2 : RingWord P
  /-- Additive fixed-weight error. -/
  e : RingWord P
  /-- First random fixed-weight ring word. -/
  r1 : RingWord P
  deriving DecidableEq

/-- An expanded HQC-PKE ciphertext `(u, v)`. -/
structure PKECiphertext (P : PKEParams) where
  /-- Complete quasi-cyclic component `u`. -/
  u : RingWord P
  /-- Truncated codeword component `v`. -/
  v : Codeword P
  deriving DecidableEq

/-- Remove the last `ℓ` coordinates of a ring word, retaining the prefix of length `n - ℓ`. -/
@[expose] def truncate (P : PKEParams) (x : RingWord P) : Codeword P :=
  x ∘ Fin.castLEEmb (show P.codeLen ≤ P.n by
    simpa only [PKEParams.codeLen] using Nat.sub_le P.n P.ell)

/-- Truncation commutes with Boolean-ring addition. -/
theorem truncate_add (P : PKEParams) (x y : RingWord P) :
    truncate P (x + y) = truncate P x + truncate P y := by
  rfl

/-- The ideal fixed-weight ring-word sampler, obtained from the already verified ideal HQC
support sampler. -/
noncomputable def sampleFixedWeight (P : PKEParams) (w : ℕ) : ProbComp (RingWord P) :=
  indicatorVector P.n <$> sampleSupportFrom (idealCandidate P.n) 0 w

/-- The ideal ring-word sampler is exactly uniform on the requested weight layer. -/
theorem eval_sampleFixedWeight (P : PKEParams) {w : ℕ} (hw : w ≤ P.n) :
    ProbComp.eval (sampleFixedWeight P w) =
      PMF.uniformOfFinset (weightLayer P.n w) (weightLayer_nonempty hw) := by
  simpa only [sampleFixedWeight, ProbComp.eval_map] using
    eval_idealSupport_map_indicatorVector hw

/-- Every supported ideal sample has exactly the requested weight. -/
theorem weight_of_mem_support_sampleFixedWeight (P : PKEParams) {w : ℕ} (hw : w ≤ P.n)
    {x : RingWord P} (hx : x ∈ (ProbComp.eval (sampleFixedWeight P w)).support) :
    weight x = w := by
  rw [eval_sampleFixedWeight P hw] at hx
  exact mem_weightLayer.mp ((PMF.mem_support_uniformOfFinset_iff _ x).mp hx)

/-- The expanded public key determined by public word `h` and secret witnesses `x, y`. -/
@[expose] def expandedPublicKey (P : PKEParams) (h x y : RingWord P) : PKEPublicKey P :=
  ⟨h, syndrome h x y⟩

/-- Ideal expanded HQC-PKE key generation. It samples `y` before `x`, as the source does, and
returns only `y` as the decryption key. -/
noncomputable def pkeKeyGen (P : PKEParams) : ProbComp (PKEPublicKey P × PKESecretKey P) := do
  let y ← sampleFixedWeight P P.omega
  let x ← sampleFixedWeight P P.omega
  let h ← ProbComp.uniform (RingWord P)
  return (expandedPublicKey P h x y, y)

/-- Every supported key pair has fixed-weight witnesses for the published syndrome, while the
actual secret key is exactly the sampled `y`. -/
theorem pkeKeyGen_support (P : PKEParams) {keys : PKEPublicKey P × PKESecretKey P}
    (hkeys : keys ∈ (ProbComp.eval (pkeKeyGen P)).support) :
    ∃ h x y : RingWord P,
      weight x = P.omega ∧ weight y = P.omega ∧ keys = (expandedPublicKey P h x y, y) := by
  simp only [pkeKeyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at hkeys
  obtain ⟨y, hy, x, hx, h, _, rfl⟩ := hkeys
  exact ⟨h, x, y,
    weight_of_mem_support_sampleFixedWeight P P.omega_le_n hx,
    weight_of_mem_support_sampleFixedWeight P P.omega_le_n hy, rfl⟩

/-- Ideal HQC-PKE encryption-coin sampling, in source order `r₂`, `e`, then `r₁`. -/
noncomputable def pkeSampleCoins (P : PKEParams) : ProbComp (PKECoins P) := do
  let r2 ← sampleFixedWeight P P.omegaR
  let e ← sampleFixedWeight P P.omegaE
  let r1 ← sampleFixedWeight P P.omegaR
  return ⟨r2, e, r1⟩

/-- Every supported encryption coin triple has exactly the source's three fixed weights. -/
theorem pkeSampleCoins_support (P : PKEParams) {coins : PKECoins P}
    (hcoins : coins ∈ (ProbComp.eval (pkeSampleCoins P)).support) :
    weight coins.r2 = P.omegaR ∧ weight coins.e = P.omegaE ∧ weight coins.r1 = P.omegaR := by
  simp only [pkeSampleCoins, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at hcoins
  obtain ⟨r2, hr2, e, he, r1, hr1, rfl⟩ := hcoins
  exact ⟨weight_of_mem_support_sampleFixedWeight P P.omegaR_le_n hr2,
    weight_of_mem_support_sampleFixedWeight P P.omegaE_le_n he,
    weight_of_mem_support_sampleFixedWeight P P.omegaR_le_n hr1⟩

/-- Deterministic expanded HQC-PKE encryption. -/
@[expose] def pkeEncrypt (P : PKEParams) (encode : PKEMessage P → Codeword P)
    (pk : PKEPublicKey P) (m : PKEMessage P) (coins : PKECoins P) : PKECiphertext P :=
  ⟨coins.r1 + circulant pk.h *ᵥ coins.r2,
    encode m + truncate P (circulant pk.s *ᵥ coins.r2 + coins.e)⟩

/-- The word supplied to the error-correcting decoder during decryption. Subtraction in the source
is addition in the Boolean ring. -/
@[expose] def pkeDecryptInput (P : PKEParams) (sk : PKESecretKey P) (ct : PKECiphertext P) :
    Codeword P :=
  ct.v + truncate P (circulant ct.u *ᵥ sk)

/-- Deterministic expanded HQC-PKE decryption. -/
@[expose] def pkeDecrypt (P : PKEParams) (decode : Codeword P → PKEMessage P)
    (sk : PKESecretKey P) (ct : PKECiphertext P) : PKEMessage P :=
  decode (pkeDecryptInput P sk ct)

/-- The complete error word from the source's correctness calculation. Its two subtractions are
additions because the coefficient ring is Boolean. -/
@[expose] def pkeDecryptionNoise (P : PKEParams) (x y : RingWord P) (coins : PKECoins P) :
    RingWord P :=
  circulant x *ᵥ coins.r2 + circulant coins.r1 *ᵥ y + coins.e

private theorem mixed_circulant_mulVec (P : PKEParams) (h y r2 : RingWord P) :
    circulant (circulant h *ᵥ y) *ᵥ r2 = circulant (circulant h *ᵥ r2) *ᵥ y := by
  rw [circulant_mulVec_assoc, circulant_mulVec_comm y r2, ← circulant_mulVec_assoc]

/-- **HQC-PKE decryption phase.** For an honestly formed expanded key and ciphertext, the decoder
input is the encoded message plus the retained prefix of
`e' = x * r₂ - r₁ * y + e`. -/
theorem pkeDecryptInput_encrypt (P : PKEParams) (encode : PKEMessage P → Codeword P)
    (h x y : RingWord P) (m : PKEMessage P) (coins : PKECoins P) :
    pkeDecryptInput P y (pkeEncrypt P encode (expandedPublicKey P h x y) m coins) =
      encode m + truncate P (pkeDecryptionNoise P x y coins) := by
  rw [pkeDecryptInput, pkeEncrypt, expandedPublicKey, syndrome]
  simp only [circulant_add, add_mulVec, truncate_add, pkeDecryptionNoise]
  have hmix : circulant (circulant h *ᵥ y) *ᵥ coins.r2 =
      circulant (circulant h *ᵥ coins.r2) *ᵥ y :=
    mixed_circulant_mulVec P h y coins.r2
  rw [hmix]
  abel_nf
  rw [two_smul, BitString.add_self]
  simp only [zero_add]

/-- A decoder corrects up to `Δ` errors when it recovers every message from its encoding plus any
error word of Hamming weight at most `Δ`. This follows the plain encoder/decoder convention used
by the binary symmetric channel API, without introducing a separate code hierarchy. -/
@[expose] def DecoderCorrects (P : PKEParams) (encode : PKEMessage P → Codeword P)
    (decode : Codeword P → PKEMessage P) : Prop :=
  ∀ m error, weight error ≤ P.delta → decode (encode m + error) = m

/-- **Deterministic bounded-error correctness of ideal HQC-PKE.** -/
theorem pkeDecrypt_encrypt_eq_of_weight_le (P : PKEParams)
    (encode : PKEMessage P → Codeword P) (decode : Codeword P → PKEMessage P)
    (hcorrect : DecoderCorrects P encode decode) (h x y : RingWord P)
    (m : PKEMessage P) (coins : PKECoins P)
    (hnoise : weight (truncate P (pkeDecryptionNoise P x y coins)) ≤ P.delta) :
    pkeDecrypt P decode y (pkeEncrypt P encode (expandedPublicKey P h x y) m coins) = m := by
  rw [pkeDecrypt, pkeDecryptInput_encrypt]
  exact hcorrect m _ hnoise

/-- The ideal algebraic HQC core as an explicit-coin public-key encryption scheme. Decryption is
total, so its result is wrapped in `some`. -/
@[expose] noncomputable def toExplicitCoinPKE (P : PKEParams)
    (encode : PKEMessage P → Codeword P)
    (decode : Codeword P → PKEMessage P) :
    ExplicitCoinPKE (PKEPublicKey P) (PKESecretKey P) (PKEMessage P) (PKECoins P)
      (PKECiphertext P) where
  keyGen := pkeKeyGen P
  sampleCoins := pkeSampleCoins P
  encDet := pkeEncrypt P encode
  dec sk ct := some (pkeDecrypt P decode sk ct)

end Cslib.Crypto.HQC
