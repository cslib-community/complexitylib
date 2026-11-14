/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.HQC.PKE
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Words

/-!
# Word encodings for the expanded HQC core

The expanded HQC public key, encryption coins, ciphertext and DQCSD samples are encoded by their
fixed-width bit-string fields, in source order. The finite `PKEParams` value is static program data:
it fixes the field widths and therefore the types below. It is not omitted from concrete program
size; the separate description-specialization layer must charge its encoded value together with
the wrapper and controller.

These encodings contain no seed/XOF compression and no serialization format from the production
HQC implementation. They are the transparent word layout used by the machine-certified reduction.

## Main definitions

* `Cslib.Crypto.HQC.encPKEPublicKey`: two `n`-bit words `(h, s)`.
* `Cslib.Crypto.HQC.encPKECoins`: the three `n`-bit words `(r2, e, r1)`.
* `Cslib.Crypto.HQC.encPKECiphertext`: the `n`-bit word `u` and `n - ell`-bit word `v`.
* `Cslib.Crypto.HQC.encSyndromeSample`, `encTruncatedSyndromeSample`: the two DQCSD sample
  layouts consumed by the reductions.

## Main results

* `Cslib.Crypto.HQC.length_encPKEPublicKey`, `length_encPKECoins`,
  `length_encPKECiphertext`, `length_encSyndromeSample`,
  `length_encTruncatedSyndromeSample`: exact encoded-word lengths.
-/

@[expose] public section

namespace Cslib.Crypto.HQC

open Turing.MultiTapeTM

namespace PKEPublicKey

/-- An expanded public key is its two ring words in source order. -/
def equivProd (P : PKEParams) : PKEPublicKey P ≃ RingWord P × RingWord P where
  toFun pk := (pk.h, pk.s)
  invFun words := ⟨words.1, words.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end PKEPublicKey

/-- Transparent fixed-width encoding of an expanded public key `(h, s)`. -/
def encPKEPublicKey (P : PKEParams) : PKEPublicKey P ↪ List Bool :=
  encOfEquiv (PKEPublicKey.equivProd P)
    (encPair (encBitString P.n) (encBitString P.n))

@[simp] theorem encPKEPublicKey_apply (P : PKEParams) (pk : PKEPublicKey P) :
    encPKEPublicKey P pk = encPair (encBitString P.n) (encBitString P.n) (pk.h, pk.s) := rfl

/-- The public-key layout charges both fixed-width words and the framing of the first. -/
theorem length_encPKEPublicKey (P : PKEParams) (pk : PKEPublicKey P) :
    (encPKEPublicKey P pk).length = 3 * P.n + 1 := by
  simp only [encPKEPublicKey_apply, length_encPair, encBitString_apply, List.length_ofFn]
  omega

namespace PKECoins

/-- Encryption coins are the three ring words `(r2, e, r1)` in sampling order. -/
def equivProd (P : PKEParams) : PKECoins P ≃ RingWord P × (RingWord P × RingWord P) where
  toFun coins := (coins.r2, coins.e, coins.r1)
  invFun
    | (r2, e, r1) => ⟨r2, e, r1⟩
  left_inv _ := rfl
  right_inv _ := rfl

end PKECoins

/-- Transparent fixed-width encoding of encryption coins `(r2, e, r1)`. -/
def encPKECoins (P : PKEParams) : PKECoins P ↪ List Bool :=
  encOfEquiv (PKECoins.equivProd P)
    (encPair (encBitString P.n) (encPair (encBitString P.n) (encBitString P.n)))

@[simp] theorem encPKECoins_apply (P : PKEParams) (coins : PKECoins P) :
    encPKECoins P coins = encPair (encBitString P.n)
      (encPair (encBitString P.n) (encBitString P.n)) (coins.r2, coins.e, coins.r1) := rfl

/-- The coin layout charges all three fixed-width words and both pair framings. -/
theorem length_encPKECoins (P : PKEParams) (coins : PKECoins P) :
    (encPKECoins P coins).length = 5 * P.n + 2 := by
  simp only [encPKECoins_apply, length_encPair, encBitString_apply, List.length_ofFn]
  omega

namespace PKECiphertext

/-- An expanded ciphertext is its complete and truncated components. -/
def equivProd (P : PKEParams) : PKECiphertext P ≃ RingWord P × Codeword P where
  toFun ciphertext := (ciphertext.u, ciphertext.v)
  invFun words := ⟨words.1, words.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end PKECiphertext

/-- Transparent fixed-width encoding of an expanded ciphertext `(u, v)`. -/
def encPKECiphertext (P : PKEParams) : PKECiphertext P ↪ List Bool :=
  encOfEquiv (PKECiphertext.equivProd P)
    (encPair (encBitString P.n) (encBitString P.codeLen))

@[simp] theorem encPKECiphertext_apply (P : PKEParams) (ciphertext : PKECiphertext P) :
    encPKECiphertext P ciphertext = encPair (encBitString P.n) (encBitString P.codeLen)
      (ciphertext.u, ciphertext.v) := rfl

/-- The ciphertext layout charges both components and the framing of the complete word. -/
theorem length_encPKECiphertext (P : PKEParams) (ciphertext : PKECiphertext P) :
    (encPKECiphertext P ciphertext).length = 2 * P.n + 1 + P.codeLen := by
  simp only [encPKECiphertext_apply, length_encPair, encBitString_apply, List.length_ofFn]

namespace SyndromeSample

/-- A two-block DQCSD sample is its public block and syndrome value. -/
def equivProd (n : ℕ) : SyndromeSample n ≃ BitString n × BitString n where
  toFun sample := (sample.publicBlock, sample.value)
  invFun words := ⟨words.1, words.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end SyndromeSample

/-- Transparent fixed-width encoding of a two-block DQCSD sample. -/
def encSyndromeSample (n : ℕ) : SyndromeSample n ↪ List Bool :=
  encOfEquiv (SyndromeSample.equivProd n)
    (encPair (encBitString n) (encBitString n))

@[simp] theorem encSyndromeSample_apply (n : ℕ) (sample : SyndromeSample n) :
    encSyndromeSample n sample = encPair (encBitString n) (encBitString n)
      (sample.publicBlock, sample.value) := rfl

/-- The two-block sample layout charges both words and the framing of the first. -/
theorem length_encSyndromeSample (n : ℕ) (sample : SyndromeSample n) :
    (encSyndromeSample n sample).length = 3 * n + 1 := by
  simp only [encSyndromeSample_apply, length_encPair, encBitString_apply, List.length_ofFn]
  omega

namespace TruncatedSyndromeSample

/-- A truncated three-block sample groups its two public blocks and two syndrome values. -/
def equivProd (n m : ℕ) :
    TruncatedSyndromeSample n m ≃ (BitString n × BitString n) × (BitString n × BitString m) where
  toFun sample := ((sample.firstBlock, sample.secondBlock),
    (sample.firstValue, sample.secondValue))
  invFun
    | ((firstBlock, secondBlock), (firstValue, secondValue)) =>
      ⟨firstBlock, secondBlock, firstValue, secondValue⟩
  left_inv _ := rfl
  right_inv _ := rfl

end TruncatedSyndromeSample

/-- Transparent fixed-width encoding of a truncated three-block DQCSD sample. -/
def encTruncatedSyndromeSample (n m : ℕ) : TruncatedSyndromeSample n m ↪ List Bool :=
  encOfEquiv (TruncatedSyndromeSample.equivProd n m)
    (encPair (encPair (encBitString n) (encBitString n))
      (encPair (encBitString n) (encBitString m)))

@[simp] theorem encTruncatedSyndromeSample_apply (n m : ℕ)
    (sample : TruncatedSyndromeSample n m) :
    encTruncatedSyndromeSample n m sample =
      encPair (encPair (encBitString n) (encBitString n))
        (encPair (encBitString n) (encBitString m))
        ((sample.firstBlock, sample.secondBlock), (sample.firstValue, sample.secondValue)) := rfl

/-- The truncated three-block layout charges three `n`-bit words, one `m`-bit word and all
three pair framings. -/
theorem length_encTruncatedSyndromeSample (n m : ℕ)
    (sample : TruncatedSyndromeSample n m) :
    (encTruncatedSyndromeSample n m sample).length = 8 * n + m + 4 := by
  simp only [encTruncatedSyndromeSample_apply, length_encPair, encBitString_apply,
    List.length_ofFn]
  omega

end Cslib.Crypto.HQC
