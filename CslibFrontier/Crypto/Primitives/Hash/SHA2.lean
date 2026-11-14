/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.ByteString
import Mathlib.Data.List.GetD

/-!
# SHA-256 and SHA-512

This module implements the byte-aligned SHA-256 and SHA-512 hash functions from
[NIST FIPS 180-4][NISTFIPS1804]. Words are `BitVec 32` or `BitVec 64`, so addition and logical
operations have exactly the modular semantics required by Sections 4 and 6. Input bytes are parsed
big-endian, padding uses the 64-bit or 128-bit big-endian message-length field from Section 5.1,
and the output types record the 32-byte or 64-byte digest length.

The public input predicates enforce the source domains `ℓ < 2^64` for SHA-256 and `ℓ < 2^128`
for SHA-512, specialized to byte-aligned messages. This is a checked executable specification,
not a constant-time or machine-costed implementation, a security proof, or a claim of NIST
validation.

## Main definitions

* `Cslib.Crypto.SHA2.ValidSHA256Input`, `ValidSHA512Input`: FIPS 180-4 message-length domains.
* `Cslib.Crypto.SHA2.sha256Pad`, `sha512Pad`: byte-aligned Section 5.1 padding.
* `Cslib.Crypto.SHA2.sha256Compress`, `sha512Compress`: one-block compression functions.
* `Cslib.Crypto.SHA2.sha256`, `sha512`: typed 32-byte and 64-byte digests.

## References

* [National Institute of Standards and Technology, *Secure Hash Standard*, FIPS PUB 180-4,
  August 2015][NISTFIPS1804], Sections 4.1.2--4.2.3, 5.1--5.3, 6.2 and 6.4.
-/

public section

namespace Cslib.Crypto.SHA2

open Cslib.Crypto

/-- A SHA-256 word. -/
abbrev Word32 := BitVec 32

/-- A SHA-512 word. -/
abbrev Word64 := BitVec 64

/-- The eight-word SHA-256 chaining state. -/
abbrev SHA256State := Vector Word32 8

/-- The eight-word SHA-512 chaining state. -/
abbrev SHA512State := Vector Word64 8

/-- The FIPS 180-4 SHA-256 domain for a byte-aligned message: its bit length is below `2^64`. -/
@[expose] def ValidSHA256Input (input : List Byte) : Prop := input.length < 2 ^ 61

/-- The FIPS 180-4 SHA-512 domain for a byte-aligned message: its bit length is below `2^128`. -/
@[expose] def ValidSHA512Input (input : List Byte) : Prop := input.length < 2 ^ 125

instance (input : List Byte) : Decidable (ValidSHA256Input input) := by
  unfold ValidSHA256Input
  infer_instance

instance (input : List Byte) : Decidable (ValidSHA512Input input) := by
  unfold ValidSHA512Input
  infer_instance

/-- The 64 SHA-256 round constants from FIPS 180-4, Section 4.2.2. -/
def sha256Constants : List Word32 :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The 80 SHA-512 round constants from FIPS 180-4, Section 4.2.3. -/
def sha512Constants : List Word64 :=
  [0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

/-- The SHA-256 initial hash value from FIPS 180-4, Section 5.3.3. -/
def sha256InitialState : SHA256State := Vector.ofFn fun i =>
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19].getD i.val 0

/-- The SHA-512 initial hash value from FIPS 180-4, Section 5.3.5. -/
def sha512InitialState : SHA512State := Vector.ofFn fun i =>
  [0x6a09e667f3bcc908, 0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b, 0x5be0cd19137e2179].getD i.val 0

/-- FIPS 180-4 choice function. -/
private def choose {w : ℕ} (x y z : BitVec w) : BitVec w :=
  (x &&& y) ^^^ ((~~~ x) &&& z)

/-- FIPS 180-4 majority function. -/
private def majority {w : ℕ} (x y z : BitVec w) : BitVec w :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

private def bigSigma2560 (x : Word32) : Word32 :=
  x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

private def bigSigma2561 (x : Word32) : Word32 :=
  x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

private def smallSigma2560 (x : Word32) : Word32 :=
  x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)

private def smallSigma2561 (x : Word32) : Word32 :=
  x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)

private def bigSigma5120 (x : Word64) : Word64 :=
  x.rotateRight 28 ^^^ x.rotateRight 34 ^^^ x.rotateRight 39

private def bigSigma5121 (x : Word64) : Word64 :=
  x.rotateRight 14 ^^^ x.rotateRight 18 ^^^ x.rotateRight 41

private def smallSigma5120 (x : Word64) : Word64 :=
  x.rotateRight 1 ^^^ x.rotateRight 8 ^^^ (x >>> 7)

private def smallSigma5121 (x : Word64) : Word64 :=
  x.rotateRight 19 ^^^ x.rotateRight 61 ^^^ (x >>> 6)

/-- Pack four bytes as one big-endian SHA-256 word. -/
private def word32OfBytes (block : FixedBytes 64) (i : Fin 16) : Word32 :=
  BitVec.ofNat 32
    (block ⟨4 * i, by omega⟩ * 2 ^ 24 +
      block ⟨4 * i + 1, by omega⟩ * 2 ^ 16 +
      block ⟨4 * i + 2, by omega⟩ * 2 ^ 8 +
      block ⟨4 * i + 3, by omega⟩)

/-- Pack eight bytes as one big-endian SHA-512 word. -/
private def word64OfBytes (block : FixedBytes 128) (i : Fin 16) : Word64 :=
  BitVec.ofNat 64
    (block ⟨8 * i, by omega⟩ * 2 ^ 56 +
      block ⟨8 * i + 1, by omega⟩ * 2 ^ 48 +
      block ⟨8 * i + 2, by omega⟩ * 2 ^ 40 +
      block ⟨8 * i + 3, by omega⟩ * 2 ^ 32 +
      block ⟨8 * i + 4, by omega⟩ * 2 ^ 24 +
      block ⟨8 * i + 5, by omega⟩ * 2 ^ 16 +
      block ⟨8 * i + 6, by omega⟩ * 2 ^ 8 +
      block ⟨8 * i + 7, by omega⟩)

private def sha256Schedule (block : FixedBytes 64) : List Word32 :=
  (List.range 48).foldl (fun words _ =>
    let t := words.length
    words ++ [smallSigma2561 (words.getD (t - 2) 0) + words.getD (t - 7) 0 +
      smallSigma2560 (words.getD (t - 15) 0) + words.getD (t - 16) 0])
    (List.ofFn (word32OfBytes block))

private def sha512Schedule (block : FixedBytes 128) : List Word64 :=
  (List.range 64).foldl (fun words _ =>
    let t := words.length
    words ++ [smallSigma5121 (words.getD (t - 2) 0) + words.getD (t - 7) 0 +
      smallSigma5120 (words.getD (t - 15) 0) + words.getD (t - 16) 0])
    (List.ofFn (word64OfBytes block))

private def sha256Round (state : SHA256State) (roundData : Word32 × Word32) : SHA256State :=
  let t1 := state.get 7 + bigSigma2561 (state.get 4) +
    choose (state.get 4) (state.get 5) (state.get 6) + roundData.1 + roundData.2
  let t2 := bigSigma2560 (state.get 0) +
    majority (state.get 0) (state.get 1) (state.get 2)
  Vector.ofFn fun i =>
    [t1 + t2, state.get 0, state.get 1, state.get 2,
      state.get 3 + t1, state.get 4, state.get 5, state.get 6].getD i.val 0

private def sha512Round (state : SHA512State) (roundData : Word64 × Word64) : SHA512State :=
  let t1 := state.get 7 + bigSigma5121 (state.get 4) +
    choose (state.get 4) (state.get 5) (state.get 6) + roundData.1 + roundData.2
  let t2 := bigSigma5120 (state.get 0) +
    majority (state.get 0) (state.get 1) (state.get 2)
  Vector.ofFn fun i =>
    [t1 + t2, state.get 0, state.get 1, state.get 2,
      state.get 3 + t1, state.get 4, state.get 5, state.get 6].getD i.val 0

/-- One SHA-256 compression step on an exact 64-byte block (FIPS 180-4, Section 6.2.2). -/
def sha256Compress (state : SHA256State) (block : FixedBytes 64) : SHA256State :=
  let working := (sha256Constants.zip (sha256Schedule block)).foldl sha256Round state
  Vector.ofFn fun i => state.get i + working.get i

/-- One SHA-512 compression step on an exact 128-byte block (FIPS 180-4, Section 6.4.2). -/
def sha512Compress (state : SHA512State) (block : FixedBytes 128) : SHA512State :=
  let working := (sha512Constants.zip (sha512Schedule block)).foldl sha512Round state
  Vector.ofFn fun i => state.get i + working.get i

/-- Byte-aligned SHA-256 padding from FIPS 180-4, Section 5.1.1. -/
def sha256Pad (input : List Byte) : List Byte :=
  let zeroBytes := (56 + 64 - (input.length + 1) % 64) % 64
  input ++ [0x80] ++ List.replicate zeroBytes 0 ++
    (natToFixedBytesBE 8 (8 * input.length)).toList

/-- Byte-aligned SHA-512 padding from FIPS 180-4, Section 5.1.2. -/
def sha512Pad (input : List Byte) : List Byte :=
  let zeroBytes := (112 + 128 - (input.length + 1) % 128) % 128
  input ++ [0x80] ++ List.replicate zeroBytes 0 ++
    (natToFixedBytesBE 16 (8 * input.length)).toList

private def blockFromList (blockBytes : ℕ) (input : List Byte) (block : ℕ) :
    FixedBytes blockBytes := fun i => input.getD (block * blockBytes + i.val) 0

private def sha256State (input : List Byte) : SHA256State :=
  let padded := sha256Pad input
  (List.range (padded.length / 64)).foldl
    (fun state block => sha256Compress state (blockFromList 64 padded block)) sha256InitialState

private def sha512State (input : List Byte) : SHA512State :=
  let padded := sha512Pad input
  (List.range (padded.length / 128)).foldl
    (fun state block => sha512Compress state (blockFromList 128 padded block)) sha512InitialState

private def sha256StateBytes (state : SHA256State) : FixedBytes 32 := fun i =>
  ⟨(state.get ⟨i.val / 4, by omega⟩).toNat / 2 ^ (8 * (3 - i.val % 4)) % 256,
    Nat.mod_lt _ (by decide)⟩

private def sha512StateBytes (state : SHA512State) : FixedBytes 64 := fun i =>
  ⟨(state.get ⟨i.val / 8, by omega⟩).toNat / 2 ^ (8 * (7 - i.val % 8)) % 256,
    Nat.mod_lt _ (by decide)⟩

/-- SHA-256 on a byte-aligned message in the FIPS 180-4 input domain. -/
def sha256 (input : List Byte) (_h : ValidSHA256Input input) : FixedBytes 32 :=
  sha256StateBytes (sha256State input)

/-- SHA-512 on a byte-aligned message in the FIPS 180-4 input domain. -/
def sha512 (input : List Byte) (_h : ValidSHA512Input input) : FixedBytes 64 :=
  sha512StateBytes (sha512State input)

end Cslib.Crypto.SHA2
