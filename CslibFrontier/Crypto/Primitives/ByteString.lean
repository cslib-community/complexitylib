/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import CslibFrontier.Init

/-!
# Byte strings

This module supplies the byte boundary shared by executable cryptographic primitives. A byte is an
unsigned integer below 256, and `FixedBytes n` records a byte-string length in its type. The
big-endian bit conversion follows the byte convention used by FIPS 180-4 and FIPS 205; primitives
with a different within-byte convention, such as FIPS 202's Keccak, keep that conversion explicit.

## Main definitions

* `Cslib.Crypto.Byte`: one unsigned byte.
* `Cslib.Crypto.FixedBytes`: a byte string whose length is part of its type.
* `Cslib.Crypto.bytesToBitsBE`: big-endian serialization of a list of bytes.
* `Cslib.Crypto.bitsToFixedBytesBE`: split a bit list into typed big-endian bytes.

## Main results

* `Cslib.Crypto.length_bytesToBitsBE`: byte serialization has eight bits per byte.
* `Cslib.Crypto.byteOfBitsBE_byteBitsBE`: converting one byte to bits and back is exact.
-/

public section

namespace Cslib.Crypto

open Cslib.BitString

/-- One byte, represented by its unsigned integer value. -/
abbrev Byte := Fin (2 ^ 8)

/-- A byte string whose byte length is part of its type. -/
abbrev FixedBytes (n : ℕ) := Fin n → Byte

namespace FixedBytes

/-- The list view of a fixed-length byte string. -/
def toList {n : ℕ} (X : FixedBytes n) : List Byte := List.ofFn X

/-- The list view has the byte length recorded in the type. -/
@[simp] theorem length_toList {n : ℕ} (X : FixedBytes n) : X.toList.length = n := by
  simp [toList]

/-- The first `m` bytes of a fixed byte string, with the bound checked at the type boundary. -/
def take {n : ℕ} (m : ℕ) (h : m ≤ n) (X : FixedBytes n) : FixedBytes m := fun i =>
  X ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

/-- Concatenate two fixed-length byte strings. -/
def append {m n : ℕ} (X : FixedBytes m) (Y : FixedBytes n) : FixedBytes (m + n) :=
  fun i => if h : i.val < m then X ⟨i.val, h⟩ else Y ⟨i.val - m, by omega⟩

end FixedBytes

/-- The eight big-endian bits of a byte. -/
@[expose]
def byteBitsBE (x : Byte) : List Bool := binaryWord 8 x

/-- The bits of a byte list in big-endian order within each byte. -/
@[expose]
def bytesToBitsBE : List Byte → List Bool
  | [] => []
  | x :: X => byteBitsBE x ++ bytesToBitsBE X

/-- A byte list has eight serialized bits per byte. -/
@[simp] theorem length_bytesToBitsBE (X : List Byte) :
    (bytesToBitsBE X).length = 8 * X.length := by
  induction X with
  | nil => simp [bytesToBitsBE]
  | cons x X ih =>
    simp only [bytesToBitsBE, byteBitsBE, List.length_append, ih, List.length_cons]
    rw [length_binaryWord x.isLt]
    omega

/-- Read at most eight big-endian bits as one byte. Missing low-order bits are not added; callers
that require a full byte should supply an eight-bit chunk. -/
def byteOfBitsBE (bits : List Bool) : Byte :=
  ⟨binaryValue (bits.take 8), by
    exact Nat.lt_of_lt_of_le (binaryValue_lt_two_pow (bits.take 8))
      (Nat.pow_le_pow_right (by decide) (List.length_take_le 8 bits))⟩

/-- Serializing one byte to eight big-endian bits and reading it back recovers the byte. -/
@[simp] theorem byteOfBitsBE_byteBitsBE (x : Byte) : byteOfBitsBE (byteBitsBE x) = x := by
  apply Fin.ext
  change binaryValue ((binaryWord 8 x).take 8) = x
  have hlength : (binaryWord 8 x).length = 8 := length_binaryWord x.isLt
  rw [List.take_of_length_le (Nat.le_of_eq hlength)]
  exact binaryValue_binaryWord 8 x

/-- Split a bit list into `n` consecutive big-endian bytes. An incomplete or absent final chunk is
read using `byteOfBitsBE`; exact-length clients avoid that fallback by construction. -/
def bitsToFixedBytesBE (n : ℕ) (bits : List Bool) : FixedBytes n := fun i =>
  byteOfBitsBE ((bits.drop (8 * i.val)).take 8)

/-- Encode a natural number as exactly `n` big-endian bytes, retaining its low `8n` bits. -/
def natToFixedBytesBE (n value : ℕ) : FixedBytes n := fun i =>
  ⟨value / 2 ^ (8 * (n - 1 - i.val)) % 256, Nat.mod_lt _ (by decide)⟩

end Cslib.Crypto
