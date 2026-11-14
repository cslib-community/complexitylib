/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Hash.Sponge

/-!
# Keccak-p[1600, 24] and SHAKE256

This module implements the concrete permutation and byte-aligned extendable-output function from
[NIST FIPS 202][NISTFIPS202]. The state is a `5 × 5` array of 64-bit lanes. Lane bit `z` is the
standard's `A[x, y, z]`, and a flat state bit at position `64 * (5 * y + x) + z` maps to that
coordinate (Sections 3.1.2--3.1.3). The five round steps follow Algorithms 1--7 and Tables 1--2
in Sections 3.2--3.3; `keccakP1600Rounds24` is Algorithm 8's underlying function as specified in
Section 4.

`shake256` implements Algorithms 8--9 and Section 6.2 for byte-aligned messages: bytes are
expanded least significant bit first, matching NIST's official SHAKE256 example state dumps; the
SHAKE suffix `1111` and `pad10*1` are appended; the 1088-bit rate blocks are processed by the
existing `Cslib.Crypto.Sponge.hashBlocks`; and output bytes are assembled in the same convention.

This is a checked executable specification, not a constant-time or efficient implementation, a
cryptographic security proof, or a claim of validation under FIPS 202. It maps to the published
August 2015 standard and does not claim agreement with a future revision or with FN-DSA / FIPS 206.

## Main definitions

* `Cslib.Crypto.Keccak.State`: a `5 × 5` array of 64-bit lanes.
* `Cslib.Crypto.Keccak.theta`, `rho`, `pi`, `chi`, `iota`: the five FIPS 202 round steps.
* `Cslib.Crypto.Keccak.keccakP1600Rounds24`: the 24-round state transformation.
* `Cslib.Crypto.Keccak.keccakP1600Rounds24Sponge`: the transformation on the generic sponge
  module's rate/capacity state split.
* `Cslib.Crypto.Keccak.byteBitsLE`, `bytesToBitsLE`, `bitsToByteLE`: the explicit FIPS 202
  least-significant-bit-first byte boundary.
* `Cslib.Crypto.Keccak.shake256`: byte-aligned SHAKE256 with an output length in bytes.

## Main results

* `Cslib.Crypto.Keccak.length_shake256`: SHAKE256 returns exactly the requested byte count.

## References

* [National Institute of Standards and Technology, *SHA-3 Standard: Permutation-Based Hash and
  Extendable-Output Functions*, FIPS PUB 202, August 2015][NISTFIPS202], Sections 3.1.2--3.3,
  Algorithms 1--9, Tables 1--2 and Section 6.2.
* NIST, [official SHAKE256 examples for the 0-bit and 1600-bit
  messages](https://csrc.nist.gov/projects/cryptographic-standards-and-guidelines/example-values).
-/

public section

namespace Cslib.Crypto.Keccak

open Cslib

/-- A 64-bit lane in the Keccak-p[1600] state. Bit-vector position zero is coordinate `z = 0`. -/
abbrev Lane := BitVec 64

/-- The 25 lanes of a Keccak-p[1600] state in FIPS 202's flat order `5 * y + x`.

The vector representation makes each round materialize all lanes once. This avoids the exponential
recomputation that would result from composing 24 rounds as nested state functions. -/
abbrev State := Vector Lane 25

/-- The sponge rate and capacity views used by SHAKE256. -/
abbrev SpongeState := BitString 1088 × BitString 512

/-- Reduce a natural-number state coordinate modulo five. -/
@[expose] def coordinate (n : ℕ) : Fin 5 :=
  ⟨n % 5, Nat.mod_lt _ (by decide)⟩

/-- The flat FIPS 202 lane index corresponding to state coordinates `(x, y)`. -/
@[expose] def laneIndex (x y : Fin 5) : Fin 25 :=
  ⟨5 * y.val + x.val, by omega⟩

/-- Read the Keccak state lane `A[x, y]`. -/
@[expose] def getLane (A : State) (x y : Fin 5) : Lane :=
  A.get (laneIndex x y)

/-- The rotation offset for lane `(x, y)`, from FIPS 202 Table 2, reduced modulo 64. -/
@[expose] def rotationOffset (x y : Fin 5) : ℕ :=
  [0, 1, 62, 28, 27,
    36, 44, 6, 55, 20,
    3, 10, 43, 25, 39,
    41, 45, 15, 21, 8,
    18, 2, 61, 56, 14].getD (5 * y.val + x.val) 0

/-- The 24 round constants for Keccak-f[1600], in round order. -/
@[expose] def roundConstants : List Lane :=
  [0x0000000000000001, 0x0000000000008082, 0x800000000000808A,
    0x8000000080008000, 0x000000000000808B, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008A,
    0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800A, 0x800000008000000A, 0x8000000080008081,
    0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- FIPS 202 Algorithm 1, the column-parity step `θ`. -/
@[expose] def theta (A : State) : State :=
  let column : Vector Lane 5 := Vector.ofFn fun x =>
    getLane A x 0 ^^^ getLane A x 1 ^^^ getLane A x 2 ^^^ getLane A x 3 ^^^ getLane A x 4
  let delta : Vector Lane 5 := Vector.ofFn fun x =>
    column.get (coordinate (x.val + 4)) ^^^
      (column.get (coordinate (x.val + 1))).rotateLeft 1
  Vector.ofFn fun lane =>
    A.get lane ^^^ delta.get (coordinate lane.val)

/-- FIPS 202 Algorithm 2, the lane-rotation step `ρ`. -/
@[expose] def rho (A : State) : State :=
  Vector.ofFn fun lane =>
    let x := coordinate lane.val
    let y : Fin 5 := ⟨lane.val / 5, by omega⟩
    (A.get lane).rotateLeft (rotationOffset x y)

/-- FIPS 202 Algorithm 3, the lane-permutation step `π`. -/
@[expose] def pi (A : State) : State :=
  Vector.ofFn fun lane =>
    let x := coordinate lane.val
    let y : Fin 5 := ⟨lane.val / 5, by omega⟩
    getLane A (coordinate (x.val + 3 * y.val)) x

/-- FIPS 202 Algorithm 4, the nonlinear row step `χ`. -/
@[expose] def chi (A : State) : State :=
  Vector.ofFn fun lane =>
    let x := coordinate lane.val
    let y : Fin 5 := ⟨lane.val / 5, by omega⟩
    getLane A x y ^^^
      ((~~~ getLane A (coordinate (x.val + 1)) y) &&&
        getLane A (coordinate (x.val + 2)) y)

/-- FIPS 202 Algorithm 6, the round-constant step `ι`. -/
@[expose] def iota (constant : Lane) (A : State) : State :=
  Vector.ofFn fun lane =>
    if lane.val = 0 then A.get lane ^^^ constant else A.get lane

/-- One FIPS 202 round: `ι ∘ χ ∘ π ∘ ρ ∘ θ`. -/
@[expose] def round (constant : Lane) (A : State) : State :=
  iota constant (chi (pi (rho (theta A))))

/-- FIPS 202 `KECCAK-p[1600, 24]`, equivalently `KECCAK-f[1600]`, on lane arrays. -/
@[expose] def keccakP1600Rounds24 (A : State) : State :=
  roundConstants.foldl (fun state constant => round constant state) A

/-- Pack 64 least-significant-bit-first coordinates into a lane. -/
@[expose] def laneOfBits (bits : BitString 64) : Lane :=
  BitVec.ofFin (BitString.equivFin 64 bits)

/-- Convert the SHAKE256 rate/capacity split into the FIPS 202 lane array. -/
@[expose] def ofSpongeState (state : SpongeState) : State :=
  Vector.ofFn fun lane =>
    if hlane : lane.val < 17 then
      laneOfBits fun z => state.1 ⟨64 * lane.val + z.val, by omega⟩
    else
      laneOfBits fun z => state.2 ⟨64 * (lane.val - 17) + z.val, by omega⟩

/-- Read a lane by its flat FIPS 202 index `5 * y + x`. -/
@[expose] def laneAt (A : State) (lane : Fin 25) : Lane :=
  A.get lane

/-- Convert the FIPS 202 lane array into SHAKE256's 1088-bit rate and 512-bit capacity split. -/
@[expose] def toSpongeState (A : State) : SpongeState :=
  (fun i =>
      (laneAt A ⟨i.val / 64, by omega⟩).getLsbD (i.val % 64),
    fun i =>
      (laneAt A ⟨17 + i.val / 64, by omega⟩).getLsbD (i.val % 64))

/-- FIPS 202 `KECCAK-p[1600, 24]` on SHAKE256's rate/capacity state split. -/
@[expose] def keccakP1600Rounds24Sponge (state : SpongeState) : SpongeState :=
  toSpongeState (keccakP1600Rounds24 (ofSpongeState state))

/-- Expand a byte into FIPS 202 bit-string order, least significant bit first. -/
@[expose] def byteBitsLE (byte : Fin 256) : List Bool :=
  (List.range 8).map byte.val.testBit

/-- Expand a byte string into FIPS 202 bit-string order. -/
@[expose] def bytesToBitsLE (bytes : List (Fin 256)) : List Bool :=
  bytes.flatMap byteBitsLE

/-- FIPS 202 Algorithm 9, `pad10*1(x, m)`. -/
@[expose] def pad10star1 (x m : ℕ) : List Bool :=
  true :: List.replicate ((x - (m + 2) % x) % x) false ++ [true]

/-- Pack the first eight least-significant-bit-first coordinates into a byte. -/
@[expose] def bitsToByteLE (bits : List Bool) : Fin 256 :=
  let value := (List.range 8).foldl
    (fun acc i => acc + if bits.getD i false then 2 ^ i else 0) 0
  ⟨value % 256, Nat.mod_lt _ (by decide)⟩

/-- Byte-aligned SHAKE256 from FIPS 202 Section 6.2.

The second argument is the requested output length in bytes. The output length affects only how
much of the XOF stream is returned, not the preceding bytes. -/
@[expose] def shake256 (input : List (Fin 256)) (outputBytes : ℕ) : List (Fin 256) :=
  let suffixed := bytesToBitsLE input ++ [true, true, true, true]
  let padded := suffixed ++ pad10star1 1088 suffixed.length
  let blocks := Sponge.toBlocks 1088 padded
  let outputBlockCount := (8 * outputBytes + 1087) / 1088
  let outputBits :=
    (Sponge.hashBlocks keccakP1600Rounds24Sponge Prod.fst outputBlockCount blocks).flatMap List.ofFn
  (List.range outputBytes).map fun i => bitsToByteLE (outputBits.drop (8 * i))

/-- SHAKE256 returns exactly the requested number of bytes. -/
@[simp] theorem length_shake256 (input : List (Fin 256)) (outputBytes : ℕ) :
    (shake256 input outputBytes).length = outputBytes := by
  simp [shake256]

/-- Requesting no bytes returns the empty output. -/
@[simp] theorem shake256_zero_output (input : List (Fin 256)) : shake256 input 0 = [] := rfl

end Cslib.Crypto.Keccak
