/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Hash.Sponge
public import CslibFrontier.Foundations.Data.BitString.Binary
public import Mathlib.Algebra.Order.Floor.Div

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
* `Cslib.Crypto.Keccak.rateBytes`: the 136-byte view of one SHAKE256 rate block.
* `Cslib.Crypto.Keccak.squeezeBytes`: the byte stream from a requested number of squeezing blocks.
* `Cslib.Crypto.Keccak.shake256`: byte-aligned SHAKE256 with an output length in bytes.

## Main results

* `Cslib.Crypto.Keccak.bitsToByteLE_byteBitsLE`, `byteBitsLE_bitsToByteLE`: the byte boundary
  round trips.
* `Cslib.Crypto.Keccak.toSpongeState_ofSpongeState`, `ofSpongeState_toSpongeState`: the two state
  views are inverse.
* `Cslib.Crypto.Keccak.length_shake256`, `take_shake256`: SHAKE256 returns exactly the requested
  byte count, and longer requests preserve the preceding XOF bytes.

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

/-- Reading an in-range coordinate of `laneOfBits` returns the corresponding input bit. -/
private theorem getLsbD_laneOfBits (bits : BitString 64) (i : ℕ) (hi : i < 64) :
    (laneOfBits bits).getLsbD i = bits ⟨i, hi⟩ := by
  rw [laneOfBits, BitVec.getLsbD_ofFin]
  exact BitString.testBit_equivFin bits ⟨i, hi⟩

/-- Convert the SHAKE256 rate/capacity split into the FIPS 202 lane array. -/
@[expose] def ofSpongeState (state : SpongeState) : State :=
  Vector.ofFn fun lane =>
    if hlane : lane.val < 17 then
      laneOfBits fun z => state.1 ⟨64 * lane.val + z.val, by omega⟩
    else
      laneOfBits fun z => state.2 ⟨64 * (lane.val - 17) + z.val, by omega⟩

/-- A lane in the rate region reads the corresponding 64 rate coordinates. -/
theorem get_ofSpongeState_rate (state : SpongeState) (lane : Fin 25)
    (h : lane.val < 17) :
    (ofSpongeState state).get lane =
      laneOfBits fun z => state.1 ⟨64 * lane.val + z.val, by omega⟩ := by
  change (ofSpongeState state)[lane.val] = _
  simp [ofSpongeState, h]

/-- A lane in the capacity region reads the corresponding 64 capacity coordinates. -/
theorem get_ofSpongeState_capacity (state : SpongeState) (lane : Fin 25)
    (h : ¬lane.val < 17) :
    (ofSpongeState state).get lane =
      laneOfBits fun z => state.2 ⟨64 * (lane.val - 17) + z.val, by omega⟩ := by
  change (ofSpongeState state)[lane.val] = _
  simp [ofSpongeState, h]

/-- Convert the FIPS 202 lane array into SHAKE256's 1088-bit rate and 512-bit capacity split. -/
@[expose] def toSpongeState (A : State) : SpongeState :=
  (fun i =>
      (A.get ⟨i.val / 64, by omega⟩).getLsbD (i.val % 64),
    fun i =>
      (A.get ⟨17 + i.val / 64, by omega⟩).getLsbD (i.val % 64))

/-- Converting a rate/capacity split to lanes and back preserves every state bit. -/
theorem toSpongeState_ofSpongeState (state : SpongeState) :
    toSpongeState (ofSpongeState state) = state := by
  apply Prod.ext <;> funext i
  · have hlane : i.val / 64 < 17 := by omega
    change ((ofSpongeState state).get ⟨i.val / 64, by omega⟩).getLsbD (i.val % 64) = state.1 i
    rw [get_ofSpongeState_rate _ _ hlane,
      getLsbD_laneOfBits _ _ (Nat.mod_lt _ (by decide))]
    have hindex : 64 * (i.val / 64) + i.val % 64 = i.val := by
      simpa [Nat.mul_comm] using Nat.div_add_mod i.val 64
    apply congrArg state.1
    exact Fin.ext hindex
  · have hlane : ¬17 + i.val / 64 < 17 := by omega
    change ((ofSpongeState state).get ⟨17 + i.val / 64, by omega⟩).getLsbD (i.val % 64) = state.2 i
    rw [get_ofSpongeState_capacity _ _ hlane,
      getLsbD_laneOfBits _ _ (Nat.mod_lt _ (by decide))]
    have hindex : 64 * (i.val / 64) + i.val % 64 = i.val := by
      simpa [Nat.mul_comm] using Nat.div_add_mod i.val 64
    apply congrArg state.2
    apply Fin.ext
    simpa only [Nat.add_sub_cancel_left] using hindex

/-- Converting a lane state to the rate/capacity split and back preserves every lane. -/
theorem ofSpongeState_toSpongeState (A : State) :
    ofSpongeState (toSpongeState A) = A := by
  refine Vector.ext fun lane hlane => ?_
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  by_cases hrate : lane < 17
  · have hdiv : (64 * lane + z) / 64 = lane := by omega
    have hmod : (64 * lane + z) % 64 = z := by omega
    change ((ofSpongeState (toSpongeState A)).get ⟨lane, hlane⟩).getLsbD z =
      (A.get ⟨lane, hlane⟩).getLsbD z
    rw [get_ofSpongeState_rate _ _ hrate, getLsbD_laneOfBits _ z hz]
    change (A.get ⟨(64 * lane + z) / 64, by omega⟩).getLsbD ((64 * lane + z) % 64) = _
    have hlaneEq : (⟨(64 * lane + z) / 64, by omega⟩ : Fin 25) = ⟨lane, hlane⟩ :=
      Fin.ext hdiv
    rw [hlaneEq, hmod]
  · have hdiv : (64 * (lane - 17) + z) / 64 = lane - 17 := by omega
    have hmod : (64 * (lane - 17) + z) % 64 = z := by omega
    change ((ofSpongeState (toSpongeState A)).get ⟨lane, hlane⟩).getLsbD z =
      (A.get ⟨lane, hlane⟩).getLsbD z
    rw [get_ofSpongeState_capacity _ _ hrate, getLsbD_laneOfBits _ z hz]
    change (A.get ⟨17 + (64 * (lane - 17) + z) / 64, by omega⟩).getLsbD
      ((64 * (lane - 17) + z) % 64) = _
    have hlaneEq : (⟨17 + (64 * (lane - 17) + z) / 64, by omega⟩ : Fin 25) =
        ⟨lane, hlane⟩ := by
      apply Fin.ext
      change 17 + (64 * (lane - 17) + z) / 64 = lane
      rw [hdiv]
      omega
    rw [hlaneEq, hmod]

/-- FIPS 202 `KECCAK-p[1600, 24]` on SHAKE256's rate/capacity state split. -/
@[expose] def keccakP1600Rounds24Sponge (state : SpongeState) : SpongeState :=
  toSpongeState (keccakP1600Rounds24 (ofSpongeState state))

/-- Expand a byte into FIPS 202 bit-string order, least significant bit first. -/
@[expose] def byteBitsLE (byte : Fin 256) : List Bool :=
  BitString.lowBits 8 byte.val

/-- Expand a byte string into FIPS 202 bit-string order. -/
@[expose] def bytesToBitsLE (bytes : List (Fin 256)) : List Bool :=
  bytes.flatMap byteBitsLE

/-- FIPS 202 Algorithm 9, `pad10*1(x, m)`. -/
@[expose] def pad10star1 (x m : ℕ) : List Bool :=
  true :: List.replicate ((x - (m + 2) % x) % x) false ++ [true]

/-- Pack the first eight least-significant-bit-first coordinates into a byte. -/
@[expose] def bitsToByteLE (bits : List Bool) : Fin 256 :=
  ⟨BitString.lsbValue (bits.take 8), by
    exact Nat.lt_of_lt_of_le (BitString.lsbValue_lt (bits.take 8))
      (Nat.pow_le_pow_right (by decide) (List.length_take_le 8 bits))⟩

/-- Expanding one byte least-significant-bit first and reading it back recovers the byte. -/
@[simp] theorem bitsToByteLE_byteBitsLE (byte : Fin 256) :
    bitsToByteLE (byteBitsLE byte) = byte := by
  apply Fin.ext
  change BitString.lsbValue ((BitString.lowBits 8 byte.val).take 8) = byte.val
  rw [List.take_of_length_le (by simp)]
  exact BitString.lsbValue_lowBits (by simp)

/-- Reading an eight-bit word as a byte and expanding it recovers the word. -/
@[simp] theorem byteBitsLE_bitsToByteLE (bits : List Bool) (h : bits.length = 8) :
    byteBitsLE (bitsToByteLE bits) = bits := by
  change BitString.lowBits 8 (BitString.lsbValue (bits.take 8)) = bits
  rw [List.take_of_length_le (by omega)]
  simpa [h] using BitString.lowBits_lsbValue bits

/-- Read the 1088-bit SHAKE256 rate as 136 consecutive little-endian bytes. -/
@[expose] def rateBytes (rate : BitString 1088) : List (Fin 256) :=
  List.ofFn fun byte : Fin 136 =>
    bitsToByteLE (List.ofFn fun bit : Fin 8 => rate ⟨8 * byte.val + bit.val, by omega⟩)

/-- One SHAKE256 rate block contains exactly 136 output bytes. -/
@[simp] theorem length_rateBytes (rate : BitString 1088) : (rateBytes rate).length = 136 := by
  simp only [rateBytes, List.length_ofFn]

/-- Absorb already-padded rate blocks, squeeze `count` states, and expose their rate parts as a
byte stream. -/
@[expose] def squeezeBytes (blocks : List (BitString 1088)) (count : ℕ) : List (Fin 256) :=
  (Sponge.hashBlocks keccakP1600Rounds24Sponge Prod.fst count blocks).flatMap rateBytes

/-- `count` SHAKE256 squeezing blocks contain exactly `136 * count` bytes. -/
@[simp] theorem length_squeezeBytes (blocks : List (BitString 1088)) (count : ℕ) :
    (squeezeBytes blocks count).length = 136 * count := by
  have hflat : ∀ states : List (BitString 1088),
      (states.flatMap rateBytes).length = 136 * states.length := by
    intro states
    induction states with
    | nil => rfl
    | cons state states ih =>
      rw [List.flatMap_cons, List.length_append, length_rateBytes, ih, List.length_cons]
      omega
  have hcount :
      (Sponge.hashBlocks keccakP1600Rounds24Sponge Prod.fst count blocks).length = count :=
    Sponge.length_squeeze _ _ _ _
  rw [squeezeBytes, hflat, hcount]

private theorem take_flatMap_rateBytes (states : List (BitString 1088)) (count : ℕ) :
    (states.flatMap rateBytes).take (136 * count) = (states.take count).flatMap rateBytes := by
  induction states generalizing count with
  | nil => simp
  | cons state states ih =>
    cases count with
    | zero => rfl
    | succ count =>
      simp only [List.flatMap_cons, List.take_succ_cons]
      rw [Nat.mul_succ,
        show 136 * count + 136 = (rateBytes state).length + 136 * count by simp [Nat.add_comm],
        List.take_length_add_append, ih]

/-- Requesting more SHAKE256 squeezing blocks preserves every byte of the earlier blocks. -/
theorem take_squeezeBytes (blocks : List (BitString 1088)) {m n : ℕ} (h : m ≤ n) :
    (squeezeBytes blocks n).take (136 * m) = squeezeBytes blocks m := by
  rw [squeezeBytes, take_flatMap_rateBytes, Sponge.take_hashBlocks _ _ h, squeezeBytes]

/-- Byte-aligned SHAKE256 from FIPS 202 Section 6.2.

The second argument is the requested output length in bytes. The output length affects only how
much of the XOF stream is returned, not the preceding bytes. -/
@[expose] def shake256 (input : List (Fin 256)) (outputBytes : ℕ) : List (Fin 256) :=
  let suffixed := bytesToBitsLE input ++ [true, true, true, true]
  let padded := suffixed ++ pad10star1 1088 suffixed.length
  let blocks := Sponge.toBlocks 1088 padded
  let outputBlockCount := outputBytes ⌈/⌉ 136
  (squeezeBytes blocks outputBlockCount).take outputBytes

/-- SHAKE256 returns exactly the requested number of bytes. -/
@[simp] theorem length_shake256 (input : List (Fin 256)) (outputBytes : ℕ) :
    (shake256 input outputBytes).length = outputBytes := by
  rw [shake256, List.length_take, length_squeezeBytes, Nat.min_eq_left]
  exact le_smul_ceilDiv (a := 136) (b := outputBytes) (by decide)

/-- SHAKE256 is prefix-consistent: requesting more output never changes preceding bytes. -/
theorem take_shake256 (input : List (Fin 256)) {m n : ℕ} (h : m ≤ n) :
    (shake256 input n).take m = shake256 input m := by
  rw [shake256, List.take_take, Nat.min_eq_left h, shake256]
  have hk : m ⌈/⌉ 136 ≤ n ⌈/⌉ 136 := by
    rw [Nat.ceilDiv_eq_add_pred_div, Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_le_div_right (by omega)
  have hm : m ≤ 136 * (m ⌈/⌉ 136) :=
    le_smul_ceilDiv (a := 136) (b := m) (by decide)
  calc
    (squeezeBytes _ (n ⌈/⌉ 136)).take m =
        ((squeezeBytes _ (n ⌈/⌉ 136)).take (136 * (m ⌈/⌉ 136))).take m := by
      rw [List.take_take, Nat.min_eq_left hm]
    _ = (squeezeBytes _ (m ⌈/⌉ 136)).take m := by
      rw [take_squeezeBytes _ hk]

/-- Requesting no bytes returns the empty output. -/
@[simp] theorem shake256_zero_output (input : List (Fin 256)) : shake256 input 0 = [] := rfl

end Cslib.Crypto.Keccak
