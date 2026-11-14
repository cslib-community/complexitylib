/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Hash.Keccak

/-!
# SHAKE128

This module supplies byte-aligned SHAKE128 on the checked Keccak-p[1600, 24] permutation from
`Cslib.Crypto.Keccak`. FIPS 202 Section 6.2 gives SHAKE128 a 1344-bit rate and 256-bit capacity.
Bytes use the same least-significant-bit-first convention as `shake256`; the only sponge-level
difference is the rate/capacity split.

This is an executable specification. It is not a constant-time implementation, an efficiency or
security certificate, or a claim of FIPS validation.

## Main definitions

* `Cslib.Crypto.Keccak.Shake128SpongeState`: SHAKE128's rate/capacity state split.
* `Cslib.Crypto.Keccak.keccakP1600Rounds24Shake128`: the shared permutation on that split.
* `Cslib.Crypto.Keccak.shake128`: byte-aligned SHAKE128 with an output length in bytes.

## Main results

* `Cslib.Crypto.Keccak.toShake128SpongeState_ofShake128SpongeState`: converting the two state
  views is exact.
* `Cslib.Crypto.Keccak.length_shake128`: SHAKE128 returns the requested byte count.
* `Cslib.Crypto.Keccak.take_shake128`: longer requests preserve the preceding XOF bytes.

## References

* [National Institute of Standards and Technology, *SHA-3 Standard: Permutation-Based Hash and
  Extendable-Output Functions*, FIPS PUB 202, Section 6.2][NISTFIPS202].
-/

public section

namespace Cslib.Crypto.Keccak

open Cslib

/-- The SHAKE128 layout: 21 rate lanes and four capacity lanes. -/
@[expose] def shake128Layout : SpongeLayout := ⟨21, 4, by decide, by decide⟩

/-- The 1344-bit rate and 256-bit capacity views used by SHAKE128. -/
abbrev Shake128SpongeState := SpongeView shake128Layout

/-- Convert the SHAKE128 rate/capacity split into the FIPS 202 lane array. -/
@[expose] def ofShake128SpongeState (state : Shake128SpongeState) : State :=
  ofSpongeView shake128Layout state

/-- A SHAKE128 rate lane reads the corresponding 64 rate coordinates. -/
theorem get_ofShake128SpongeState_rate (state : Shake128SpongeState) (lane : Fin 25)
    (h : lane.val < 21) :
    (ofShake128SpongeState state).get lane =
      laneOfBits fun z => state.1 ⟨64 * lane.val + z.val, by omega⟩ := by
  simpa [ofShake128SpongeState, shake128Layout] using
    get_ofSpongeView_rate shake128Layout state lane h

/-- A SHAKE128 capacity lane reads the corresponding 64 capacity coordinates. -/
theorem get_ofShake128SpongeState_capacity (state : Shake128SpongeState) (lane : Fin 25)
    (h : ¬lane.val < 21) :
    (ofShake128SpongeState state).get lane =
      laneOfBits fun z => state.2 ⟨64 * (lane.val - 21) + z.val, by omega⟩ := by
  simpa [ofShake128SpongeState, shake128Layout] using
    get_ofSpongeView_capacity shake128Layout state lane h

/-- Convert the FIPS 202 lane array into SHAKE128's rate and capacity split. -/
@[expose] def toShake128SpongeState (A : State) : Shake128SpongeState :=
  toSpongeView shake128Layout A

/-- Converting a SHAKE128 rate/capacity split to lanes and back preserves every state bit. -/
theorem toShake128SpongeState_ofShake128SpongeState (state : Shake128SpongeState) :
    toShake128SpongeState (ofShake128SpongeState state) = state := by
  simpa [toShake128SpongeState, ofShake128SpongeState] using
    toSpongeView_ofSpongeView shake128Layout state

/-- Converting a lane state to the SHAKE128 split and back preserves every lane. -/
theorem ofShake128SpongeState_toShake128SpongeState (A : State) :
    ofShake128SpongeState (toShake128SpongeState A) = A := by
  simpa [toShake128SpongeState, ofShake128SpongeState] using
    ofSpongeView_toSpongeView shake128Layout A

/-- FIPS 202 `KECCAK-p[1600, 24]` on SHAKE128's rate/capacity split. -/
@[expose] def keccakP1600Rounds24Shake128 (state : Shake128SpongeState) :
    Shake128SpongeState :=
  keccakP1600Rounds24View shake128Layout state

/-- Read the 1344-bit SHAKE128 rate as 168 consecutive little-endian bytes. -/
@[expose] def shake128RateBytes (rate : BitString 1344) : List (Fin 256) :=
  rateBytesFor shake128Layout rate

/-- One SHAKE128 rate block contains exactly 168 output bytes. -/
@[simp] theorem length_shake128RateBytes (rate : BitString 1344) :
    (shake128RateBytes rate).length = 168 := by
  simpa [shake128RateBytes, shake128Layout] using length_rateBytesFor shake128Layout rate

/-- Absorb padded SHAKE128 blocks and expose `count` squeezed rate states as bytes. -/
@[expose] def shake128SqueezeBytes (blocks : List (BitString 1344)) (count : ℕ) :
    List (Fin 256) :=
  squeezeBytesFor shake128Layout blocks count

/-- `count` SHAKE128 squeezing blocks contain exactly `168 * count` bytes. -/
@[simp] theorem length_shake128SqueezeBytes (blocks : List (BitString 1344)) (count : ℕ) :
    (shake128SqueezeBytes blocks count).length = 168 * count := by
  simpa [shake128SqueezeBytes, shake128Layout] using
    length_squeezeBytesFor shake128Layout blocks count

/-- Requesting more SHAKE128 squeezing blocks preserves every byte of the earlier blocks. -/
theorem take_shake128SqueezeBytes (blocks : List (BitString 1344)) {m n : ℕ} (h : m ≤ n) :
    (shake128SqueezeBytes blocks n).take (168 * m) = shake128SqueezeBytes blocks m := by
  simpa [shake128SqueezeBytes, shake128Layout] using
    take_squeezeBytesFor shake128Layout blocks h

/-- Byte-aligned SHAKE128 from FIPS 202 Section 6.2.

The second argument is measured in output bytes. It changes only how much of the XOF stream is
returned, not the preceding bytes. -/
@[expose] def shake128 (input : List (Fin 256)) (outputBytes : ℕ) : List (Fin 256) :=
  byteXof shake128Layout input outputBytes

/-- SHAKE128 returns exactly the requested number of bytes. -/
@[simp] theorem length_shake128 (input : List (Fin 256)) (outputBytes : ℕ) :
    (shake128 input outputBytes).length = outputBytes := by
  simpa [shake128] using length_byteXof shake128Layout input outputBytes

/-- SHAKE128 is prefix-consistent: requesting more output never changes preceding bytes. -/
theorem take_shake128 (input : List (Fin 256)) {m n : ℕ} (h : m ≤ n) :
    (shake128 input n).take m = shake128 input m := by
  simpa [shake128] using take_byteXof shake128Layout input h

/-- Requesting no SHAKE128 bytes returns the empty output. -/
@[simp] theorem shake128_zero_output (input : List (Fin 256)) : shake128 input 0 = [] := rfl

end Cslib.Crypto.Keccak
