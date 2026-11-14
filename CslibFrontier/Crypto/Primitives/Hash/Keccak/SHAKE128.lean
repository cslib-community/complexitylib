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

/-- The 1344-bit rate and 256-bit capacity views used by SHAKE128. -/
abbrev Shake128SpongeState := BitString 1344 × BitString 256

private theorem getLsbD_laneOfBits_shake128 (bits : BitString 64) (i : ℕ) (hi : i < 64) :
    (laneOfBits bits).getLsbD i = bits ⟨i, hi⟩ := by
  rw [laneOfBits, BitVec.getLsbD_ofFin]
  exact BitString.testBit_equivFin bits ⟨i, hi⟩

/-- Convert the SHAKE128 rate/capacity split into the FIPS 202 lane array. -/
@[expose] def ofShake128SpongeState (state : Shake128SpongeState) : State :=
  Vector.ofFn fun lane =>
    if hlane : lane.val < 21 then
      laneOfBits fun z => state.1 ⟨64 * lane.val + z.val, by omega⟩
    else
      laneOfBits fun z => state.2 ⟨64 * (lane.val - 21) + z.val, by omega⟩

/-- A SHAKE128 rate lane reads the corresponding 64 rate coordinates. -/
theorem get_ofShake128SpongeState_rate (state : Shake128SpongeState) (lane : Fin 25)
    (h : lane.val < 21) :
    (ofShake128SpongeState state).get lane =
      laneOfBits fun z => state.1 ⟨64 * lane.val + z.val, by omega⟩ := by
  change (ofShake128SpongeState state)[lane.val] = _
  simp [ofShake128SpongeState, h]

/-- A SHAKE128 capacity lane reads the corresponding 64 capacity coordinates. -/
theorem get_ofShake128SpongeState_capacity (state : Shake128SpongeState) (lane : Fin 25)
    (h : ¬lane.val < 21) :
    (ofShake128SpongeState state).get lane =
      laneOfBits fun z => state.2 ⟨64 * (lane.val - 21) + z.val, by omega⟩ := by
  change (ofShake128SpongeState state)[lane.val] = _
  simp [ofShake128SpongeState, h]

/-- Convert the FIPS 202 lane array into SHAKE128's rate and capacity split. -/
@[expose] def toShake128SpongeState (A : State) : Shake128SpongeState :=
  (fun i =>
      (A.get ⟨i.val / 64, by omega⟩).getLsbD (i.val % 64),
    fun i =>
      (A.get ⟨21 + i.val / 64, by omega⟩).getLsbD (i.val % 64))

/-- Converting a SHAKE128 rate/capacity split to lanes and back preserves every state bit. -/
theorem toShake128SpongeState_ofShake128SpongeState (state : Shake128SpongeState) :
    toShake128SpongeState (ofShake128SpongeState state) = state := by
  apply Prod.ext <;> funext i
  · have hlane : i.val / 64 < 21 := by omega
    change ((ofShake128SpongeState state).get ⟨i.val / 64, by omega⟩).getLsbD
      (i.val % 64) = state.1 i
    rw [get_ofShake128SpongeState_rate _ _ hlane,
      getLsbD_laneOfBits_shake128 _ _ (Nat.mod_lt _ (by decide))]
    apply congrArg state.1
    apply Fin.ext
    simpa only [Nat.mul_comm] using Nat.div_add_mod i.val 64
  · have hlane : ¬21 + i.val / 64 < 21 := by omega
    change ((ofShake128SpongeState state).get ⟨21 + i.val / 64, by omega⟩).getLsbD
      (i.val % 64) = state.2 i
    rw [get_ofShake128SpongeState_capacity _ _ hlane,
      getLsbD_laneOfBits_shake128 _ _ (Nat.mod_lt _ (by decide))]
    apply congrArg state.2
    apply Fin.ext
    simpa only [Nat.add_sub_cancel_left, Nat.mul_comm] using Nat.div_add_mod i.val 64

/-- Converting a lane state to the SHAKE128 split and back preserves every lane. -/
theorem ofShake128SpongeState_toShake128SpongeState (A : State) :
    ofShake128SpongeState (toShake128SpongeState A) = A := by
  refine Vector.ext fun lane hlane => ?_
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  by_cases hrate : lane < 21
  · have hdiv : (64 * lane + z) / 64 = lane := by omega
    have hmod : (64 * lane + z) % 64 = z := by omega
    change ((ofShake128SpongeState (toShake128SpongeState A)).get
      ⟨lane, hlane⟩).getLsbD z = (A.get ⟨lane, hlane⟩).getLsbD z
    rw [get_ofShake128SpongeState_rate _ _ hrate,
      getLsbD_laneOfBits_shake128 _ z hz]
    change (A.get ⟨(64 * lane + z) / 64, by omega⟩).getLsbD
      ((64 * lane + z) % 64) = _
    have hlaneEq : (⟨(64 * lane + z) / 64, by omega⟩ : Fin 25) = ⟨lane, hlane⟩ :=
      Fin.ext hdiv
    rw [hlaneEq, hmod]
  · have hdiv : (64 * (lane - 21) + z) / 64 = lane - 21 := by omega
    have hmod : (64 * (lane - 21) + z) % 64 = z := by omega
    change ((ofShake128SpongeState (toShake128SpongeState A)).get
      ⟨lane, hlane⟩).getLsbD z = (A.get ⟨lane, hlane⟩).getLsbD z
    rw [get_ofShake128SpongeState_capacity _ _ hrate,
      getLsbD_laneOfBits_shake128 _ z hz]
    change (A.get ⟨21 + (64 * (lane - 21) + z) / 64, by omega⟩).getLsbD
      ((64 * (lane - 21) + z) % 64) = _
    have hlaneEq : (⟨21 + (64 * (lane - 21) + z) / 64, by omega⟩ : Fin 25) =
        ⟨lane, hlane⟩ := by
      apply Fin.ext
      change 21 + (64 * (lane - 21) + z) / 64 = lane
      rw [hdiv]
      omega
    rw [hlaneEq, hmod]

/-- FIPS 202 `KECCAK-p[1600, 24]` on SHAKE128's rate/capacity split. -/
@[expose] def keccakP1600Rounds24Shake128 (state : Shake128SpongeState) :
    Shake128SpongeState :=
  toShake128SpongeState (keccakP1600Rounds24 (ofShake128SpongeState state))

/-- Read the 1344-bit SHAKE128 rate as 168 consecutive little-endian bytes. -/
@[expose] def shake128RateBytes (rate : BitString 1344) : List (Fin 256) :=
  List.ofFn fun byte : Fin 168 =>
    bitsToByteLE (List.ofFn fun bit : Fin 8 => rate ⟨8 * byte.val + bit.val, by omega⟩)

/-- One SHAKE128 rate block contains exactly 168 output bytes. -/
@[simp] theorem length_shake128RateBytes (rate : BitString 1344) :
    (shake128RateBytes rate).length = 168 := by
  simp only [shake128RateBytes, List.length_ofFn]

/-- Absorb padded SHAKE128 blocks and expose `count` squeezed rate states as bytes. -/
@[expose] def shake128SqueezeBytes (blocks : List (BitString 1344)) (count : ℕ) :
    List (Fin 256) :=
  (Sponge.hashBlocks keccakP1600Rounds24Shake128 Prod.fst count blocks).flatMap
    shake128RateBytes

/-- `count` SHAKE128 squeezing blocks contain exactly `168 * count` bytes. -/
@[simp] theorem length_shake128SqueezeBytes (blocks : List (BitString 1344)) (count : ℕ) :
    (shake128SqueezeBytes blocks count).length = 168 * count := by
  have hflat : ∀ states : List (BitString 1344),
      (states.flatMap shake128RateBytes).length = 168 * states.length := by
    intro states
    induction states with
    | nil => simp
    | cons state states ih =>
      rw [List.flatMap_cons, List.length_append, length_shake128RateBytes, ih,
        List.length_cons]
      omega
  have hcount :
      (Sponge.hashBlocks keccakP1600Rounds24Shake128 Prod.fst count blocks).length = count :=
    Sponge.length_squeeze _ _ _ _
  rw [shake128SqueezeBytes, hflat, hcount]

private theorem take_flatMap_shake128RateBytes (states : List (BitString 1344)) (count : ℕ) :
    (states.flatMap shake128RateBytes).take (168 * count) =
      (states.take count).flatMap shake128RateBytes := by
  induction states generalizing count with
  | nil => simp
  | cons state states ih =>
    cases count with
    | zero => rfl
    | succ count =>
      simp only [List.flatMap_cons, List.take_succ_cons]
      rw [Nat.mul_succ,
        show 168 * count + 168 = (shake128RateBytes state).length + 168 * count by
          simp [Nat.add_comm],
        List.take_length_add_append, ih]

/-- Requesting more SHAKE128 squeezing blocks preserves every byte of the earlier blocks. -/
theorem take_shake128SqueezeBytes (blocks : List (BitString 1344)) {m n : ℕ} (h : m ≤ n) :
    (shake128SqueezeBytes blocks n).take (168 * m) = shake128SqueezeBytes blocks m := by
  rw [shake128SqueezeBytes, take_flatMap_shake128RateBytes,
    Sponge.take_hashBlocks _ _ h, shake128SqueezeBytes]

/-- Byte-aligned SHAKE128 from FIPS 202 Section 6.2.

The second argument is measured in output bytes. It changes only how much of the XOF stream is
returned, not the preceding bytes. -/
@[expose] def shake128 (input : List (Fin 256)) (outputBytes : ℕ) : List (Fin 256) :=
  let suffixed := bytesToBitsLE input ++ [true, true, true, true]
  let padded := suffixed ++ pad10star1 1344 suffixed.length
  let blocks := Sponge.toBlocks 1344 padded
  let outputBlockCount := outputBytes ⌈/⌉ 168
  (shake128SqueezeBytes blocks outputBlockCount).take outputBytes

/-- SHAKE128 returns exactly the requested number of bytes. -/
@[simp] theorem length_shake128 (input : List (Fin 256)) (outputBytes : ℕ) :
    (shake128 input outputBytes).length = outputBytes := by
  rw [shake128, List.length_take, length_shake128SqueezeBytes, Nat.min_eq_left]
  exact le_smul_ceilDiv (a := 168) (b := outputBytes) (by decide)

/-- SHAKE128 is prefix-consistent: requesting more output never changes preceding bytes. -/
theorem take_shake128 (input : List (Fin 256)) {m n : ℕ} (h : m ≤ n) :
    (shake128 input n).take m = shake128 input m := by
  rw [shake128, List.take_take, Nat.min_eq_left h, shake128]
  have hk : m ⌈/⌉ 168 ≤ n ⌈/⌉ 168 := by
    rw [Nat.ceilDiv_eq_add_pred_div, Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_le_div_right (by omega)
  have hm : m ≤ 168 * (m ⌈/⌉ 168) :=
    le_smul_ceilDiv (a := 168) (b := m) (by decide)
  calc
    (shake128SqueezeBytes _ (n ⌈/⌉ 168)).take m =
        ((shake128SqueezeBytes _ (n ⌈/⌉ 168)).take (168 * (m ⌈/⌉ 168))).take m := by
      rw [List.take_take, Nat.min_eq_left hm]
    _ = (shake128SqueezeBytes _ (m ⌈/⌉ 168)).take m := by
      rw [take_shake128SqueezeBytes _ hk]

/-- Requesting no SHAKE128 bytes returns the empty output. -/
@[simp] theorem shake128_zero_output (input : List (Fin 256)) : shake128 input 0 = [] := rfl

end Cslib.Crypto.Keccak
