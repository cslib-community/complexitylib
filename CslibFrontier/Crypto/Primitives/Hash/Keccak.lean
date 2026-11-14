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
# Keccak-p[1600, 24] and byte-aligned SHAKE

This module implements the concrete permutation and byte-aligned extendable-output function from
[NIST FIPS 202][NISTFIPS202]. The state is a `5 × 5` array of 64-bit lanes. Lane bit `z` is the
standard's `A[x, y, z]`, and a flat state bit at position `64 * (5 * y + x) + z` maps to that
coordinate (Sections 3.1.2--3.1.3). The five round steps follow Algorithms 1--7 and Tables 1--2
in Sections 3.2--3.3; `keccakP1600Rounds24` is Algorithm 8's underlying function as specified in
Section 4.

`byteXof` implements Algorithms 8--9 and Section 6.2 for byte-aligned messages at any lane-aligned
Keccak-p[1600] rate/capacity split. Bytes are expanded least significant bit first, matching NIST's
official SHAKE example state dumps; the SHAKE suffix `1111` and `pad10*1` are appended; rate blocks
are processed by the existing `Cslib.Crypto.Sponge.hashBlocks`; and output bytes are assembled in
the same convention. `shake256` is the 1088-bit-rate specialization; SHAKE128 specializes the same
machinery in `CslibFrontier.Crypto.Primitives.Hash.Keccak.SHAKE128`.

This is a checked executable specification, not a constant-time or efficient implementation, a
cryptographic security proof, or a claim of validation under FIPS 202. It maps to the published
August 2015 standard and does not claim agreement with a future revision or with FN-DSA / FIPS 206.

## Main definitions

* `Cslib.Crypto.Keccak.State`: a `5 × 5` array of 64-bit lanes.
* `Cslib.Crypto.Keccak.SpongeLayout`, `SpongeView`: a lane-aligned rate/capacity split.
* `Cslib.Crypto.Keccak.theta`, `rho`, `pi`, `chi`, `iota`: the five FIPS 202 round steps.
* `Cslib.Crypto.Keccak.keccakP1600Rounds24`: the 24-round state transformation.
* `Cslib.Crypto.Keccak.keccakP1600Rounds24View`: the transformation on a selected sponge split.
* `Cslib.Crypto.Keccak.byteBitsLE`, `bytesToBitsLE`, `bitsToByteLE`: the explicit FIPS 202
  least-significant-bit-first byte boundary.
* `Cslib.Crypto.Keccak.rateBytesFor`, `squeezeBytesFor`, `byteXof`: shared byte-aligned XOF
  machinery parameterized by the sponge layout.
* `Cslib.Crypto.Keccak.shake256`: byte-aligned SHAKE256 with an output length in bytes.

## Main results

* `Cslib.Crypto.Keccak.bitsToByteLE_byteBitsLE`, `byteBitsLE_bitsToByteLE`: the byte boundary
  round trips.
* `Cslib.Crypto.Keccak.toSpongeView_ofSpongeView`, `ofSpongeView_toSpongeView`: the selected state
  views are inverse.
* `Cslib.Crypto.Keccak.length_byteXof`, `take_byteXof`: the shared byte XOF has the requested
  length and preserves prefixes.
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

/-- A lane-aligned rate/capacity split of the 25-lane Keccak-p[1600] state. -/
structure SpongeLayout where
  /-- The number of 64-bit lanes exposed by the rate. -/
  rateLanes : ℕ
  /-- The number of 64-bit lanes retained as capacity. -/
  capacityLanes : ℕ
  /-- A byte XOF has a nonempty rate. -/
  rate_pos : 0 < rateLanes
  /-- Rate and capacity together fill the Keccak-p[1600] state. -/
  lane_count : rateLanes + capacityLanes = 25
  deriving DecidableEq

/-- The rate and capacity bit-string views selected by a lane-aligned sponge layout. -/
abbrev SpongeView (layout : SpongeLayout) :=
  BitString (64 * layout.rateLanes) × BitString (64 * layout.capacityLanes)

/-- The SHAKE256 layout: 17 rate lanes and eight capacity lanes. -/
@[expose] def shake256Layout : SpongeLayout := ⟨17, 8, by decide, by decide⟩

/-- The sponge rate and capacity views used by SHAKE256. -/
abbrev SpongeState := SpongeView shake256Layout

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

/-! ### Shared lane-aligned sponge adapter -/

/-- Convert a lane-aligned rate/capacity split into the FIPS 202 lane array. -/
@[expose] def ofSpongeView (layout : SpongeLayout) (state : SpongeView layout) : State :=
  Vector.ofFn fun lane =>
    if hlane : lane.val < layout.rateLanes then
      laneOfBits fun z => state.1 ⟨64 * lane.val + z.val, by omega⟩
    else
      laneOfBits fun z => state.2 ⟨64 * (lane.val - layout.rateLanes) + z.val, by
        have hlaneVal := lane.isLt
        have hlayout := layout.lane_count
        omega⟩

/-- A rate lane reads the corresponding 64 rate coordinates. -/
theorem get_ofSpongeView_rate (layout : SpongeLayout) (state : SpongeView layout)
    (lane : Fin 25) (h : lane.val < layout.rateLanes) :
    (ofSpongeView layout state).get lane =
      laneOfBits fun z => state.1 ⟨64 * lane.val + z.val, by omega⟩ := by
  change (ofSpongeView layout state)[lane.val] = _
  simp [ofSpongeView, h]

/-- A capacity lane reads the corresponding 64 capacity coordinates. -/
theorem get_ofSpongeView_capacity (layout : SpongeLayout) (state : SpongeView layout)
    (lane : Fin 25) (h : ¬lane.val < layout.rateLanes) :
    (ofSpongeView layout state).get lane =
      laneOfBits fun z => state.2 ⟨64 * (lane.val - layout.rateLanes) + z.val, by
        have hlaneVal := lane.isLt
        have hlayout := layout.lane_count
        omega⟩ := by
  change (ofSpongeView layout state)[lane.val] = _
  simp [ofSpongeView, h]

/-- Convert the FIPS 202 lane array into a selected rate/capacity split. -/
@[expose] def toSpongeView (layout : SpongeLayout) (A : State) : SpongeView layout :=
  (fun i =>
      (A.get ⟨i.val / 64, by
        have hi := i.isLt
        have hlayout := layout.lane_count
        omega⟩).getLsbD (i.val % 64),
    fun i =>
      (A.get ⟨layout.rateLanes + i.val / 64, by
        have hi := i.isLt
        have hlayout := layout.lane_count
        omega⟩).getLsbD (i.val % 64))

/-- Converting a selected sponge view to lanes and back preserves every state bit. -/
theorem toSpongeView_ofSpongeView (layout : SpongeLayout) (state : SpongeView layout) :
    toSpongeView layout (ofSpongeView layout state) = state := by
  apply Prod.ext <;> funext i
  · have hlane : i.val / 64 < layout.rateLanes := by
      have hi := i.isLt
      omega
    change ((ofSpongeView layout state).get ⟨i.val / 64, by
      have hlayout := layout.lane_count
      omega⟩).getLsbD (i.val % 64) = state.1 i
    rw [get_ofSpongeView_rate _ _ _ hlane,
      getLsbD_laneOfBits _ _ (Nat.mod_lt _ (by decide))]
    apply congrArg state.1
    apply Fin.ext
    simpa [Nat.mul_comm] using Nat.div_add_mod i.val 64
  · have hlane : ¬layout.rateLanes + i.val / 64 < layout.rateLanes := by omega
    change ((ofSpongeView layout state).get ⟨layout.rateLanes + i.val / 64, by
      have hi := i.isLt
      have hlayout := layout.lane_count
      omega⟩).getLsbD (i.val % 64) = state.2 i
    rw [get_ofSpongeView_capacity _ _ _ hlane,
      getLsbD_laneOfBits _ _ (Nat.mod_lt _ (by decide))]
    apply congrArg state.2
    apply Fin.ext
    simpa only [Nat.add_sub_cancel_left, Nat.mul_comm] using Nat.div_add_mod i.val 64

/-- Converting a lane state to a selected sponge view and back preserves every lane. -/
theorem ofSpongeView_toSpongeView (layout : SpongeLayout) (A : State) :
    ofSpongeView layout (toSpongeView layout A) = A := by
  refine Vector.ext fun lane hlane => ?_
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  by_cases hrate : lane < layout.rateLanes
  · have hdiv : (64 * lane + z) / 64 = lane := by omega
    have hmod : (64 * lane + z) % 64 = z := by omega
    change ((ofSpongeView layout (toSpongeView layout A)).get
      ⟨lane, hlane⟩).getLsbD z = (A.get ⟨lane, hlane⟩).getLsbD z
    rw [get_ofSpongeView_rate _ _ _ hrate, getLsbD_laneOfBits _ z hz]
    change (A.get ⟨(64 * lane + z) / 64, by
      have hlayout := layout.lane_count
      omega⟩).getLsbD ((64 * lane + z) % 64) = _
    have hlaneEq : (⟨(64 * lane + z) / 64, by
        have hlayout := layout.lane_count
        omega⟩ : Fin 25) = ⟨lane, hlane⟩ := Fin.ext hdiv
    rw [hlaneEq, hmod]
  · have hdiv : (64 * (lane - layout.rateLanes) + z) / 64 =
        lane - layout.rateLanes := by omega
    have hmod : (64 * (lane - layout.rateLanes) + z) % 64 = z := by omega
    change ((ofSpongeView layout (toSpongeView layout A)).get
      ⟨lane, hlane⟩).getLsbD z = (A.get ⟨lane, hlane⟩).getLsbD z
    rw [get_ofSpongeView_capacity _ _ _ hrate, getLsbD_laneOfBits _ z hz]
    change (A.get ⟨layout.rateLanes +
      (64 * (lane - layout.rateLanes) + z) / 64, by
        have hlayout := layout.lane_count
        omega⟩).getLsbD ((64 * (lane - layout.rateLanes) + z) % 64) = _
    have hlaneEq : (⟨layout.rateLanes +
        (64 * (lane - layout.rateLanes) + z) / 64, by
          have hlayout := layout.lane_count
          omega⟩ : Fin 25) = ⟨lane, hlane⟩ := by
      apply Fin.ext
      rw [hdiv]
      omega
    rw [hlaneEq, hmod]

/-- Keccak-p[1600, 24] on a lane-aligned sponge view. -/
@[expose] def keccakP1600Rounds24View (layout : SpongeLayout) (state : SpongeView layout) :
    SpongeView layout :=
  toSpongeView layout (keccakP1600Rounds24 (ofSpongeView layout state))

/-! ### Shared byte-aligned SHAKE machinery -/

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

/-- Expanding one byte least-significant bit first and reading it back recovers the byte. -/
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

/-- Read the rate selected by `layout` as consecutive little-endian bytes. -/
@[expose] def rateBytesFor (layout : SpongeLayout) (rate : BitString (64 * layout.rateLanes)) :
    List (Fin 256) :=
  List.ofFn fun byte : Fin (8 * layout.rateLanes) =>
    bitsToByteLE (List.ofFn fun bit : Fin 8 => rate ⟨8 * byte.val + bit.val, by omega⟩)

/-- A lane-aligned rate exposes eight bytes per lane. -/
@[simp] theorem length_rateBytesFor (layout : SpongeLayout)
    (rate : BitString (64 * layout.rateLanes)) :
    (rateBytesFor layout rate).length = 8 * layout.rateLanes := by
  simp only [rateBytesFor, List.length_ofFn]

/-- Absorb padded blocks and expose `count` squeezed rate states as bytes. -/
@[expose] def squeezeBytesFor (layout : SpongeLayout)
    (blocks : List (BitString (64 * layout.rateLanes))) (count : ℕ) : List (Fin 256) :=
  (Sponge.hashBlocks (keccakP1600Rounds24View layout) Prod.fst count blocks).flatMap
    (rateBytesFor layout)

/-- `count` squeezing blocks contain `8 * rateLanes * count` bytes. -/
@[simp] theorem length_squeezeBytesFor (layout : SpongeLayout)
    (blocks : List (BitString (64 * layout.rateLanes))) (count : ℕ) :
    (squeezeBytesFor layout blocks count).length = (8 * layout.rateLanes) * count := by
  have hflat : ∀ states : List (BitString (64 * layout.rateLanes)),
      (states.flatMap (rateBytesFor layout)).length =
        (8 * layout.rateLanes) * states.length := by
    intro states
    induction states with
    | nil => simp
    | cons state states ih =>
      rw [List.flatMap_cons, List.length_append, length_rateBytesFor, ih, List.length_cons]
      omega
  have hcount :
      (Sponge.hashBlocks (keccakP1600Rounds24View layout) Prod.fst count blocks).length = count :=
    Sponge.length_squeeze _ _ _ _
  rw [squeezeBytesFor, hflat, hcount]

private theorem take_flatMap_rateBytesFor (layout : SpongeLayout)
    (states : List (BitString (64 * layout.rateLanes))) (count : ℕ) :
    (states.flatMap (rateBytesFor layout)).take ((8 * layout.rateLanes) * count) =
      (states.take count).flatMap (rateBytesFor layout) := by
  induction states generalizing count with
  | nil => simp
  | cons state states ih =>
    cases count with
    | zero => rfl
    | succ count =>
      simp only [List.flatMap_cons, List.take_succ_cons]
      rw [Nat.mul_succ,
        show (8 * layout.rateLanes) * count + 8 * layout.rateLanes =
            (rateBytesFor layout state).length + (8 * layout.rateLanes) * count by
          simp [Nat.add_comm],
        List.take_length_add_append, ih]

/-- Requesting more squeezing blocks preserves every byte of the earlier blocks. -/
theorem take_squeezeBytesFor (layout : SpongeLayout)
    (blocks : List (BitString (64 * layout.rateLanes))) {m n : ℕ} (h : m ≤ n) :
    (squeezeBytesFor layout blocks n).take ((8 * layout.rateLanes) * m) =
      squeezeBytesFor layout blocks m := by
  rw [squeezeBytesFor, take_flatMap_rateBytesFor,
    Sponge.take_hashBlocks _ _ h, squeezeBytesFor]

/-- Byte-aligned SHAKE with the rate and capacity selected by `layout`.

The output length is measured in bytes. Every specialization uses the SHAKE suffix `1111` and
FIPS 202's `pad10*1`; `layout` changes only the rate/capacity split. -/
@[expose] def byteXof (layout : SpongeLayout) (input : List (Fin 256)) (outputBytes : ℕ) :
    List (Fin 256) :=
  let suffixed := bytesToBitsLE input ++ [true, true, true, true]
  let padded := suffixed ++ pad10star1 (64 * layout.rateLanes) suffixed.length
  let blocks := Sponge.toBlocks (64 * layout.rateLanes) padded
  let rateBytes := 8 * layout.rateLanes
  let outputBlockCount := outputBytes ⌈/⌉ rateBytes
  (squeezeBytesFor layout blocks outputBlockCount).take outputBytes

/-- A byte-aligned XOF returns exactly the requested byte count. -/
@[simp] theorem length_byteXof (layout : SpongeLayout) (input : List (Fin 256))
    (outputBytes : ℕ) : (byteXof layout input outputBytes).length = outputBytes := by
  rw [byteXof, List.length_take, length_squeezeBytesFor, Nat.min_eq_left]
  exact le_smul_ceilDiv (a := 8 * layout.rateLanes) (b := outputBytes) (by
    have hr := layout.rate_pos
    omega)

/-- Byte-aligned XOF output is prefix-consistent across requested lengths. -/
theorem take_byteXof (layout : SpongeLayout) (input : List (Fin 256)) {m n : ℕ} (h : m ≤ n) :
    (byteXof layout input n).take m = byteXof layout input m := by
  rw [byteXof, List.take_take, Nat.min_eq_left h, byteXof]
  have hk : m ⌈/⌉ (8 * layout.rateLanes) ≤ n ⌈/⌉ (8 * layout.rateLanes) := by
    rw [Nat.ceilDiv_eq_add_pred_div, Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_le_div_right (by
      have hr := layout.rate_pos
      omega)
  have hm : m ≤ (8 * layout.rateLanes) * (m ⌈/⌉ (8 * layout.rateLanes)) :=
    le_smul_ceilDiv (a := 8 * layout.rateLanes) (b := m) (by
      have hr := layout.rate_pos
      omega)
  calc
    (squeezeBytesFor layout _ (n ⌈/⌉ (8 * layout.rateLanes))).take m =
        ((squeezeBytesFor layout _ (n ⌈/⌉ (8 * layout.rateLanes))).take
          ((8 * layout.rateLanes) * (m ⌈/⌉ (8 * layout.rateLanes)))).take m := by
      rw [List.take_take, Nat.min_eq_left hm]
    _ = (squeezeBytesFor layout _ (m ⌈/⌉ (8 * layout.rateLanes))).take m := by
      rw [take_squeezeBytesFor _ _ hk]

/-! ### SHAKE256 specialization -/

/-- Convert the SHAKE256 rate/capacity split into the FIPS 202 lane array. -/
@[expose] def ofSpongeState (state : SpongeState) : State :=
  ofSpongeView shake256Layout state

/-- A SHAKE256 rate lane reads the corresponding 64 rate coordinates. -/
theorem get_ofSpongeState_rate (state : SpongeState) (lane : Fin 25) (h : lane.val < 17) :
    (ofSpongeState state).get lane =
      laneOfBits fun z => state.1 ⟨64 * lane.val + z.val, by omega⟩ := by
  simpa [ofSpongeState, shake256Layout] using
    get_ofSpongeView_rate shake256Layout state lane h

/-- A SHAKE256 capacity lane reads the corresponding 64 capacity coordinates. -/
theorem get_ofSpongeState_capacity (state : SpongeState) (lane : Fin 25) (h : ¬lane.val < 17) :
    (ofSpongeState state).get lane =
      laneOfBits fun z => state.2 ⟨64 * (lane.val - 17) + z.val, by omega⟩ := by
  simpa [ofSpongeState, shake256Layout] using
    get_ofSpongeView_capacity shake256Layout state lane h

/-- Convert the FIPS 202 lane array into SHAKE256's 1088-bit rate and 512-bit capacity split. -/
@[expose] def toSpongeState (A : State) : SpongeState :=
  toSpongeView shake256Layout A

/-- Converting a SHAKE256 sponge split to lanes and back preserves every state bit. -/
theorem toSpongeState_ofSpongeState (state : SpongeState) :
    toSpongeState (ofSpongeState state) = state := by
  simpa [toSpongeState, ofSpongeState] using toSpongeView_ofSpongeView shake256Layout state

/-- Converting a lane state to the SHAKE256 split and back preserves every lane. -/
theorem ofSpongeState_toSpongeState (A : State) :
    ofSpongeState (toSpongeState A) = A := by
  simpa [toSpongeState, ofSpongeState] using ofSpongeView_toSpongeView shake256Layout A

/-- FIPS 202 `KECCAK-p[1600, 24]` on SHAKE256's rate/capacity split. -/
@[expose] def keccakP1600Rounds24Sponge (state : SpongeState) : SpongeState :=
  keccakP1600Rounds24View shake256Layout state

/-- Read the 1088-bit SHAKE256 rate as 136 consecutive little-endian bytes. -/
@[expose] def rateBytes (rate : BitString 1088) : List (Fin 256) :=
  rateBytesFor shake256Layout rate

/-- One SHAKE256 rate block contains exactly 136 output bytes. -/
@[simp] theorem length_rateBytes (rate : BitString 1088) : (rateBytes rate).length = 136 := by
  simpa [rateBytes, shake256Layout] using length_rateBytesFor shake256Layout rate

/-- Squeeze SHAKE256 rate states as bytes. -/
@[expose] def squeezeBytes (blocks : List (BitString 1088)) (count : ℕ) : List (Fin 256) :=
  squeezeBytesFor shake256Layout blocks count

/-- `count` SHAKE256 squeezing blocks contain exactly `136 * count` bytes. -/
@[simp] theorem length_squeezeBytes (blocks : List (BitString 1088)) (count : ℕ) :
    (squeezeBytes blocks count).length = 136 * count := by
  simpa [squeezeBytes, shake256Layout] using
    length_squeezeBytesFor shake256Layout blocks count

/-- Requesting more SHAKE256 squeezing blocks preserves every byte of the earlier blocks. -/
theorem take_squeezeBytes (blocks : List (BitString 1088)) {m n : ℕ} (h : m ≤ n) :
    (squeezeBytes blocks n).take (136 * m) = squeezeBytes blocks m := by
  simpa [squeezeBytes, shake256Layout] using take_squeezeBytesFor shake256Layout blocks h

/-- Byte-aligned SHAKE256 from FIPS 202 Section 6.2. -/
@[expose] def shake256 (input : List (Fin 256)) (outputBytes : ℕ) : List (Fin 256) :=
  byteXof shake256Layout input outputBytes

/-- SHAKE256 returns exactly the requested number of bytes. -/
@[simp] theorem length_shake256 (input : List (Fin 256)) (outputBytes : ℕ) :
    (shake256 input outputBytes).length = outputBytes := by
  simpa [shake256] using length_byteXof shake256Layout input outputBytes

/-- SHAKE256 is prefix-consistent: requesting more output never changes preceding bytes. -/
theorem take_shake256 (input : List (Fin 256)) {m n : ℕ} (h : m ≤ n) :
    (shake256 input n).take m = shake256 input m := by
  simpa [shake256] using take_byteXof shake256Layout input h

/-- Requesting no bytes returns the empty SHAKE256 output. -/
@[simp] theorem shake256_zero_output (input : List (Fin 256)) : shake256 input 0 = [] := rfl

end Cslib.Crypto.Keccak
