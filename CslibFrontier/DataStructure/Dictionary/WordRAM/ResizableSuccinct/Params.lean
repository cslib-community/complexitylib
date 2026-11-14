/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlotInv
public import CslibFrontier.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Compacted Epoch Parameters, Dense Pair-Stream Packing, and `Memory.Prog` Bit-Slice Accessors

This module defines the 8-word persistent root header, the 225-word active epoch header, the
metadata-first compacted epoch layout, and the dense `[0, n)` `(quotient, value)` pair-stream
packing for the resizable succinct dynamic dictionary of [Bender, Farach-Colton, J. Kuszmaul and
W. Kuszmaul, SOSA 2024][BenderFarachColtonKuszmaulKuszmaul2024].

## Memory layout (`[metaBase, +offCompItems)` and `[itemBase, +compactedItemWords)`)

1. **Persistent 8-word root header (`[metaBase, metaBase + 8)`):**
   `[U, V, w, keyBits U, valBits V, N, n, n_init]`. When `n = 0` (`N = 0`), the resting dictionary
   occupies only these `8` words (`compactedEpochWords U V w 0 0 = 8`).
2. **Active epoch parameter and hash-scratch header (`[metaBase + 8, metaBase + 225)`):**
   * `[metaBase + 8, metaBase + 27)`: 19 words of `RuntimeReducedKWise.HashParams`.
   * `[metaBase + 27, metaBase + 63)`: 36 words of `CompParams`.
   * `[metaBase + 63, metaBase + 225)`: 162-word limb scratch (`RuntimeReducedKWise.scratchWords`).
3. **Epoch metadata prefix (`[metaBase + 225, metaBase + offCompItems U w N)`):**
   `Hash` (`Succinct.hashSpace U w N`), `LocalMeta` (`9 * Succinct.lmSubWords N w`), `GlobalMeta`,
   `TailToDense`, and `DenseToTail`.
4. **Dense `[0, n)` item stream (`[itemBase, itemBase + compactedItemWords U V w N n)`):**
   `n` active `(quotient, value)` pairs packed densely at global bit offsets
   `d * (quotientBits U N + valBits V)` and `d * (quotientBits U N + valBits V) + quotientBits U N`.
   Parameterizing `itemBase` separately from `metaBase` allows both resting in-epoch states
   (`itemBase = metaBase + offCompItems U w N`) and single-tape epoch migration (Zone 1 metadata +
   Zone 3 shared item arena) to share the exact same `Memory.Prog` operations.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.rootHdrWords`, `RootHeaderValid`,
  `EpochValid`, `targetCap`: root header and epoch capacity invariants.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.wOffQ`, `bOffQ`, `wOffV`, `bOffV`,
  `compactedItemWords`, `readBitSlice`, `writeBitSlice`, `compQuotAt`, `compValAt`,
  `writeCompQuot`, `writeCompVal`: overflow-free dense `[0, n)` pair-stream packing.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.epochHdrWords`, `offCompLM`,
  `offCompLMSub`, `offCompGM`, `offTailToDense`, `offDenseToTail`, `offCompItems`,
  `compactedEpochWords`: compacted epoch word offsets and total footprint.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompParams`, `mkCompParams`,
  `EpochParamsStored`: 36-word runtime parameter block and header storage predicate.

## Main results

* `compactedItemWords_succ_sub_le_two`: adding one item grows `compactedItemWords` by `≤ 2` words.
* `quotientBits_le_add_six_of_le_four_mul`, `succinctWords_mul_w_le_bits`: quotient-bit and
  word-to-bit space conversion helpers.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM

/-! ## Section 1: Dense `[0, n)` Pair-Stream Bit Packing -/

/-- Overflow-free word offset of the quotient field `q_d` at dense index `d` in a stream of
`(q_bits, v_bits)` pairs on a `w`-bit machine. -/
@[expose] def wOffQ (q_bits v_bits w d : ℕ) : ℕ :=
  wordOffset q_bits w d + wordOffset v_bits w d +
    (bitOffset q_bits w d + bitOffset v_bits w d) / w

/-- Intra-word bit offset `< w` of the quotient field `q_d` at dense index `d`. -/
@[expose] def bOffQ (q_bits v_bits w d : ℕ) : ℕ :=
  (bitOffset q_bits w d + bitOffset v_bits w d) % w

/-- Overflow-free word offset of the value field `v_d` at dense index `d`. -/
@[expose] def wOffV (q_bits v_bits w d : ℕ) : ℕ :=
  wOffQ q_bits v_bits w d + (bOffQ q_bits v_bits w d + q_bits) / w

/-- Intra-word bit offset `< w` of the value field `v_d` at dense index `d`. -/
@[expose] def bOffV (q_bits v_bits w d : ℕ) : ℕ :=
  (bOffQ q_bits v_bits w d + q_bits) % w

theorem bOffQ_lt {q_bits v_bits w d : ℕ} (hw : 0 < w) : bOffQ q_bits v_bits w d < w :=
  Nat.mod_lt _ hw

theorem bOffV_lt {q_bits v_bits w d : ℕ} (hw : 0 < w) : bOffV q_bits v_bits w d < w :=
  Nat.mod_lt _ hw

/-- Exact global bit-offset identity `wOffQ * w + bOffQ = d * (q_bits + v_bits)`. -/
theorem wOffQ_mul_add_bOffQ {q_bits v_bits w d : ℕ} :
    wOffQ q_bits v_bits w d * w + bOffQ q_bits v_bits w d = d * (q_bits + v_bits) := by
  unfold wOffQ bOffQ
  have hq := wordOffset_mul_add_bitOffset (k := q_bits) (w := w) (idx := d)
  have hv := wordOffset_mul_add_bitOffset (k := v_bits) (w := w) (idx := d)
  have hdiv := Nat.div_add_mod (bitOffset q_bits w d + bitOffset v_bits w d) w
  calc (wordOffset q_bits w d + wordOffset v_bits w d +
          (bitOffset q_bits w d + bitOffset v_bits w d) / w) * w +
        (bitOffset q_bits w d + bitOffset v_bits w d) % w
      = wordOffset q_bits w d * w + wordOffset v_bits w d * w +
          (w * ((bitOffset q_bits w d + bitOffset v_bits w d) / w) +
            (bitOffset q_bits w d + bitOffset v_bits w d) % w) := by ring
    _ = wordOffset q_bits w d * w + wordOffset v_bits w d * w +
          (bitOffset q_bits w d + bitOffset v_bits w d) := by rw [hdiv]
    _ = (wordOffset q_bits w d * w + bitOffset q_bits w d) +
          (wordOffset v_bits w d * w + bitOffset v_bits w d) := by ring
    _ = d * q_bits + d * v_bits := by rw [hq, hv]
    _ = d * (q_bits + v_bits) := by ring

/-- Exact global bit-offset identity `wOffV * w + bOffV = d * (q_bits + v_bits) + q_bits`. -/
theorem wOffV_mul_add_bOffV {q_bits v_bits w d : ℕ} :
    wOffV q_bits v_bits w d * w + bOffV q_bits v_bits w d =
      d * (q_bits + v_bits) + q_bits := by
  unfold wOffV bOffV
  have hq := wOffQ_mul_add_bOffQ (q_bits := q_bits) (v_bits := v_bits) (w := w) (d := d)
  have hdiv := Nat.div_add_mod (bOffQ q_bits v_bits w d + q_bits) w
  calc (wOffQ q_bits v_bits w d + (bOffQ q_bits v_bits w d + q_bits) / w) * w +
        (bOffQ q_bits v_bits w d + q_bits) % w
      = wOffQ q_bits v_bits w d * w +
          (w * ((bOffQ q_bits v_bits w d + q_bits) / w) +
            (bOffQ q_bits v_bits w d + q_bits) % w) := by ring
    _ = wOffQ q_bits v_bits w d * w + (bOffQ q_bits v_bits w d + q_bits) := by rw [hdiv]
    _ = (wOffQ q_bits v_bits w d * w + bOffQ q_bits v_bits w d) + q_bits := by ring
    _ = d * (q_bits + v_bits) + q_bits := by rw [hq]

/-- Word footprint of `n` densely packed `(quotient, value)` entries in epoch `N`. -/
@[expose] def compactedItemWords (U V w N n : ℕ) : ℕ :=
  (n * (quotientBits U N + valBits V) + w - 1) / w + 2

theorem wOffQ_add_one_lt_compactedItemWords {U V w N n d : ℕ} (hw : 0 < w) (hd : d < n) :
    wOffQ (quotientBits U N) (valBits V) w d + 1 < compactedItemWords U V w N n := by
  have hid := wOffQ_mul_add_bOffQ
    (q_bits := quotientBits U N) (v_bits := valBits V) (w := w) (d := d)
  have hle : d * (quotientBits U N + valBits V) ≤ n * (quotientBits U N + valBits V) :=
    Nat.mul_le_mul_right _ hd.le
  have hdiv : wOffQ (quotientBits U N) (valBits V) w d ≤
      (n * (quotientBits U N + valBits V) + w - 1) / w := by
    have h1 : wOffQ (quotientBits U N) (valBits V) w d =
        (d * (quotientBits U N + valBits V)) / w := by
      have hb := bOffQ_lt (q_bits := quotientBits U N) (v_bits := valBits V) (d := d) hw
      rw [← hid, Nat.mul_comm _ w, Nat.mul_add_div hw, Nat.div_eq_of_lt hb, add_zero]
    rw [h1]
    exact Nat.div_le_div_right (by omega)
  unfold compactedItemWords
  omega

theorem wOffV_add_one_lt_compactedItemWords {U V w N n d : ℕ} (hw : 0 < w) (hd : d < n) :
    wOffV (quotientBits U N) (valBits V) w d + 1 < compactedItemWords U V w N n := by
  have hid := wOffV_mul_add_bOffV
    (q_bits := quotientBits U N) (v_bits := valBits V) (w := w) (d := d)
  have hle : d * (quotientBits U N + valBits V) + quotientBits U N ≤
      n * (quotientBits U N + valBits V) := by
    have hsucc : (d + 1) * (quotientBits U N + valBits V) ≤
        n * (quotientBits U N + valBits V) := Nat.mul_le_mul_right _ hd
    rw [Nat.add_one_mul] at hsucc
    omega
  have hdiv : wOffV (quotientBits U N) (valBits V) w d ≤
      (n * (quotientBits U N + valBits V) + w - 1) / w := by
    have h1 : wOffV (quotientBits U N) (valBits V) w d =
        (d * (quotientBits U N + valBits V) + quotientBits U N) / w := by
      have hb := bOffV_lt (q_bits := quotientBits U N) (v_bits := valBits V) (d := d) hw
      rw [← hid, Nat.mul_comm _ w, Nat.mul_add_div hw, Nat.div_eq_of_lt hb, add_zero]
    rw [h1]
    exact Nat.div_le_div_right (by omega)
  unfold compactedItemWords
  omega

theorem compactedItemWords_mono {U V w N n₁ n₂ : ℕ} (h : n₁ ≤ n₂) :
    compactedItemWords U V w N n₁ ≤ compactedItemWords U V w N n₂ := by
  unfold compactedItemWords
  have hmul : n₁ * (quotientBits U N + valBits V) ≤ n₂ * (quotientBits U N + valBits V) :=
    Nat.mul_le_mul_right _ h
  have hdiv : (n₁ * (quotientBits U N + valBits V) + w - 1) / w ≤
      (n₂ * (quotientBits U N + valBits V) + w - 1) / w :=
    Nat.div_le_div_right (by omega)
  omega

/-- Adding `1` live item increases `compactedItemWords` by at most `2` words when `U, V ≤ 2 ^ w`. -/
theorem compactedItemWords_succ_sub_le_two {U V w N n : ℕ} (hw : 0 < w)
    (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w) :
    compactedItemWords U V w N (n + 1) - compactedItemWords U V w N n ≤ 2 := by
  have hq : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hv : valBits V ≤ w := Nat.clog_le_of_le_pow hV
  unfold compactedItemWords
  have hdiv : ((n + 1) * (quotientBits U N + valBits V) + w - 1) / w ≤
      (n * (quotientBits U N + valBits V) + w - 1) / w + 2 := by
    rw [Nat.add_mul, Nat.one_mul]
    calc (n * (quotientBits U N + valBits V) + (quotientBits U N + valBits V) + w - 1) / w
        ≤ (n * (quotientBits U N + valBits V) + w - 1 + 2 * w) / w :=
          Nat.div_le_div_right (by omega)
      _ = (n * (quotientBits U N + valBits V) + w - 1) / w + 2 :=
          Nat.add_mul_div_right _ _ hw
  omega

/-- Read a `k`-bit field starting at `(base + wOff, bOff)` across at most 2 words. -/
@[expose] def readBitSlice (base wOff bOff k w : ℕ) (mem : ℕ → ℕ) : ℕ :=
  let k₀ := min k (w - bOff)
  let k₁ := k - k₀
  let low := (mem (base + wOff) >>> bOff) &&& (2 ^ k₀ - 1)
  let high := (mem (base + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)
  low ^^^ (high <<< k₀)

/-- Write `val < 2 ^ k` into the `k`-bit field starting at `(base + wOff, bOff)`. -/
@[expose] def writeBitSlice (base wOff bOff k w : ℕ) (mem : ℕ → ℕ) (val : ℕ) : ℕ → ℕ :=
  let k₀ := min k (w - bOff)
  let k₁ := k - k₀
  let old₀ := (mem (base + wOff) >>> bOff) &&& (2 ^ k₀ - 1)
  let val₀ := val &&& (2 ^ k₀ - 1)
  let mem₁ := Function.update mem (base + wOff)
    (mem (base + wOff) ^^^ ((old₀ ^^^ val₀) <<< bOff))
  let old₁ := (mem₁ (base + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)
  let val₁ := (val >>> k₀) &&& (2 ^ k₁ - 1)
  Function.update mem₁ (base + wOff + 1)
    (mem₁ (base + wOff + 1) ^^^ ((old₁ ^^^ val₁) <<< 0))

theorem readBitSlice_lt (base wOff bOff k w : ℕ) (mem : ℕ → ℕ) :
    readBitSlice base wOff bOff k w mem < 2 ^ k := by
  unfold readBitSlice
  dsimp only
  set k₀ := min k (w - bOff)
  set k₁ := k - k₀
  have hsum : k₀ + k₁ = k := Nat.add_sub_of_le (Nat.min_le_left _ _)
  rw [← hsum]
  have hlow : ((mem (base + wOff) >>> bOff) &&& (2 ^ k₀ - 1)) < 2 ^ k₀ := by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hhigh : (((mem (base + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)) <<< k₀) < 2 ^ (k₀ + k₁) := by
    rw [Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_comm]
    refine Nat.mul_lt_mul_of_pos_left ?_ (by positivity)
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  exact Nat.xor_lt_two_pow (hlow.trans_le (Nat.pow_le_pow_right (by decide) (by omega))) hhigh

theorem readBitSlice_writeBitSlice_self (base wOff bOff k w : ℕ) (mem : ℕ → ℕ) {val : ℕ}
    (hval : val < 2 ^ k) :
    readBitSlice base wOff bOff k w (writeBitSlice base wOff bOff k w mem val) = val := by
  unfold readBitSlice writeBitSlice
  dsimp only
  set k₀ := min k (w - bOff)
  set k₁ := k - k₀
  set old₀ := (mem (base + wOff) >>> bOff) &&& (2 ^ k₀ - 1)
  set val₀ := val &&& (2 ^ k₀ - 1)
  set mem₁ := Function.update mem (base + wOff)
    (mem (base + wOff) ^^^ ((old₀ ^^^ val₀) <<< bOff))
  set old₁ := (mem₁ (base + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)
  set val₁ := (val >>> k₀) &&& (2 ^ k₁ - 1)
  have hne : base + wOff ≠ base + wOff + 1 := by omega
  have hmem0 :
      Function.update mem₁ (base + wOff + 1)
        (mem₁ (base + wOff + 1) ^^^ ((old₁ ^^^ val₁) <<< 0)) (base + wOff) =
        mem (base + wOff) ^^^ ((old₀ ^^^ val₀) <<< bOff) := by
    rw [Function.update_of_ne hne]
    exact Function.update_self _ _ _
  have hmem1 :
      Function.update mem₁ (base + wOff + 1)
        (mem₁ (base + wOff + 1) ^^^ ((old₁ ^^^ val₁) <<< 0)) (base + wOff + 1) =
        mem₁ (base + wOff + 1) ^^^ ((old₁ ^^^ val₁) <<< 0) :=
    Function.update_self _ _ _
  rw [hmem0, hmem1]
  have hval0_lt : val₀ < 2 ^ k₀ := by
    dsimp only [val₀]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hval1_lt : val₁ < 2 ^ k₁ := by
    dsimp only [val₁]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  rw [extract_xor_shiftLeft_self (mem (base + wOff)) bOff k₀ hval0_lt,
    extract_xor_shiftLeft_self (mem₁ (base + wOff + 1)) 0 k₁ hval1_lt]
  have hsum : k₀ + k₁ = k := Nat.add_sub_of_le (Nat.min_le_left _ _)
  exact low_xor_high_shiftLeft (hsum.symm ▸ hval)

/-- Non-interference of `writeBitSlice` and `readBitSlice` for disjoint global bit intervals. -/
theorem readBitSlice_writeBitSlice_of_disjoint {base wOff bOff k wOff' bOff' k' w : ℕ}
    (hb : bOff < w) (hb' : bOff' < w)
    (hdisj : (wOff * w + bOff) + k ≤ wOff' * w + bOff' ∨
      (wOff' * w + bOff') + k' ≤ wOff * w + bOff)
    (mem : ℕ → ℕ) (val : ℕ) :
    readBitSlice base wOff' bOff' k' w (writeBitSlice base wOff bOff k w mem val) =
      readBitSlice base wOff' bOff' k' w mem := by
  rcases Nat.eq_zero_or_pos k with rfl | _hk_pos
  · unfold readBitSlice writeBitSlice; dsimp only; simp
  unfold readBitSlice writeBitSlice
  dsimp only
  set k₀ := min k (w - bOff)
  set k₁ := k - k₀
  set k₀' := min k' (w - bOff')
  set k₁' := k' - k₀'
  set old₀ := (mem (base + wOff) >>> bOff) &&& (2 ^ k₀ - 1)
  set val₀ := val &&& (2 ^ k₀ - 1)
  set mem₁ := Function.update mem (base + wOff)
    (mem (base + wOff) ^^^ ((old₀ ^^^ val₀) <<< bOff))
  set old₁ := (mem₁ (base + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)
  set val₁ := (val >>> k₀) &&& (2 ^ k₁ - 1)
  set mem₂ := Function.update mem₁ (base + wOff + 1)
    (mem₁ (base + wOff + 1) ^^^ ((old₁ ^^^ val₁) <<< 0))
  have hδ0 : old₀ ^^^ val₀ < 2 ^ k₀ := by
    refine Nat.xor_lt_two_pow ?_ ?_ <;>
    · dsimp only [old₀, val₀]
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by positivity)
  have hδ1 : old₁ ^^^ val₁ < 2 ^ k₁ := by
    refine Nat.xor_lt_two_pow ?_ ?_ <;>
    · dsimp only [old₁, val₁]
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by positivity)
  have hsum : k₀ + k₁ = k := Nat.add_sub_of_le (Nat.min_le_left _ _)
  have hsum' : k₀' + k₁' = k' := Nat.add_sub_of_le (Nat.min_le_left _ _)
  have hle0 : bOff + k₀ ≤ w := by have := Nat.min_le_right k (w - bOff); omega
  have hle0' : bOff' + k₀' ≤ w := by have := Nat.min_le_right k' (w - bOff'); omega
  have hbw_of_pos : 0 < k₁ → bOff + k₀ = w := fun hk1 => by
    have hlt : w - bOff < k := by omega
    have hmin : k₀ = w - bOff := Nat.min_eq_right hlt.le
    omega
  have hbw'_of_pos : 0 < k₁' → bOff' + k₀' = w := fun hk1' => by
    have hlt : w - bOff' < k' := by omega
    have hmin : k₀' = w - bOff' := Nat.min_eq_right hlt.le
    omega
  have hw_add : (wOff + 1) * w = wOff * w + w := Nat.succ_mul wOff w
  have hw_add' : (wOff' + 1) * w = wOff' * w + w := Nat.succ_mul wOff' w
  have hlow_eq :
      ((mem₂ (base + wOff') >>> bOff') &&& (2 ^ k₀' - 1)) =
        ((mem (base + wOff') >>> bOff') &&& (2 ^ k₀' - 1)) := by
    rw [extract_update_xor_of_disjoint mem₁ (base + wOff + 1) (base + wOff') hδ1 (fun haddr => by
      rcases Nat.eq_zero_or_pos k₁ with hk1_0 | hk1_pos
      · left; omega
      · have hbw := hbw_of_pos hk1_pos
        have hw_eq : (wOff + 1) * w = wOff' * w := by
          have : wOff + 1 = wOff' := by omega
          rw [this]
        omega)]
    exact extract_update_xor_of_disjoint mem (base + wOff) (base + wOff') hδ0 (fun haddr => by
      have hw_eq : wOff * w = wOff' * w := by
        have : wOff = wOff' := by omega
        rw [this]
      omega)
  have hhigh_eq :
      ((mem₂ (base + wOff' + 1) >>> 0) &&& (2 ^ k₁' - 1)) =
        ((mem (base + wOff' + 1) >>> 0) &&& (2 ^ k₁' - 1)) := by
    rcases Nat.eq_zero_or_pos k₁' with hk1'_0 | hk1'_pos
    · simp [hk1'_0]
    · have hbw' := hbw'_of_pos hk1'_pos
      rw [extract_update_xor_of_disjoint mem₁ (base + wOff + 1) (base + wOff' + 1) hδ1
        (fun haddr => by
          rcases Nat.eq_zero_or_pos k₁ with hk1_0 | hk1_pos
          · left; omega
          · have hbw := hbw_of_pos hk1_pos
            have hw_eq : (wOff + 1) * w = (wOff' + 1) * w := by
              have : wOff + 1 = wOff' + 1 := by omega
              rw [this]
            omega)]
      exact extract_update_xor_of_disjoint mem (base + wOff) (base + wOff' + 1) hδ0 (fun haddr => by
        have hw_eq : wOff * w = (wOff' + 1) * w := by
          have : wOff = wOff' + 1 := by omega
          rw [this]
        omega)
  rw [hlow_eq, hhigh_eq]

/-- Pure extraction function for dense quotient `d < n` at `itemBase`. -/
@[expose] def compQuotAt (itemBase U V w N n : ℕ) (mem : ℕ → ℕ) (d : ℕ) : ℕ :=
  if d < n then
    let q_bits := quotientBits U N
    let v_bits := valBits V
    readBitSlice itemBase (wOffQ q_bits v_bits w d) (bOffQ q_bits v_bits w d) q_bits w mem
  else 0

/-- Pure extraction function for dense value `d < n` at `itemBase`. -/
@[expose] def compValAt (itemBase U V w N n : ℕ) (mem : ℕ → ℕ) (d : ℕ) : ℕ :=
  if d < n then
    let q_bits := quotientBits U N
    let v_bits := valBits V
    readBitSlice itemBase (wOffV q_bits v_bits w d) (bOffV q_bits v_bits w d) v_bits w mem
  else 0

/-- Write `q` into dense quotient `d` at `itemBase`. -/
@[expose] def writeCompQuot (itemBase U V w N : ℕ) (mem : ℕ → ℕ) (d q : ℕ) : ℕ → ℕ :=
  let q_bits := quotientBits U N
  let v_bits := valBits V
  writeBitSlice itemBase (wOffQ q_bits v_bits w d) (bOffQ q_bits v_bits w d) q_bits w mem q

/-- Write `v` into dense value `d` at `itemBase`. -/
@[expose] def writeCompVal (itemBase U V w N : ℕ) (mem : ℕ → ℕ) (d v : ℕ) : ℕ → ℕ :=
  let q_bits := quotientBits U N
  let v_bits := valBits V
  writeBitSlice itemBase (wOffV q_bits v_bits w d) (bOffV q_bits v_bits w d) v_bits w mem v

theorem compQuotAt_lt (itemBase U V w N n : ℕ) (mem : ℕ → ℕ) (d : ℕ) :
    compQuotAt itemBase U V w N n mem d < 2 ^ quotientBits U N := by
  unfold compQuotAt
  split_ifs
  · exact readBitSlice_lt _ _ _ _ _ _
  · positivity

theorem compValAt_lt (itemBase U V w N n : ℕ) (mem : ℕ → ℕ) (d : ℕ) :
    compValAt itemBase U V w N n mem d < 2 ^ valBits V := by
  unfold compValAt
  split_ifs
  · exact readBitSlice_lt _ _ _ _ _ _
  · positivity

theorem compQuotAt_writeCompQuot_self {itemBase U V w N n d q : ℕ} (mem : ℕ → ℕ)
    (hd : d < n) (hq : q < 2 ^ quotientBits U N) :
    compQuotAt itemBase U V w N n (writeCompQuot itemBase U V w N mem d q) d = q := by
  unfold compQuotAt writeCompQuot; simp only [hd, ↓reduceIte]
  exact readBitSlice_writeBitSlice_self _ _ _ _ _ _ hq

theorem compQuotAt_writeCompQuot_of_ne {itemBase U V w N n d d' q : ℕ} (hw : 0 < w)
    (mem : ℕ → ℕ) (hne : d' ≠ d) :
    compQuotAt itemBase U V w N n (writeCompQuot itemBase U V w N mem d q) d' =
      compQuotAt itemBase U V w N n mem d' := by
  unfold compQuotAt writeCompQuot
  split_ifs with hd'
  · refine readBitSlice_writeBitSlice_of_disjoint (bOffQ_lt hw) (bOffQ_lt hw) ?_ mem q
    rw [wOffQ_mul_add_bOffQ, wOffQ_mul_add_bOffQ]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · right
      have hle := Nat.mul_le_mul_right (quotientBits U N + valBits V) hlt
      rw [Nat.add_one_mul] at hle; omega
    · left
      have hle := Nat.mul_le_mul_right (quotientBits U N + valBits V) hgt
      rw [Nat.add_one_mul] at hle; omega
  · rfl

theorem compValAt_writeCompQuot {itemBase U V w N n d d' q : ℕ} (hw : 0 < w) (mem : ℕ → ℕ) :
    compValAt itemBase U V w N n (writeCompQuot itemBase U V w N mem d q) d' =
      compValAt itemBase U V w N n mem d' := by
  unfold compValAt writeCompQuot
  split_ifs with hd'
  · refine readBitSlice_writeBitSlice_of_disjoint (bOffQ_lt hw) (bOffV_lt hw) ?_ mem q
    rw [wOffQ_mul_add_bOffQ, wOffV_mul_add_bOffV]
    rcases lt_trichotomy d d' with hlt | rfl | hgt
    · left
      have hle := Nat.mul_le_mul_right (quotientBits U N + valBits V) hlt
      rw [Nat.add_one_mul] at hle; omega
    · left; omega
    · right
      have hle := Nat.mul_le_mul_right (quotientBits U N + valBits V) hgt
      rw [Nat.add_one_mul] at hle; omega
  · rfl

theorem compValAt_writeCompVal_self {itemBase U V w N n d v : ℕ} (mem : ℕ → ℕ)
    (hd : d < n) (hv : v < 2 ^ valBits V) :
    compValAt itemBase U V w N n (writeCompVal itemBase U V w N mem d v) d = v := by
  unfold compValAt writeCompVal; simp only [hd, ↓reduceIte]
  exact readBitSlice_writeBitSlice_self _ _ _ _ _ _ hv

theorem compValAt_writeCompVal_of_ne {itemBase U V w N n d d' v : ℕ} (hw : 0 < w)
    (mem : ℕ → ℕ) (hne : d' ≠ d) :
    compValAt itemBase U V w N n (writeCompVal itemBase U V w N mem d v) d' =
      compValAt itemBase U V w N n mem d' := by
  unfold compValAt writeCompVal
  split_ifs with hd'
  · refine readBitSlice_writeBitSlice_of_disjoint (bOffV_lt hw) (bOffV_lt hw) ?_ mem v
    rw [wOffV_mul_add_bOffV, wOffV_mul_add_bOffV]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · right
      have hle := Nat.mul_le_mul_right (quotientBits U N + valBits V) hlt
      rw [Nat.add_one_mul] at hle; omega
    · left
      have hle := Nat.mul_le_mul_right (quotientBits U N + valBits V) hgt
      rw [Nat.add_one_mul] at hle; omega
  · rfl

theorem compQuotAt_writeCompVal {itemBase U V w N n d d' v : ℕ} (hw : 0 < w) (mem : ℕ → ℕ) :
    compQuotAt itemBase U V w N n (writeCompVal itemBase U V w N mem d v) d' =
      compQuotAt itemBase U V w N n mem d' := by
  unfold compQuotAt writeCompVal
  split_ifs with hd'
  · refine readBitSlice_writeBitSlice_of_disjoint (bOffV_lt hw) (bOffQ_lt hw) ?_ mem v
    rw [wOffV_mul_add_bOffV, wOffQ_mul_add_bOffQ]
    rcases lt_trichotomy d' d with hlt | rfl | hgt
    · right
      have hle := Nat.mul_le_mul_right (quotientBits U N + valBits V) hlt
      rw [Nat.add_one_mul] at hle; omega
    · right; omega
    · left
      have hle := Nat.mul_le_mul_right (quotientBits U N + valBits V) hgt
      rw [Nat.add_one_mul] at hle; omega
  · rfl

theorem writeCompQuot_outside {itemBase U V w N n d q addr : ℕ} (hw : 0 < w) (hd : d < n)
    (mem : ℕ → ℕ) (haddr : ¬(itemBase ≤ addr ∧ addr < itemBase + compactedItemWords U V w N n)) :
    writeCompQuot itemBase U V w N mem d q addr = mem addr := by
  unfold writeCompQuot writeBitSlice
  have hlt := wOffQ_add_one_lt_compactedItemWords (U := U) (V := V) (N := N) hw hd
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

theorem writeCompVal_outside {itemBase U V w N n d v addr : ℕ} (hw : 0 < w) (hd : d < n)
    (mem : ℕ → ℕ) (haddr : ¬(itemBase ≤ addr ∧ addr < itemBase + compactedItemWords U V w N n)) :
    writeCompVal itemBase U V w N mem d v addr = mem addr := by
  unfold writeCompVal writeBitSlice
  have hlt := wOffV_add_one_lt_compactedItemWords (U := U) (V := V) (N := N) hw hd
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

theorem compQuotAt_congr {itemBase U V w N n : ℕ} (hw : 0 < w) {mem₁ mem₂ : ℕ → ℕ}
    (heq : ∀ addr, itemBase ≤ addr ∧ addr < itemBase + compactedItemWords U V w N n →
      mem₁ addr = mem₂ addr) :
    compQuotAt itemBase U V w N n mem₁ = compQuotAt itemBase U V w N n mem₂ := by
  funext d; unfold compQuotAt readBitSlice
  split_ifs with hd
  · dsimp only
    have hlt := wOffQ_add_one_lt_compactedItemWords (U := U) (V := V) (N := N) hw hd
    rw [heq (itemBase + wOffQ (quotientBits U N) (valBits V) w d) ⟨by omega, by omega⟩,
      heq (itemBase + wOffQ (quotientBits U N) (valBits V) w d + 1) ⟨by omega, by omega⟩]
  · rfl

theorem compValAt_congr {itemBase U V w N n : ℕ} (hw : 0 < w) {mem₁ mem₂ : ℕ → ℕ}
    (heq : ∀ addr, itemBase ≤ addr ∧ addr < itemBase + compactedItemWords U V w N n →
      mem₁ addr = mem₂ addr) :
    compValAt itemBase U V w N n mem₁ = compValAt itemBase U V w N n mem₂ := by
  funext d; unfold compValAt readBitSlice
  split_ifs with hd
  · dsimp only
    have hlt := wOffV_add_one_lt_compactedItemWords (U := U) (V := V) (N := N) hw hd
    rw [heq (itemBase + wOffV (quotientBits U N) (valBits V) w d) ⟨by omega, by omega⟩,
      heq (itemBase + wOffV (quotientBits U N) (valBits V) w d + 1) ⟨by omega, by omega⟩]
  · rfl

theorem compQuotAt_of_lt {itemBase U V w N n₁ n₂ d : ℕ} (mem : ℕ → ℕ)
    (hd₁ : d < n₁) (hd₂ : d < n₂) :
    compQuotAt itemBase U V w N n₁ mem d = compQuotAt itemBase U V w N n₂ mem d := by
  simp [compQuotAt, hd₁, hd₂]

theorem compValAt_of_lt {itemBase U V w N n₁ n₂ d : ℕ} (mem : ℕ → ℕ)
    (hd₁ : d < n₁) (hd₂ : d < n₂) :
    compValAt itemBase U V w N n₁ mem d = compValAt itemBase U V w N n₂ mem d := by
  simp [compValAt, hd₁, hd₂]

/-! ## Section 2: Persistent Root Header, Compacted Epoch Layout, and `1 · OPT` Space Bounds -/

/-- The 8-word persistent root header `[U, V, w, keyBits U, valBits V, N, n, n_init]`. -/
@[expose] def rootHdrWords : ℕ := 8
/-- Word offset `8` of the 19-word `RuntimeReducedKWise.HashParams` vector. -/
@[expose] def offHashParams : ℕ := 8
/-- Word offset `27` of the 36-word `CompParams` vector. -/
@[expose] def offCompParams : ℕ := 27
/-- Word offset `63` of the 162-word limb scratch slice (`63 + 162 = 225`). -/
@[expose] def offScratch : ℕ := 63
/-- Word offset `225` where the active epoch's `ReducedKWise` hash table and seed begin. -/
@[expose] def epochHdrWords : ℕ := 225

/-- Persistent 8-word root header invariant at `metaBase`. -/
structure RootHeaderValid (U V w N n n_init metaBase : ℕ) (mem : ℕ → ℕ) : Prop where
  hdr_U : mem metaBase = U
  hdr_V : mem (metaBase + 1) = V
  hdr_w : mem (metaBase + 2) = w
  hdr_keyBits : mem (metaBase + 3) = keyBits U
  hdr_valBits : mem (metaBase + 4) = valBits V
  hdr_N : mem (metaBase + 5) = N
  hdr_n : mem (metaBase + 6) = n
  hdr_n_init : mem (metaBase + 7) = n_init

/-- Epoch capacity invariant: `N = 0` when `n = 0`, else `1 ≤ n ≤ N ≤ 4 * n ∧ N ≤ U`. -/
@[expose] def EpochValid (U n N : ℕ) : Prop :=
  (n = 0 ∧ N = 0) ∨ (1 ≤ n ∧ n ≤ N ∧ N ≤ 4 * n ∧ N ≤ U)

/-- Target epoch capacity `min (2 * n) U` (`0` when `n = 0`). -/
@[expose] def targetCap (U n : ℕ) : ℕ :=
  if n = 0 then 0 else min (2 * n) U

theorem epochValid_targetCap {U n : ℕ} (hnU : n ≤ U) : EpochValid U n (targetCap U n) := by
  unfold EpochValid targetCap
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Or.inl ⟨rfl, rfl⟩
  · rw [ite_eq_right (by omega)]
    exact Or.inr ⟨hn, le_min (by omega) hnU, (min_le_left _ _).trans (by omega), min_le_right _ _⟩

/-- Effective quotient bit-width `max (quotientBits U N) 1` (`= Succinct.qBits U N`). -/
abbrev epochQBits (U N : ℕ) : ℕ := max (quotientBits U N) 1

/-- Reduction target bit-width `totalMicroBits N + 1` (`= Succinct.hashB N`). -/
abbrev epochHashB (N : ℕ) : ℕ := totalMicroBits N + 1

/-- Word footprint of the epoch quotient hash (`= Succinct.hashSpace U w N`). -/
abbrev epochHashSpace (U w N : ℕ) : ℕ :=
  ReducedKWise.space w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3

/-- Word offset of `LocalMeta` relative to `metaBase` in a compacted epoch of capacity `N`. -/
@[expose] def offCompLM (U w N : ℕ) : ℕ :=
  epochHdrWords + epochHashSpace U w N

/-- Word offset of the `c`-th `LocalMeta` sub-array (`c < 9`) relative to `metaBase`. -/
@[expose] def offCompLMSub (U w N c : ℕ) : ℕ :=
  offCompLM U w N + c * lmSubWords N w

/-- Word offset of `GlobalMeta` relative to `metaBase` in a compacted epoch of capacity `N`. -/
@[expose] def offCompGM (U w N : ℕ) : ℕ :=
  offCompLM U w N + 9 * lmSubWords N w

/-- Word offset of `TailToDense` relative to `metaBase`. -/
@[expose] def offTailToDense (U w N : ℕ) : ℕ :=
  offCompGM U w N + packedWords (globalMetaLen N) (globalPtrBits N) w

/-- Word offset of `DenseToTail` relative to `metaBase`. -/
@[expose] def offDenseToTail (U w N : ℕ) : ℕ :=
  offTailToDense U w N + packedWords (maxTailItems N) (globalPtrBits N) w

/-- Word offset of the dense `[0, n)` active `(quotient, value)` stream relative to `metaBase`. -/
@[expose] def offCompItems (U w N : ℕ) : ℕ :=
  offDenseToTail U w N + packedWords (maxTailItems N) (globalPtrBits N) w

/-- Total resting word footprint of a compacted epoch `(N, n)`:
`8` words when `n = 0` (`rootHdrWords`), and `offCompItems U w N + compactedItemWords U V w N n`
when `0 < n`. -/
@[expose] def compactedEpochWords (U V w N n : ℕ) : ℕ :=
  if n = 0 then rootHdrWords else offCompItems U w N + compactedItemWords U V w N n

theorem eight_le_compactedEpochWords (U V w N n : ℕ) :
    8 ≤ compactedEpochWords U V w N n := by
  unfold compactedEpochWords rootHdrWords offCompItems offDenseToTail offTailToDense offCompGM
    offCompLM epochHdrWords
  split_ifs <;> omega

theorem compactedEpochWords_mono {U V w N n₁ n₂ : ℕ} (h : n₁ ≤ n₂) :
    compactedEpochWords U V w N n₁ ≤ compactedEpochWords U V w N n₂ := by
  unfold compactedEpochWords rootHdrWords
  split_ifs with h1 h2
  · exact le_rfl
  · unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega
  · omega
  · exact Nat.add_le_add_left (compactedItemWords_mono h) _

theorem clog_two_mul_le (x : ℕ) : Nat.clog 2 (2 * x) ≤ Nat.clog 2 x + 1 := by
  rw [Nat.clog_le_iff_le_pow one_lt_two, pow_succ']
  exact Nat.mul_le_mul_left 2 (Nat.le_pow_clog one_lt_two x)

theorem logLogFactor_two_mul_le_add_one (n : ℕ) :
    Dynamic.logLogFactor (2 * n) ≤ Dynamic.logLogFactor n + 1 := by
  unfold Dynamic.logLogFactor
  have hm : max (2 * n) 4 ≤ 2 * max n 4 := by omega
  have hc1 : Nat.clog 2 (max (2 * n) 4) ≤ 2 * Nat.clog 2 (max n 4) := by
    have hle1 := Nat.clog_mono_right 2 hm
    have hle2 := clog_two_mul_le (max n 4)
    have hpos : 1 ≤ Nat.clog 2 (max n 4) := by
      have h4 := Nat.clog_mono_right 2 (le_max_right n 4)
      have : Nat.clog 2 4 = 2 := by decide
      omega
    omega
  exact (Nat.clog_mono_right 2 hc1).trans (clog_two_mul_le _)

theorem logLogFactor_four_mul_le_add_two (n : ℕ) :
    Dynamic.logLogFactor (4 * n) ≤ Dynamic.logLogFactor n + 2 := by
  rw [show 4 * n = 2 * (2 * n) by ring]
  exact (logLogFactor_two_mul_le_add_one (2 * n)).trans
    (Nat.add_le_add_right (logLogFactor_two_mul_le_add_one n) 1)

theorem logLogFactor_four_mul_le (n : ℕ) :
    Dynamic.logLogFactor (4 * n) ≤ 4 * Dynamic.logLogFactor n := by
  have h1 := logLogFactor_four_mul_le_add_two n
  have h2 := Dynamic.one_le_logLogFactor n
  omega

theorem quotientBits_le_add_six_of_le_four_mul {n N : ℕ} (U : ℕ)
    (hnN : n ≤ N) (hN4 : N ≤ 4 * n) :
    quotientBits U N ≤ quotientBits U n + 6 := by
  have hlog : Nat.log 2 n ≤ Nat.log 2 N := Nat.log_mono_right hnN
  have hll : Dynamic.logLogFactor N ≤ Dynamic.logLogFactor n + 2 :=
    (Dynamic.logLogFactor_mono hN4).trans (logLogFactor_four_mul_le_add_two n)
  unfold quotientBits bucketBits
  omega

theorem succinctWords_mul_w_le_bits (C C₀ U V w n : ℕ) :
    w * Dynamic.succinctWords C C₀ U V w n ≤
      Dynamic.optBits U V n + C * n * Dynamic.logLogFactor n + (C₀ + 1) * w := by
  unfold Dynamic.succinctWords
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp
  · set B := Dynamic.optBits U V n + C * n * Dynamic.logLogFactor n
    have hmul : w * ((B + w - 1) / w) ≤ B + w - 1 := Nat.mul_div_le (B + w - 1) w
    calc w * ((B + w - 1) / w + C₀)
        = w * ((B + w - 1) / w) + C₀ * w := by ring
      _ ≤ (B + w - 1) + C₀ * w := Nat.add_le_add_right hmul _
      _ ≤ B + (C₀ + 1) * w := by
        have : (C₀ + 1) * w = C₀ * w + w := by ring
        omega

/-! ## Section 3: Pure Metadata Extractors and Runtime `CompParams` -/

/-- Pure extraction function for `LocalMeta` in a compacted epoch at `metaBase`. -/
@[expose] def compLmAt (metaBase U w N : ℕ) (mem : ℕ → ℕ) : ℕ × ℕ → ℕ
  | (c, idx) =>
    if c < 9 ∧ idx < totalMicroBuckets N then
      readPacked (metaBase + offCompLMSub U w N c) (effBucketPosBits N) w mem idx
    else 0

/-- Pure extraction function for `GlobalMeta` in a compacted epoch at `metaBase`. -/
@[expose] def compGmAt (metaBase U w N : ℕ) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx < globalMetaLen N then
    readPacked (metaBase + offCompGM U w N) (globalPtrBits N) w mem idx
  else 0

/-- Pure extraction function for `TailToDense[t]` (`0` when `t ≥ maxTailItems N`). -/
@[expose] def compTDAt (metaBase U w N : ℕ) (mem : ℕ → ℕ) (t : ℕ) : ℕ :=
  if t < maxTailItems N then
    readPacked (metaBase + offTailToDense U w N) (globalPtrBits N) w mem t
  else 0

/-- Pure extraction function for `DenseToTail[r]` (`0` when `r ≥ maxTailItems N`). -/
@[expose] def compDTAt (metaBase U w N : ℕ) (mem : ℕ → ℕ) (r : ℕ) : ℕ :=
  if r < maxTailItems N then
    readPacked (metaBase + offDenseToTail U w N) (globalPtrBits N) w mem r
  else 0

/-- Runtime 36-word parameter vector stored at `[metaBase + offCompParams, +36)`. -/
@[expose] def CompParams : Type := Fin 36 → ℕ

instance : WordEncoding CompParams := ⟨36, Function.Embedding.refl (Fin 36 → ℕ)⟩

/-- Populate the 36-word `CompParams` vector for `(U, V, w, N)`. -/
@[expose] def mkCompParams (U V w N : ℕ) : CompParams := fun i =>
  match i.val with
  | 0 => w
  | 1 => N
  | 2 => N - 1
  | 3 => quotientBits U N
  | 4 => valBits V
  | 5 => offCompLMSub U w N 0
  | 6 => offCompLMSub U w N 1
  | 7 => offCompLMSub U w N 2
  | 8 => offCompLMSub U w N 3
  | 9 => offCompLMSub U w N 4
  | 10 => offCompLMSub U w N 5
  | 11 => offCompLMSub U w N 6
  | 12 => offCompLMSub U w N 7
  | 13 => offCompLMSub U w N 8
  | 14 => effBucketPosBits N
  | 15 => offCompGM U w N
  | 16 => globalPtrBits N
  | 17 => offTailToDense U w N
  | 18 => offDenseToTail U w N
  | 19 => maxTailItems N
  | 20 => bucketBits N
  | 21 => 2 ^ bucketBits N - 1
  | 22 => slabSize N
  | 23 => slabSize N - 1
  | 24 => 2 * slabSize N
  | 25 => dirSlabsPerBucket N
  | 26 => dirSlabsPerBucket N - 1
  | 27 => tailCapPerBucket N
  | 28 => gmSlabDirBase N
  | 29 => gmTailPtrBase N
  | 30 => gmTailOwnerBase N
  | 31 => gmSlabMetaBase N
  | 32 => numMicroPerBucket N
  | 33 => min N (effBucketCap N)
  | 34 => offCompItems U w N
  | 35 => epochHashSpace U w N
  | _ => 0

abbrev cpW (cp : CompParams) : ℕ := cp ⟨0, by decide⟩
abbrev cpN (cp : CompParams) : ℕ := cp ⟨1, by decide⟩
abbrev cpNSubOne (cp : CompParams) : ℕ := cp ⟨2, by decide⟩
abbrev cpQuotBits (cp : CompParams) : ℕ := cp ⟨3, by decide⟩
abbrev cpValBits (cp : CompParams) : ℕ := cp ⟨4, by decide⟩
abbrev cpOffLMSub (c : Fin 9) (cp : CompParams) : ℕ :=
  match c.val with
  | 0 => cp ⟨5, by decide⟩ | 1 => cp ⟨6, by decide⟩ | 2 => cp ⟨7, by decide⟩
  | 3 => cp ⟨8, by decide⟩ | 4 => cp ⟨9, by decide⟩ | 5 => cp ⟨10, by decide⟩
  | 6 => cp ⟨11, by decide⟩ | 7 => cp ⟨12, by decide⟩ | _ => cp ⟨13, by decide⟩
abbrev cpLmBits (cp : CompParams) : ℕ := cp ⟨14, by decide⟩
abbrev cpOffGM (cp : CompParams) : ℕ := cp ⟨15, by decide⟩
abbrev cpGmBits (cp : CompParams) : ℕ := cp ⟨16, by decide⟩
abbrev cpOffTD (cp : CompParams) : ℕ := cp ⟨17, by decide⟩
abbrev cpOffDT (cp : CompParams) : ℕ := cp ⟨18, by decide⟩
abbrev cpMaxTail (cp : CompParams) : ℕ := cp ⟨19, by decide⟩
abbrev cpBucketBits (cp : CompParams) : ℕ := cp ⟨20, by decide⟩
abbrev cpBucketMask (cp : CompParams) : ℕ := cp ⟨21, by decide⟩
abbrev cpSlabSize (cp : CompParams) : ℕ := cp ⟨22, by decide⟩
abbrev cpSlabSizeSubOne (cp : CompParams) : ℕ := cp ⟨23, by decide⟩
abbrev cpTwoSlabSize (cp : CompParams) : ℕ := cp ⟨24, by decide⟩
abbrev cpDirSlabs (cp : CompParams) : ℕ := cp ⟨25, by decide⟩
abbrev cpDirSlabsSubOne (cp : CompParams) : ℕ := cp ⟨26, by decide⟩
abbrev cpTailCap (cp : CompParams) : ℕ := cp ⟨27, by decide⟩
abbrev cpGmSlabDirBase (cp : CompParams) : ℕ := cp ⟨28, by decide⟩
abbrev cpGmTailPtrBase (cp : CompParams) : ℕ := cp ⟨29, by decide⟩
abbrev cpGmTailOwnerBase (cp : CompParams) : ℕ := cp ⟨30, by decide⟩
abbrev cpGmSlabMetaBase (cp : CompParams) : ℕ := cp ⟨31, by decide⟩
abbrev cpNumMicro (cp : CompParams) : ℕ := cp ⟨32, by decide⟩
abbrev cpMinCap (cp : CompParams) : ℕ := cp ⟨33, by decide⟩
abbrev cpOffItems (cp : CompParams) : ℕ := cp ⟨34, by decide⟩
abbrev cpHashSpace (cp : CompParams) : ℕ := cp ⟨35, by decide⟩

@[simp] theorem cpOffLMSub_mk (U V w N : ℕ) (c : Fin 9) :
    cpOffLMSub c (mkCompParams U V w N) = offCompLMSub U w N c.val := by
  rcases c with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | c, hc⟩ <;> try rfl
  omega

@[simp] theorem cpW_mk (U V w N : ℕ) : cpW (mkCompParams U V w N) = w := rfl
@[simp] theorem cpN_mk (U V w N : ℕ) : cpN (mkCompParams U V w N) = N := rfl
@[simp] theorem cpNSubOne_mk (U V w N : ℕ) : cpNSubOne (mkCompParams U V w N) = N - 1 := rfl
@[simp] theorem cpQuotBits_mk (U V w N : ℕ) :
    cpQuotBits (mkCompParams U V w N) = quotientBits U N := rfl
@[simp] theorem cpValBits_mk (U V w N : ℕ) : cpValBits (mkCompParams U V w N) = valBits V := rfl
@[simp] theorem cpLmBits_mk (U V w N : ℕ) :
    cpLmBits (mkCompParams U V w N) = effBucketPosBits N := rfl
@[simp] theorem cpOffGM_mk (U V w N : ℕ) : cpOffGM (mkCompParams U V w N) = offCompGM U w N := rfl
@[simp] theorem cpGmBits_mk (U V w N : ℕ) :
    cpGmBits (mkCompParams U V w N) = globalPtrBits N := rfl
@[simp] theorem cpOffTD_mk (U V w N : ℕ) :
    cpOffTD (mkCompParams U V w N) = offTailToDense U w N := rfl
@[simp] theorem cpOffDT_mk (U V w N : ℕ) :
    cpOffDT (mkCompParams U V w N) = offDenseToTail U w N := rfl
@[simp] theorem cpMaxTail_mk (U V w N : ℕ) :
    cpMaxTail (mkCompParams U V w N) = maxTailItems N := rfl
@[simp] theorem cpBucketBits_mk (U V w N : ℕ) :
    cpBucketBits (mkCompParams U V w N) = bucketBits N := rfl
@[simp] theorem cpBucketMask_mk (U V w N : ℕ) :
    cpBucketMask (mkCompParams U V w N) = 2 ^ bucketBits N - 1 := rfl
@[simp] theorem cpSlabSize_mk (U V w N : ℕ) : cpSlabSize (mkCompParams U V w N) = slabSize N := rfl
@[simp] theorem cpSlabSizeSubOne_mk (U V w N : ℕ) :
    cpSlabSizeSubOne (mkCompParams U V w N) = slabSize N - 1 := rfl
@[simp] theorem cpTwoSlabSize_mk (U V w N : ℕ) :
    cpTwoSlabSize (mkCompParams U V w N) = 2 * slabSize N := rfl
@[simp] theorem cpDirSlabs_mk (U V w N : ℕ) :
    cpDirSlabs (mkCompParams U V w N) = dirSlabsPerBucket N := rfl
@[simp] theorem cpDirSlabsSubOne_mk (U V w N : ℕ) :
    cpDirSlabsSubOne (mkCompParams U V w N) = dirSlabsPerBucket N - 1 := rfl
@[simp] theorem cpTailCap_mk (U V w N : ℕ) :
    cpTailCap (mkCompParams U V w N) = tailCapPerBucket N := rfl
@[simp] theorem cpGmSlabDirBase_mk (U V w N : ℕ) :
    cpGmSlabDirBase (mkCompParams U V w N) = gmSlabDirBase N := rfl
@[simp] theorem cpGmTailPtrBase_mk (U V w N : ℕ) :
    cpGmTailPtrBase (mkCompParams U V w N) = gmTailPtrBase N := rfl
@[simp] theorem cpGmTailOwnerBase_mk (U V w N : ℕ) :
    cpGmTailOwnerBase (mkCompParams U V w N) = gmTailOwnerBase N := rfl
@[simp] theorem cpGmSlabMetaBase_mk (U V w N : ℕ) :
    cpGmSlabMetaBase (mkCompParams U V w N) = gmSlabMetaBase N := rfl
@[simp] theorem cpNumMicro_mk (U V w N : ℕ) :
    cpNumMicro (mkCompParams U V w N) = numMicroPerBucket N := rfl
@[simp] theorem cpMinCap_mk (U V w N : ℕ) :
    cpMinCap (mkCompParams U V w N) = min N (effBucketCap N) := rfl
@[simp] theorem cpOffItems_mk (U V w N : ℕ) :
    cpOffItems (mkCompParams U V w N) = offCompItems U w N := rfl
@[simp] theorem cpHashSpace_mk (U V w N : ℕ) :
    cpHashSpace (mkCompParams U V w N) = epochHashSpace U w N := rfl

/-- Stored runtime parameter blocks in `[metaBase + 8, metaBase + 63)` for active epoch `N`. -/
structure EpochParamsStored (U V w N metaBase : ℕ) (mem : ℕ → ℕ) : Prop where
  hp_eq : ∀ i : Fin 19, mem (metaBase + offHashParams + i.val) =
    RuntimeReducedKWise.mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3 i
  cp_eq : ∀ i : Fin 36, mem (metaBase + offCompParams + i.val) = mkCompParams U V w N i

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
