/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.ApproximateMembership.QuotientFilter.Operations
public import Complexity.DataStructure.ApproximateMembership.QuotientFilter.Probability
public import Complexity.DataStructure.HashFamily.WordRAM.ReducedKWise

/-!
# Bit-Packed Slot Arrays for the Word-RAM Quotient Filter

This file defines the compact bit-packed memory layout and extraction/update laws for the
two-stage quotient filter:

1. **Generic power-of-2 bit-packed array (`slotPackShift`, `packedWords`, `extractPacked`,
   `writePackedMem`)**:
   For `2 ^ b` slots of `d`-bit entries (`0 < d`, `2 * d ≤ w`), each word packs
   `2 ^ p` entries where `p = slotPackShift b d w = min b (Nat.log 2 (w / (2 * d)))`.
   Because `p ≤ b` and `2 ^ p * d ≤ w / 2 < w`, the array occupies `packedWords b d w = 2 ^ (b - p)
   ≤ 4 * (2 ^ b * d) / w + 1` words, no entry ever crosses a word boundary, and every intermediate
   bit-shift mask fits strictly inside a `w`-bit word.
2. **Quotient-filter memory layout and total state extraction (`extractFilterState`, `space_le`)**:
   Packs `ReducedKWise` (`5`-wise quotient hash seed and bit-packed table), the `1`-word remainder
   seed `γ : RemSeed w₀`, three `1`-bit slot arrays (`isFull`, `isOcc`, `isRunStart`), and one
   `f`-bit remainder array (`remAt`, `f = remBits w₀ k = min w₀ (k + 1)`) into
   `space w w₀ n k ≤ 640 * ((n * k + w - 1) / w + 1)` words.
3. **Slot modular arithmetic and memory layout offsets (`add_and_eq_probeSlot_val`,
   `add_sub_and_eq_backSlot_val`, `remSeedOff`, `fullOff`, `occOff`, `runOff`, `remOff`)**:
   Relates bitwise slot masks to `probeSlot` / `backSlot` and base-relative offsets to physical
   array addresses.
-/

public section

namespace Cslib.DataStructure.ApproximateMembership.QuotientFilter

open Finset
open Cslib.WordRAM Cslib.WordRAM.ExactLog
open Cslib.Probability
open Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.Dictionary.WordRAM.LinearProbing
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.WordRAM.LinearProbing
open scoped BigOperators ENNReal

/-! ## Section 1: Generic power-of-2 bit-packed slot array arithmetic -/

/-- Log₂ of the number of `d`-bit entries packed per `w`-bit word in a `2 ^ b`-slot array:
`min b (Nat.log 2 (w / (2 * d)))`. -/
@[expose] def slotPackShift (b d w : ℕ) : ℕ :=
  min b (Nat.log 2 (w / (2 * d)))

/-- Number of `w`-bit words `2 ^ (b - slotPackShift b d w)` used by a `2 ^ b`-slot packed array of
`d`-bit entries. -/
@[expose] def packedWords (b d w : ℕ) : ℕ :=
  2 ^ (b - slotPackShift b d w)

theorem slotPackShift_le (b d w : ℕ) : slotPackShift b d w ≤ b :=
  min_le_left b _

theorem packedWords_pos (b d w : ℕ) : 0 < packedWords b d w :=
  Nat.two_pow_pos _

theorem packedWords_mul_two_pow_slotPackShift (b d w : ℕ) :
    packedWords b d w * 2 ^ slotPackShift b d w = 2 ^ b := by
  dsimp only [packedWords]
  rw [← pow_add, Nat.sub_add_cancel (slotPackShift_le b d w)]

/-- Whenever `0 < d` and `2 * d ≤ w`, the total bits `2 ^ (slotPackShift b d w) * d` used per word
is at most `w / 2` (and hence strictly less than `w`). -/
theorem two_pow_slotPackShift_mul_le {b d w : ℕ} (hd : 0 < d) (hdw : 2 * d ≤ w) :
    2 ^ slotPackShift b d w * d ≤ w / 2 := by
  have hdiv_pos : 0 < w / (2 * d) := Nat.div_pos hdw (by omega)
  have hle_log : slotPackShift b d w ≤ Nat.log 2 (w / (2 * d)) := min_le_right b _
  have hpow_le : 2 ^ slotPackShift b d w ≤ w / (2 * d) :=
    (Nat.pow_le_pow_right two_pos hle_log).trans (Nat.pow_log_le_self 2 (by omega))
  have hmul : 2 * (2 ^ slotPackShift b d w * d) ≤ w := by
    calc 2 * (2 ^ slotPackShift b d w * d)
        = 2 ^ slotPackShift b d w * (2 * d) := by ring
      _ ≤ w := (Nat.mul_le_mul_right (2 * d) hpow_le).trans (Nat.div_mul_le_self w (2 * d))
  omega

theorem two_pow_slotPackShift_mul_lt {b d w : ℕ} (hd : 0 < d) (hdw : 2 * d ≤ w) :
    2 ^ slotPackShift b d w * d < w := by
  have hle := two_pow_slotPackShift_mul_le (b := b) hd hdw
  omega

/-- Word-count upper bound: whenever `0 < d` and `2 * d ≤ w`, `packedWords b d w` is at most
`4 * (2 ^ b * d) / w + 1`. -/
theorem packedWords_le {b d w : ℕ} (hd : 0 < d) (hdw : 2 * d ≤ w) :
    packedWords b d w ≤ 4 * (2 ^ b * d) / w + 1 := by
  dsimp only [packedWords, slotPackShift]
  by_cases hle : b ≤ Nat.log 2 (w / (2 * d))
  · rw [min_eq_left hle, Nat.sub_self, pow_zero]
    exact Nat.le_add_left 1 _
  · push Not at hle
    rw [min_eq_right hle.le]
    set p := Nat.log 2 (w / (2 * d))
    have hgt : w / (2 * d) < 2 ^ (p + 1) := Nat.lt_pow_succ_log_self one_lt_two _
    have hw_lt : w < 2 ^ (p + 1) * (2 * d) := by
      have h1 := Nat.div_add_mod w (2 * d)
      have h2 : w % (2 * d) < 2 * d := Nat.mod_lt w (by omega)
      have h3 : (w / (2 * d) + 1) * (2 * d) ≤ 2 ^ (p + 1) * (2 * d) :=
        Nat.mul_le_mul_right (2 * d) hgt
      nlinarith
    have hpow_split : 2 ^ b = 2 ^ (b - p) * 2 ^ p := by
      rw [← pow_add, Nat.sub_add_cancel hle.le]
    have hmul_le : 2 ^ (b - p) * w ≤ 4 * (2 ^ b * d) := by
      calc 2 ^ (b - p) * w
          ≤ 2 ^ (b - p) * (2 ^ (p + 1) * (2 * d)) := Nat.mul_le_mul_left _ hw_lt.le
        _ = 4 * ((2 ^ (b - p) * 2 ^ p) * d) := by rw [pow_succ]; ring
        _ = 4 * (2 ^ b * d) := by rw [hpow_split]
    have hdiv : 2 ^ (b - p) ≤ 4 * (2 ^ b * d) / w :=
      Nat.le_div_iff_mul_le (by omega) |>.mpr hmul_le
    omega

theorem shiftRight_lt_packedWords (b d w : ℕ) (q : Fin (2 ^ b)) :
    q.val >>> slotPackShift b d w < packedWords b d w := by
  rw [Nat.shiftRight_eq_div_pow]
  apply Nat.div_lt_of_lt_mul
  rw [mul_comm, packedWords_mul_two_pow_slotPackShift]
  exact q.isLt

theorem and_two_pow_slotPackShift_lt (b d w : ℕ) (q : Fin (2 ^ b)) :
    q.val &&& (2 ^ slotPackShift b d w - 1) < 2 ^ slotPackShift b d w := by
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem shiftRight_mul_add_and_eq (x p : ℕ) :
    (x >>> p) * 2 ^ p + (x &&& (2 ^ p - 1)) = x := by
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod, mul_comm, Nat.div_add_mod]

/-- Extract the `d`-bit value at slot `q : Fin (2 ^ b)` from a packed array starting at `arrBase`.
-/
@[expose] def extractPacked (arrBase b d w : ℕ) (mem : ℕ → ℕ) (q : Fin (2 ^ b)) : Fin (2 ^ d) :=
  let p := slotPackShift b d w
  ⟨getLimb d (mem (arrBase + (q.val >>> p))) (q.val &&& (2 ^ p - 1)), getLimb_lt d _ _⟩

/-- Update the `d`-bit entry at slot `q : Fin (2 ^ b)` in a packed array starting at `arrBase` to
`val`. -/
@[expose] def writePackedMem (arrBase b d w : ℕ) (mem : ℕ → ℕ) (q : Fin (2 ^ b)) (val : ℕ) :
    ℕ → ℕ :=
  let p := slotPackShift b d w
  let wIdx := q.val >>> p
  let subIdx := q.val &&& (2 ^ p - 1)
  let sh := subIdx * d
  let oldWord := mem (arrBase + wIdx)
  let oldLimb := (oldWord >>> sh) &&& (2 ^ d - 1)
  let newWord := oldWord ^^^ ((oldLimb ^^^ val) <<< sh)
  Function.update mem (arrBase + wIdx) newWord

theorem writePackedMem_outside (arrBase b d w : ℕ) (mem : ℕ → ℕ) (q : Fin (2 ^ b)) (val : ℕ)
    {a : ℕ} (ha : a < arrBase ∨ arrBase + packedWords b d w ≤ a) :
    writePackedMem arrBase b d w mem q val a = mem a := by
  unfold writePackedMem
  have hwIdx := shiftRight_lt_packedWords b d w q
  generalize q.val >>> slotPackShift b d w = wIdx at hwIdx ⊢
  rw [Function.update_of_ne (by omega)]

@[simp]
theorem extractPacked_writePackedMem_self (arrBase b d w : ℕ) (mem : ℕ → ℕ)
    (q : Fin (2 ^ b)) (val : Fin (2 ^ d)) :
    extractPacked arrBase b d w (writePackedMem arrBase b d w mem q val.val) q = val := by
  apply Fin.ext
  dsimp only [extractPacked, writePackedMem]
  set p := slotPackShift b d w
  set wIdx := q.val >>> p
  set subIdx := q.val &&& (2 ^ p - 1)
  set oldWord := mem (arrBase + wIdx)
  set oldLimb := getLimb d oldWord subIdx
  have hold_lt : oldLimb < 2 ^ d := getLimb_lt d oldWord subIdx
  have hdiff_lt : oldLimb ^^^ val.val < 2 ^ d := Nat.xor_lt_two_pow hold_lt val.isLt
  rw [Function.update_self]
  change getLimb d (oldWord ^^^ ((oldLimb ^^^ val.val) <<< (subIdx * d))) subIdx = val.val
  rw [getLimb_xor]
  have hsh := getLimb_shiftLeft_mul_add d (oldLimb ^^^ val.val) subIdx 0
  rw [add_zero] at hsh
  have h0 : getLimb d (oldLimb ^^^ val.val) 0 = oldLimb ^^^ val.val := by
    dsimp only [getLimb]
    rw [zero_mul, Nat.shiftRight_zero, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hdiff_lt]
  rw [hsh, h0, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem extractPacked_writePackedMem_of_ne (arrBase b d w : ℕ) (mem : ℕ → ℕ)
    (q q' : Fin (2 ^ b)) (val : Fin (2 ^ d)) (hne : q' ≠ q) :
    extractPacked arrBase b d w (writePackedMem arrBase b d w mem q val.val) q' =
      extractPacked arrBase b d w mem q' := by
  apply Fin.ext
  dsimp only [extractPacked, writePackedMem]
  set p := slotPackShift b d w
  set wIdx := q.val >>> p
  set subIdx := q.val &&& (2 ^ p - 1)
  set wIdx' := q'.val >>> p
  set subIdx' := q'.val &&& (2 ^ p - 1)
  by_cases hw : wIdx' = wIdx
  · have hsub_ne : subIdx' ≠ subIdx := by
      intro hsub
      apply hne
      apply Fin.ext
      rw [← shiftRight_mul_add_and_eq q'.val p, ← shiftRight_mul_add_and_eq q.val p]
      change wIdx' * 2 ^ p + subIdx' = wIdx * 2 ^ p + subIdx
      rw [hw, hsub]
    have hold_lt : getLimb d (mem (arrBase + wIdx)) subIdx < 2 ^ d := getLimb_lt d _ _
    have hdiff_lt : getLimb d (mem (arrBase + wIdx)) subIdx ^^^ val.val < 2 ^ d :=
      Nat.xor_lt_two_pow hold_lt val.isLt
    have haddr : arrBase + wIdx' = arrBase + wIdx := by rw [hw]
    rw [haddr, Function.update_self]
    exact getLimb_xor_shiftLeft_of_ne hdiff_lt hsub_ne
  · rw [Function.update_of_ne (by omega)]

@[simp]
theorem extractPacked_writePackedMem (arrBase b d w : ℕ) (mem : ℕ → ℕ)
    (q : Fin (2 ^ b)) (val : Fin (2 ^ d)) :
    extractPacked arrBase b d w (writePackedMem arrBase b d w mem q val.val) =
      Function.update (extractPacked arrBase b d w mem) q val := by
  ext q'
  by_cases h : q' = q
  · subst h
    rw [extractPacked_writePackedMem_self, Function.update_self]
  · rw [extractPacked_writePackedMem_of_ne _ _ _ _ _ _ _ _ h, Function.update_of_ne h]

/-- Extract the boolean flag at slot `q : Fin (2 ^ b)` from a `1`-bit packed array at `arrBase`. -/
@[expose] def extractBit (arrBase b w : ℕ) (mem : ℕ → ℕ) (q : Fin (2 ^ b)) : Bool :=
  (extractPacked arrBase b 1 w mem q).val == 1

/-- Update the boolean flag at slot `q : Fin (2 ^ b)` in a `1`-bit packed array at `arrBase`. -/
@[expose] def writeBitMem (arrBase b w : ℕ) (mem : ℕ → ℕ) (q : Fin (2 ^ b)) (bval : Bool) :
    ℕ → ℕ :=
  writePackedMem arrBase b 1 w mem q bval.toNat

theorem toNat_lt_two (bval : Bool) : bval.toNat < 2 ^ 1 := by
  cases bval <;> decide

@[simp]
theorem extractBit_writeBitMem (arrBase b w : ℕ) (mem : ℕ → ℕ)
    (q : Fin (2 ^ b)) (bval : Bool) :
    extractBit arrBase b w (writeBitMem arrBase b w mem q bval) =
      Function.update (extractBit arrBase b w mem) q bval := by
  ext q'
  dsimp only [extractBit, writeBitMem]
  let v : Fin (2 ^ 1) := ⟨bval.toNat, toNat_lt_two bval⟩
  have h1 := congrFun (extractPacked_writePackedMem arrBase b 1 w mem q v) q'
  rw [h1]
  by_cases hq : q' = q
  · subst hq
    rw [Function.update_self, Function.update_self]
    cases bval <;> rfl
  · rw [Function.update_of_ne hq, Function.update_of_ne hq]
    rfl

@[simp]
theorem extractPacked_zero (arrBase b d w : ℕ) (q : Fin (2 ^ b)) :
    extractPacked arrBase b d w (fun _ => 0) q = ⟨0, Nat.two_pow_pos d⟩ := by
  apply Fin.ext
  dsimp only [extractPacked]
  exact getLimb_zero d _

@[simp]
theorem extractBit_zero (arrBase b w : ℕ) (q : Fin (2 ^ b)) :
    extractBit arrBase b w (fun _ => 0) q = false := by
  dsimp only [extractBit]
  rw [extractPacked_zero]
  rfl

/-! ## Section 2: Quotient-filter memory layout, `space_le`, and `extractFilterState` -/

/-- Address `base + ReducedKWise.space w w₀ (quotBits w₀ n) (quotBits w₀ n) 5` storing the
multiply-shift remainder seed `γ : RemSeed w₀`. -/
@[expose] def remSeedAddr (base w w₀ n : ℕ) : ℕ :=
  base + ReducedKWise.space w w₀ (quotBits w₀ n) (quotBits w₀ n) 5

/-- Base address of the `isFull` `1`-bit packed array (`packedWords (quotBits w₀ n) 1 w` words). -/
@[expose] def fullBase (base w w₀ n : ℕ) : ℕ :=
  remSeedAddr base w w₀ n + 1

/-- Base address of the `isOcc` `1`-bit packed array (`packedWords (quotBits w₀ n) 1 w` words). -/
@[expose] def occBase (base w w₀ n : ℕ) : ℕ :=
  fullBase base w w₀ n + packedWords (quotBits w₀ n) 1 w

/-- Base address of the `isRunStart` `1`-bit packed array (`packedWords (quotBits w₀ n) 1 w` words).
-/
@[expose] def runBase (base w w₀ n : ℕ) : ℕ :=
  occBase base w w₀ n + packedWords (quotBits w₀ n) 1 w

/-- Base address of the `remAt` `remBits w₀ k`-bit packed array
(`packedWords (quotBits w₀ n) (remBits w₀ k) w` words). -/
@[expose] def remBase (base w w₀ n : ℕ) : ℕ :=
  runBase base w w₀ n + packedWords (quotBits w₀ n) 1 w

/-- Total contiguous memory footprint `space w w₀ n k` of the two-stage quotient filter in words. -/
@[expose] def space (w w₀ n k : ℕ) : ℕ :=
  let b := quotBits w₀ n
  let f := remBits w₀ k
  ReducedKWise.space w w₀ b b 5 + 1 + 3 * packedWords b 1 w + packedWords b f w

theorem remBase_add_packedWords_eq (base w w₀ n k : ℕ) :
    remBase base w w₀ n + packedWords (quotBits w₀ n) (remBits w₀ k) w =
      base + space w w₀ n k := by
  dsimp only [remBase, runBase, occBase, fullBase, remSeedAddr, space]
  ring

/-- Because `effCap w₀ n = min n (2 ^ w₀) ≤ 2 ^ w₀`, the quotient bit-width `quotBits w₀ n` is
always at most `w₀ + 3`. -/
theorem quotBits_le_add_three (w₀ n : ℕ) : quotBits w₀ n ≤ w₀ + 3 := by
  dsimp only [quotBits, tableLog]
  rw [Nat.clog_le_iff_le_pow one_lt_two]
  have h1 : effCap w₀ n ≤ 2 ^ w₀ := min_le_right n (2 ^ w₀)
  have h2 : 8 * effCap w₀ n ≤ 2 ^ (w₀ + 3) := by
    calc 8 * effCap w₀ n ≤ 8 * 2 ^ w₀ := Nat.mul_le_mul_left 8 h1
      _ = 2 ^ (w₀ + 3) := by rw [pow_add]; ring
  have h3 : 8 ≤ 2 ^ (w₀ + 3) := by
    calc 8 = 2 ^ 3 := by decide
      _ ≤ 2 ^ (w₀ + 3) := Nat.pow_le_pow_right two_pos (Nat.le_add_left 3 w₀)
  exact max_le h2 h3

theorem two_pow_quotBits_le_sixteen_mul {w₀ n : ℕ} (hn : 1 ≤ n) :
    2 ^ quotBits w₀ n ≤ 16 * n := by
  have h1 : 2 ^ quotBits w₀ n ≤ 16 * max (effCap w₀ n) 1 :=
    tableSize_le_sixteen_mul (effCap w₀ n)
  have h2 : max (effCap w₀ n) 1 ≤ n := max_le (min_le_left n (2 ^ w₀)) hn
  exact h1.trans (Nat.mul_le_mul_left 16 h2)

theorem remBits_pos {w₀ k : ℕ} (hw₀ : 0 < w₀) : 0 < remBits w₀ k := by
  dsimp only [remBits]
  omega

theorem remBits_le_w₀ (w₀ k : ℕ) : remBits w₀ k ≤ w₀ :=
  min_le_left w₀ (k + 1)

theorem remBits_le_two_mul {w₀ k : ℕ} (hk : 1 ≤ k) : remBits w₀ k ≤ 2 * k := by
  have h1 : remBits w₀ k ≤ k + 1 := min_le_right w₀ (k + 1)
  omega

/-- **Compact space bound**: for all `n ≥ 1`, `k ≥ 1`, `0 < w₀`, `2 * w₀ ≤ w`, and
`quotBits w₀ n ≤ w`, the total Word-RAM footprint `space w w₀ n k` is at most
`640 * ((n * k + w - 1) / w + 1)` words. -/
theorem space_le {w w₀ n k : ℕ} (hw₀ : 0 < w₀) (hw : 2 * w₀ ≤ w) (hb_w : quotBits w₀ n ≤ w)
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    space w w₀ n k ≤ 640 * ((n * k + w - 1) / w + 1) := by
  set b := quotBits w₀ n
  set f := remBits w₀ k
  have hw₀_le : w₀ ≤ w := by omega
  have hw2 : 2 ≤ w := by omega
  have hb3 : b ≤ 3 * b := by omega
  have hf_pos : 0 < f := remBits_pos hw₀
  have h2f_le : 2 * f ≤ w := by have := remBits_le_w₀ w₀ k; omega
  have hpow_b : 2 ^ b ≤ 16 * n := two_pow_quotBits_le_sixteen_mul hn
  have hmax_b2 : max 8 (2 ^ (b / 2)) ≤ 16 * n := by
    have hle : 2 ^ (b / 2) ≤ 2 ^ b := Nat.pow_le_pow_right two_pos (Nat.div_le_self b 2)
    exact max_le (by omega) (hle.trans hpow_b)
  have hsp_kwise : ReducedKWise.space w w₀ b b 5 ≤ 272 + (32 * (n * k)) / w := by
    have h1 := ReducedKWise.space_le (k := 5) hw₀_le hb3 hb_w hw2
    have h2 : 2 * max 8 (2 ^ (b / 2)) ≤ 32 * (n * k) := by
      calc 2 * max 8 (2 ^ (b / 2)) ≤ 2 * (16 * n) := Nat.mul_le_mul_left 2 hmax_b2
        _ = 32 * (n * 1) := by ring
        _ ≤ 32 * (n * k) := Nat.mul_le_mul_left 32 (Nat.mul_le_mul_left n hk)
    have h3 : 2 * max 8 (2 ^ (b / 2)) / w ≤ (32 * (n * k)) / w := Nat.div_le_div_right h2
    omega
  have hbit_words : packedWords b 1 w ≤ (64 * (n * k)) / w + 1 := by
    have h1 := packedWords_le (b := b) (d := 1) (w := w) one_pos hw2
    have h2 : 4 * (2 ^ b * 1) ≤ 64 * (n * k) := by
      calc 4 * (2 ^ b * 1) ≤ 4 * (16 * n) := by omega
        _ = 64 * (n * 1) := by ring
        _ ≤ 64 * (n * k) := Nat.mul_le_mul_left 64 (Nat.mul_le_mul_left n hk)
    exact h1.trans (Nat.add_le_add_right (Nat.div_le_div_right h2) 1)
  have hrem_words : packedWords b f w ≤ (128 * (n * k)) / w + 1 := by
    have h1 := packedWords_le (b := b) (d := f) (w := w) hf_pos h2f_le
    have hf2k : f ≤ 2 * k := remBits_le_two_mul hk
    have h2 : 4 * (2 ^ b * f) ≤ 128 * (n * k) := by
      calc 4 * (2 ^ b * f) ≤ 4 * ((16 * n) * (2 * k)) :=
            Nat.mul_le_mul_left 4 (Nat.mul_le_mul hpow_b hf2k)
        _ = 128 * (n * k) := by ring
    exact h1.trans (Nat.add_le_add_right (Nat.div_le_div_right h2) 1)
  have hdiv_bound (c x : ℕ) : (c * x) / w ≤ c * (x / w) + c := by
    have h1 := Nat.div_add_mod x w
    have h2 : x % w < w := Nat.mod_lt x (by omega)
    have h3 : c * x < w * (c * (x / w) + c + 1) := by
      have h4 : c * x ≤ c * (w * (x / w)) + c * w := by
        calc c * x = c * (w * (x / w) + x % w) := by conv_lhs => rw [← h1]
          _ = c * (w * (x / w)) + c * (x % w) := by ring
          _ ≤ c * (w * (x / w)) + c * w := Nat.add_le_add_left (Nat.mul_le_mul_left c h2.le) _
      have h5 : c * (w * (x / w)) + c * w + w = w * (c * (x / w) + c + 1) := by ring
      omega
    exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul h3)
  have h32 := hdiv_bound 32 (n * k)
  have h64 := hdiv_bound 64 (n * k)
  have h128 := hdiv_bound 128 (n * k)
  have hceil : (n * k) / w ≤ (n * k + w - 1) / w :=
    Nat.div_le_div_right (by omega)
  generalize (n * k) / w = qdiv at h32 h64 h128 hceil
  generalize (n * k + w - 1) / w = cdiv at hceil ⊢
  change ReducedKWise.space w w₀ b b 5 + 1 + 3 * packedWords b 1 w + packedWords b f w ≤
    640 * (cdiv + 1)
  omega

/-- Extract the remainder seed `γ : RemSeed w₀` from `mem (remSeedAddr base w w₀ n)`. -/
@[expose] def extractRemSeed (base w w₀ n : ℕ) (mem : ℕ → ℕ) : RemSeed w₀ :=
  Tabulation.extractWord (w₀ - 1) (mem (remSeedAddr base w w₀ n))

/-- Extract the full seed `(θ, γ) : FilterSeed w₀ n` from memory at `base`. -/
@[expose] def extractFilterSeed (base w w₀ n : ℕ) (mem : ℕ → ℕ) : FilterSeed w₀ n :=
  (ReducedKWise.extractSeed base w₀ (quotBits w₀ n) (quotBits w₀ n) 5 mem,
   extractRemSeed base w w₀ n mem)

/-- Extract the pure `FilterState (quotBits w₀ n) (remBits w₀ k)` from the 4 bit-packed slot arrays
in `mem`. -/
@[expose] def extractFilterState (base w w₀ n k : ℕ) (mem : ℕ → ℕ) :
    FilterState (quotBits w₀ n) (remBits w₀ k) where
  isFull := extractBit (fullBase base w w₀ n) (quotBits w₀ n) w mem
  isOcc := extractBit (occBase base w w₀ n) (quotBits w₀ n) w mem
  isRunStart := extractBit (runBase base w w₀ n) (quotBits w₀ n) w mem
  remAt := extractPacked (remBase base w w₀ n) (quotBits w₀ n) (remBits w₀ k) w mem

theorem extractFilterState_congr {base w w₀ n k : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (h : ∀ a, fullBase base w w₀ n ≤ a → a < base + space w w₀ n k → mem₁ a = mem₂ a) :
    extractFilterState base w w₀ n k mem₁ = extractFilterState base w w₀ n k mem₂ := by
  have hfull : extractBit (fullBase base w w₀ n) (quotBits w₀ n) w mem₁ =
      extractBit (fullBase base w w₀ n) (quotBits w₀ n) w mem₂ := by
    ext q
    dsimp only [extractBit, extractPacked]
    have hlt := shiftRight_lt_packedWords (quotBits w₀ n) 1 w q
    generalize q.val >>> slotPackShift (quotBits w₀ n) 1 w = wIdx at hlt ⊢
    rw [h (fullBase base w w₀ n + wIdx) (by omega)
      (by dsimp only [space, fullBase, remSeedAddr]; omega)]
  have hocc : extractBit (occBase base w w₀ n) (quotBits w₀ n) w mem₁ =
      extractBit (occBase base w w₀ n) (quotBits w₀ n) w mem₂ := by
    ext q
    dsimp only [extractBit, extractPacked]
    have hlt := shiftRight_lt_packedWords (quotBits w₀ n) 1 w q
    generalize q.val >>> slotPackShift (quotBits w₀ n) 1 w = wIdx at hlt ⊢
    rw [h (occBase base w w₀ n + wIdx)
      (by dsimp only [occBase]; omega)
      (by dsimp only [space, occBase, fullBase, remSeedAddr]; omega)]
  have hrun : extractBit (runBase base w w₀ n) (quotBits w₀ n) w mem₁ =
      extractBit (runBase base w w₀ n) (quotBits w₀ n) w mem₂ := by
    ext q
    dsimp only [extractBit, extractPacked]
    have hlt := shiftRight_lt_packedWords (quotBits w₀ n) 1 w q
    generalize q.val >>> slotPackShift (quotBits w₀ n) 1 w = wIdx at hlt ⊢
    rw [h (runBase base w w₀ n + wIdx)
      (by dsimp only [runBase, occBase]; omega)
      (by dsimp only [space, runBase, occBase, fullBase, remSeedAddr]; omega)]
  have hrem : extractPacked (remBase base w w₀ n) (quotBits w₀ n) (remBits w₀ k) w mem₁ =
      extractPacked (remBase base w w₀ n) (quotBits w₀ n) (remBits w₀ k) w mem₂ := by
    ext q
    dsimp only [extractPacked]
    have hlt := shiftRight_lt_packedWords (quotBits w₀ n) (remBits w₀ k) w q
    generalize q.val >>> slotPackShift (quotBits w₀ n) (remBits w₀ k) w = wIdx at hlt ⊢
    rw [h (remBase base w w₀ n + wIdx)
      (by dsimp only [remBase, runBase, occBase]; omega)
      (by rw [← remBase_add_packedWords_eq]; omega)]
  dsimp only [extractFilterState]
  rw [hfull, hocc, hrun, hrem]

/-- Zeroed slot arrays `[fullBase, base + space)` represent `FilterState.empty`. -/
theorem extractFilterState_of_zero {base w w₀ n k : ℕ} {mem : ℕ → ℕ}
    (hz : ∀ a, fullBase base w w₀ n ≤ a → a < base + space w w₀ n k → mem a = 0) :
    extractFilterState base w w₀ n k mem =
      FilterState.empty (quotBits w₀ n) (remBits w₀ k) := by
  rw [extractFilterState_congr hz]
  dsimp only [extractFilterState, FilterState.empty]
  congr <;> funext q <;> simp

@[simp]
theorem extractFilterState_writeFull (base w w₀ n k : ℕ) (mem : ℕ → ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (bval : Bool) :
    extractFilterState base w w₀ n k
      (writeBitMem (fullBase base w w₀ n) (quotBits w₀ n) w mem q bval) =
      (extractFilterState base w w₀ n k mem).setFull q bval := by
  have hfull : extractBit (fullBase base w w₀ n) (quotBits w₀ n) w
      (writeBitMem (fullBase base w w₀ n) (quotBits w₀ n) w mem q bval) =
      Function.update (extractBit (fullBase base w w₀ n) (quotBits w₀ n) w mem) q bval :=
    extractBit_writeBitMem _ _ _ _ _ _
  have hocc : extractBit (occBase base w w₀ n) (quotBits w₀ n) w
      (writeBitMem (fullBase base w w₀ n) (quotBits w₀ n) w mem q bval) =
      extractBit (occBase base w w₀ n) (quotBits w₀ n) w mem := by
    ext q'
    dsimp only [extractBit, extractPacked, writeBitMem]
    rw [writePackedMem_outside]
    generalize q'.val >>> slotPackShift (quotBits w₀ n) 1 w = wIdx
    dsimp only [occBase]
    omega
  have hrun : extractBit (runBase base w w₀ n) (quotBits w₀ n) w
      (writeBitMem (fullBase base w w₀ n) (quotBits w₀ n) w mem q bval) =
      extractBit (runBase base w w₀ n) (quotBits w₀ n) w mem := by
    ext q'
    dsimp only [extractBit, extractPacked, writeBitMem]
    rw [writePackedMem_outside]
    generalize q'.val >>> slotPackShift (quotBits w₀ n) 1 w = wIdx
    dsimp only [runBase, occBase]
    omega
  have hrem : extractPacked (remBase base w w₀ n) (quotBits w₀ n) (remBits w₀ k) w
      (writeBitMem (fullBase base w w₀ n) (quotBits w₀ n) w mem q bval) =
      extractPacked (remBase base w w₀ n) (quotBits w₀ n) (remBits w₀ k) w mem := by
    ext q'
    dsimp only [extractPacked, writeBitMem]
    rw [writePackedMem_outside]
    generalize q'.val >>> slotPackShift (quotBits w₀ n) (remBits w₀ k) w = wIdx
    dsimp only [remBase, runBase, occBase]
    omega
  dsimp only [extractFilterState, FilterState.setFull]
  rw [hfull, hocc, hrun, hrem]

@[simp]
theorem extractFilterState_writeOcc (base w w₀ n k : ℕ) (mem : ℕ → ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (bval : Bool) :
    extractFilterState base w w₀ n k
      (writeBitMem (occBase base w w₀ n) (quotBits w₀ n) w mem q bval) =
      (extractFilterState base w w₀ n k mem).setOcc q bval := by
  have hfull : extractBit (fullBase base w w₀ n) (quotBits w₀ n) w
      (writeBitMem (occBase base w w₀ n) (quotBits w₀ n) w mem q bval) =
      extractBit (fullBase base w w₀ n) (quotBits w₀ n) w mem := by
    ext q'
    dsimp only [extractBit, extractPacked, writeBitMem]
    have hlt := shiftRight_lt_packedWords (quotBits w₀ n) 1 w q'
    rw [writePackedMem_outside]
    generalize q'.val >>> slotPackShift (quotBits w₀ n) 1 w = wIdx at hlt ⊢
    dsimp only [occBase]
    omega
  have hocc : extractBit (occBase base w w₀ n) (quotBits w₀ n) w
      (writeBitMem (occBase base w w₀ n) (quotBits w₀ n) w mem q bval) =
      Function.update (extractBit (occBase base w w₀ n) (quotBits w₀ n) w mem) q bval :=
    extractBit_writeBitMem _ _ _ _ _ _
  have hrun : extractBit (runBase base w w₀ n) (quotBits w₀ n) w
      (writeBitMem (occBase base w w₀ n) (quotBits w₀ n) w mem q bval) =
      extractBit (runBase base w w₀ n) (quotBits w₀ n) w mem := by
    ext q'
    dsimp only [extractBit, extractPacked, writeBitMem]
    rw [writePackedMem_outside]
    generalize q'.val >>> slotPackShift (quotBits w₀ n) 1 w = wIdx
    dsimp only [runBase]
    omega
  have hrem : extractPacked (remBase base w w₀ n) (quotBits w₀ n) (remBits w₀ k) w
      (writeBitMem (occBase base w w₀ n) (quotBits w₀ n) w mem q bval) =
      extractPacked (remBase base w w₀ n) (quotBits w₀ n) (remBits w₀ k) w mem := by
    ext q'
    dsimp only [extractPacked, writeBitMem]
    rw [writePackedMem_outside]
    generalize q'.val >>> slotPackShift (quotBits w₀ n) (remBits w₀ k) w = wIdx
    dsimp only [remBase, runBase]
    omega
  dsimp only [extractFilterState, FilterState.setOcc]
  rw [hfull, hocc, hrun, hrem]

@[simp]
theorem extractFilterState_writeRunStart (base w w₀ n k : ℕ) (mem : ℕ → ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (bval : Bool) :
    extractFilterState base w w₀ n k
      (writeBitMem (runBase base w w₀ n) (quotBits w₀ n) w mem q bval) =
      (extractFilterState base w w₀ n k mem).setRunStart q bval := by
  have hfull : extractBit (fullBase base w w₀ n) (quotBits w₀ n) w
      (writeBitMem (runBase base w w₀ n) (quotBits w₀ n) w mem q bval) =
      extractBit (fullBase base w w₀ n) (quotBits w₀ n) w mem := by
    ext q'
    dsimp only [extractBit, extractPacked, writeBitMem]
    have hlt := shiftRight_lt_packedWords (quotBits w₀ n) 1 w q'
    rw [writePackedMem_outside]
    generalize q'.val >>> slotPackShift (quotBits w₀ n) 1 w = wIdx at hlt ⊢
    dsimp only [runBase, occBase]
    omega
  have hocc : extractBit (occBase base w w₀ n) (quotBits w₀ n) w
      (writeBitMem (runBase base w w₀ n) (quotBits w₀ n) w mem q bval) =
      extractBit (occBase base w w₀ n) (quotBits w₀ n) w mem := by
    ext q'
    dsimp only [extractBit, extractPacked, writeBitMem]
    have hlt := shiftRight_lt_packedWords (quotBits w₀ n) 1 w q'
    rw [writePackedMem_outside]
    generalize q'.val >>> slotPackShift (quotBits w₀ n) 1 w = wIdx at hlt ⊢
    dsimp only [runBase]
    omega
  have hrun : extractBit (runBase base w w₀ n) (quotBits w₀ n) w
      (writeBitMem (runBase base w w₀ n) (quotBits w₀ n) w mem q bval) =
      Function.update (extractBit (runBase base w w₀ n) (quotBits w₀ n) w mem) q bval :=
    extractBit_writeBitMem _ _ _ _ _ _
  have hrem : extractPacked (remBase base w w₀ n) (quotBits w₀ n) (remBits w₀ k) w
      (writeBitMem (runBase base w w₀ n) (quotBits w₀ n) w mem q bval) =
      extractPacked (remBase base w w₀ n) (quotBits w₀ n) (remBits w₀ k) w mem := by
    ext q'
    dsimp only [extractPacked, writeBitMem]
    rw [writePackedMem_outside]
    generalize q'.val >>> slotPackShift (quotBits w₀ n) (remBits w₀ k) w = wIdx
    dsimp only [remBase]
    omega
  dsimp only [extractFilterState, FilterState.setRunStart]
  rw [hfull, hocc, hrun, hrem]

@[simp]
theorem extractFilterState_writeRem (base w w₀ n k : ℕ) (mem : ℕ → ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) :
    extractFilterState base w w₀ n k
      (writePackedMem (remBase base w w₀ n) (quotBits w₀ n) (remBits w₀ k) w mem q r.val) =
      (extractFilterState base w w₀ n k mem).setRem q r := by
  have hfull : extractBit (fullBase base w w₀ n) (quotBits w₀ n) w
      (writePackedMem (remBase base w w₀ n) (quotBits w₀ n) (remBits w₀ k) w mem q r.val) =
      extractBit (fullBase base w w₀ n) (quotBits w₀ n) w mem := by
    ext q'
    dsimp only [extractBit, extractPacked]
    have hlt := shiftRight_lt_packedWords (quotBits w₀ n) 1 w q'
    rw [writePackedMem_outside]
    generalize q'.val >>> slotPackShift (quotBits w₀ n) 1 w = wIdx at hlt ⊢
    dsimp only [remBase, runBase, occBase]
    omega
  have hocc : extractBit (occBase base w w₀ n) (quotBits w₀ n) w
      (writePackedMem (remBase base w w₀ n) (quotBits w₀ n) (remBits w₀ k) w mem q r.val) =
      extractBit (occBase base w w₀ n) (quotBits w₀ n) w mem := by
    ext q'
    dsimp only [extractBit, extractPacked]
    have hlt := shiftRight_lt_packedWords (quotBits w₀ n) 1 w q'
    rw [writePackedMem_outside]
    generalize q'.val >>> slotPackShift (quotBits w₀ n) 1 w = wIdx at hlt ⊢
    dsimp only [remBase, runBase]
    omega
  have hrun : extractBit (runBase base w w₀ n) (quotBits w₀ n) w
      (writePackedMem (remBase base w w₀ n) (quotBits w₀ n) (remBits w₀ k) w mem q r.val) =
      extractBit (runBase base w w₀ n) (quotBits w₀ n) w mem := by
    ext q'
    dsimp only [extractBit, extractPacked]
    have hlt := shiftRight_lt_packedWords (quotBits w₀ n) 1 w q'
    rw [writePackedMem_outside]
    generalize q'.val >>> slotPackShift (quotBits w₀ n) 1 w = wIdx at hlt ⊢
    dsimp only [remBase]
    omega
  have hrem : extractPacked (remBase base w w₀ n) (quotBits w₀ n) (remBits w₀ k) w
      (writePackedMem (remBase base w w₀ n) (quotBits w₀ n) (remBits w₀ k) w mem q r.val) =
      Function.update
        (extractPacked (remBase base w w₀ n) (quotBits w₀ n) (remBits w₀ k) w mem) q r :=
    extractPacked_writePackedMem _ _ _ _ _ _ _
  dsimp only [extractFilterState, FilterState.setRem]
  rw [hfull, hocc, hrun, hrem]

/-! ## Section 3: Slot modular arithmetic and memory layout offsets -/

/-- Bitwise identity `(o.val + d) &&& (2 ^ b - 1) = (probeSlot b o d).val`. -/
theorem add_and_eq_probeSlot_val {b : ℕ} (o : Fin (2 ^ b)) (d : ℕ) :
    (o.val + d) &&& (2 ^ b - 1) = (probeSlot b o d).val := by
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rfl

/-- Bitwise identity `(q.val + 2 ^ b - a) &&& (2 ^ b - 1) = (backSlot b q a).val` for `a ≤ 2 ^ b`.
-/
theorem add_sub_and_eq_backSlot_val {b : ℕ} (q : Fin (2 ^ b)) {a : ℕ} (ha : a ≤ 2 ^ b) :
    (q.val + 2 ^ b - a) &&& (2 ^ b - 1) = (backSlot b q a).val := by
  rw [Nat.and_two_pow_sub_one_eq_mod]
  change (q.val + 2 ^ b - a) % 2 ^ b = (q.val + 2 ^ b * (a + 1) - a) % 2 ^ b
  have h1 : q.val + 2 ^ b * (a + 1) - a = (q.val + 2 ^ b - a) + a * 2 ^ b := by
    have : 2 ^ b * (a + 1) = 2 ^ b + a * 2 ^ b := by ring
    omega
  rw [h1, Nat.add_mul_mod_self_right]

theorem extractPacked_one_val_eq_toNat (arrBase b w : ℕ) (mem : ℕ → ℕ) (q : Fin (2 ^ b)) :
    (extractPacked arrBase b 1 w mem q).val = (extractBit arrBase b w mem q).toNat := by
  dsimp only [extractBit]
  have hlt : (extractPacked arrBase b 1 w mem q).val < 2 := (extractPacked arrBase b 1 w mem q).isLt
  set v := (extractPacked arrBase b 1 w mem q).val
  interval_cases v <;> rfl

/-- Offset of `remSeedAddr` from `base`. -/
@[expose] def remSeedOff (w w₀ n : ℕ) : ℕ :=
  ReducedKWise.space w w₀ (quotBits w₀ n) (quotBits w₀ n) 5

/-- Offset of `fullBase` from `base`. -/
@[expose] def fullOff (w w₀ n : ℕ) : ℕ :=
  remSeedOff w w₀ n + 1

/-- Offset of `occBase` from `base`. -/
@[expose] def occOff (w w₀ n : ℕ) : ℕ :=
  fullOff w w₀ n + packedWords (quotBits w₀ n) 1 w

/-- Offset of `runBase` from `base`. -/
@[expose] def runOff (w w₀ n : ℕ) : ℕ :=
  occOff w w₀ n + packedWords (quotBits w₀ n) 1 w

/-- Offset of `remBase` from `base`. -/
@[expose] def remOff (w w₀ n : ℕ) : ℕ :=
  runOff w w₀ n + packedWords (quotBits w₀ n) 1 w

theorem base_add_remSeedOff (base w w₀ n : ℕ) :
    base + remSeedOff w w₀ n = remSeedAddr base w w₀ n := rfl

theorem base_add_fullOff (base w w₀ n : ℕ) :
    base + fullOff w w₀ n = fullBase base w w₀ n := by
  dsimp only [fullOff, remSeedOff, fullBase, remSeedAddr]; ring

theorem base_add_occOff (base w w₀ n : ℕ) :
    base + occOff w w₀ n = occBase base w w₀ n := by
  dsimp only [occOff, fullOff, remSeedOff, occBase, fullBase, remSeedAddr]; ring

theorem base_add_runOff (base w w₀ n : ℕ) :
    base + runOff w w₀ n = runBase base w w₀ n := by
  dsimp only [runOff, occOff, fullOff, remSeedOff, runBase, occBase, fullBase, remSeedAddr]; ring

theorem base_add_remOff (base w w₀ n : ℕ) :
    base + remOff w w₀ n = remBase base w w₀ n := by
  dsimp only [remOff, runOff, occOff, fullOff, remSeedOff, remBase, runBase, occBase,
    fullBase, remSeedAddr]
  ring

end Cslib.DataStructure.ApproximateMembership.QuotientFilter
