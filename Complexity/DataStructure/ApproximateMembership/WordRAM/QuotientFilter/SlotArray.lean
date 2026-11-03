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
# Bit-Packed Slot Arrays and Primitives for the Word-RAM Quotient Filter

This file defines the compact bit-packed memory layout and constant-time Word-RAM slot-access
primitives for the two-stage quotient filter:

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
3. **Constant-time Word-RAM primitives on `Data 248`**:
   Provides deterministic `ExecWithin` certificates for `probeSlotCode`, `backSlotCode`,
   `readPackedCode`, `writePackedCode`, `remInitCode`, and `remEvalCode`.
-/

public section

namespace Cslib.DataStructure.ApproximateMembership.QuotientFilter

open Finset
open Cslib.WordRAM Cslib.WordRAM.ExactLog
open Cslib.Probability
open Cslib.DataStructure.WordRAM.Randomized
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

/-! ## Section 3: Word-RAM primitive instructions on `Data 248` -/

/-- Register count `248` for the Word-RAM quotient filter (`0..239` shared with `ReducedKWise`,
`240..247` dedicated to `SubroutineCode` control and operation tags). -/
abbrev rQF : ℕ := 248

/-- Embedding `Fin 240 → Fin 248` for `ReducedKWise` subroutines. -/
@[expose] def kwiseMap : Fin 240 → Fin rQF :=
  Fin.castLE (by decide)

theorem injective_kwiseMap : Function.Injective kwiseMap :=
  Fin.castLE_injective (by decide)

theorem extend_kwiseMap_regs {y : Data 240} {x : Data rQF} {j : Fin rQF} (hj : 240 ≤ j.val) :
    (y.extend kwiseMap x).regs j = x.regs j := by
  change Function.extend kwiseMap y.regs x.regs j = x.regs j
  apply Function.extend_apply'
  rintro ⟨i, rfl⟩
  have := i.isLt
  dsimp only [kwiseMap, Fin.val_castLE] at hj
  omega

private theorem exec_exactBin {w : ℕ} {op : BinOp} {d s1 s2 : Fin rQF} {x : Data rQF} {v : ℕ}
    (hev : op.evalExact (x.regs s1) (x.regs s2) = some v) (hfit : Fits w v) :
    Exec w (.op (.exactBin op d s1 s2) : Code .exact rQF) x (x.set d v) 1 := by
  apply Exec.op
  rw [Op.eval_exactBin, hev]
  exact Data.put_of_fits hfit

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

/-- Word-RAM snippet computing `(probeSlot b o d).val = (o.val + d) &&& (2 ^ b - 1)` into `dstReg`
from `baseSlotReg` (`o.val`) and `offReg` (`d`), using scratch register `30` in `3` instructions. -/
@[expose] def probeSlotCode (b : ℕ) (baseSlotReg offReg dstReg : Fin rQF) : Code .exact rQF :=
  .seq (.op (.const 30 (2 ^ b - 1)))
  (.seq (.op (.exactBin .add dstReg baseSlotReg offReg))
        (.op (.exactBin .and dstReg dstReg 30)))

theorem probeSlotCode_exec {w b : ℕ} (hb_lt : b < w)
    {baseSlotReg offReg dstReg : Fin rQF}
    (hb_ne : baseSlotReg ≠ 30) (hoff_ne : offReg ≠ 30) (hdst_ne : dstReg ≠ 30)
    (o : Fin (2 ^ b)) {d : ℕ} (hd : d ≤ 2 ^ b) {x : Data rQF}
    (ho : x.regs baseSlotReg = o.val) (hoff : x.regs offReg = d) :
    ∃ y : Data rQF,
      Exec w (probeSlotCode b baseSlotReg offReg dstReg) x y 3 ∧
      y.mem = x.mem ∧
      y.regs dstReg = (probeSlot b o d).val ∧
      ∀ j : Fin rQF, j ≠ dstReg → j ≠ 30 → y.regs j = x.regs j := by
  have hpow_b : 2 ^ b < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hb_lt
  have hfit_mask : Fits w (2 ^ b - 1) := by
    change 2 ^ b - 1 < 2 ^ w
    omega
  have hfit_sum : Fits w (o.val + d) := by
    change o.val + d < 2 ^ w
    have h1 : o.val + d < 2 ^ (b + 1) := by
      rw [pow_succ']
      have := o.isLt
      omega
    have h2 : 2 ^ (b + 1) ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hb_lt
    omega
  have hfit_out : Fits w ((probeSlot b o d).val) := (probeSlot b o d).isLt.trans hpow_b
  set s1 := x.set 30 (2 ^ b - 1)
  have e1 : Exec w (.op (.const 30 (2 ^ b - 1)) : Code .exact rQF) x s1 1 :=
    Exec.const hfit_mask
  set s2 := s1.set dstReg (o.val + d)
  have e2 : Exec w (.op (.exactBin .add dstReg baseSlotReg offReg) : Code .exact rQF) s1 s2 1 :=
    exec_exactBin (by simp [s1, hb_ne, hoff_ne, ho, hoff]) hfit_sum
  set s3 := s2.set dstReg (probeSlot b o d).val
  have e3 : Exec w (.op (.exactBin .and dstReg dstReg 30) : Code .exact rQF) s2 s3 1 :=
    exec_exactBin (by simp [s2, s1, hdst_ne.symm]; rfl) hfit_out
  refine ⟨s3, e1.seq (e2.seq e3), rfl, by simp [s3], fun j hj1 hj2 => ?_⟩
  simp [s3, s2, s1, hj1, hj2]

/-- Word-RAM snippet computing `(backSlot b q a).val = (q.val + 2 ^ b - a) &&& (2 ^ b - 1)` into
`dstReg` from `slotReg` (`q.val`) and `offReg` (`a ≤ 2 ^ b`), using scratch registers `30, 31` in
`5` instructions. -/
@[expose] def backSlotCode (b : ℕ) (slotReg offReg dstReg : Fin rQF) : Code .exact rQF :=
  .seq (.op (.const 30 (2 ^ b)))
  (.seq (.op (.exactBin .add 30 slotReg 30))
  (.seq (.op (.exactBin .sub 30 30 offReg))
  (.seq (.op (.const 31 (2 ^ b - 1)))
        (.op (.exactBin .and dstReg 30 31)))))

theorem backSlotCode_exec {w b : ℕ} (hb_lt : b < w)
    {slotReg offReg dstReg : Fin rQF}
    (hs_ne30 : slotReg ≠ 30) (hoff_ne30 : offReg ≠ 30)
    (q : Fin (2 ^ b)) {a : ℕ} (ha : a ≤ 2 ^ b) {x : Data rQF}
    (hq : x.regs slotReg = q.val) (hoff : x.regs offReg = a) :
    ∃ y : Data rQF,
      Exec w (backSlotCode b slotReg offReg dstReg) x y 5 ∧
      y.mem = x.mem ∧
      y.regs dstReg = (backSlot b q a).val ∧
      ∀ j : Fin rQF, j ≠ dstReg → j ≠ 30 → j ≠ 31 → y.regs j = x.regs j := by
  have hpow_b : 2 ^ b < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hb_lt
  have hfit_pow : Fits w (2 ^ b) := hpow_b
  have hfit_mask : Fits w (2 ^ b - 1) := by change 2 ^ b - 1 < 2 ^ w; omega
  have hfit_sum : Fits w (q.val + 2 ^ b) := by
    change q.val + 2 ^ b < 2 ^ w
    have h1 : q.val + 2 ^ b < 2 ^ (b + 1) := by
      rw [pow_succ']
      have := q.isLt
      omega
    have h2 : 2 ^ (b + 1) ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hb_lt
    omega
  have hfit_sub : Fits w (q.val + 2 ^ b - a) := hfit_sum.of_le (Nat.sub_le _ _)
  have hfit_out : Fits w (backSlot b q a).val := (backSlot b q a).isLt.trans hpow_b
  set s1 := x.set 30 (2 ^ b)
  have e1 : Exec w (.op (.const 30 (2 ^ b)) : Code .exact rQF) x s1 1 := Exec.const hfit_pow
  set s2 := s1.set 30 (q.val + 2 ^ b)
  have e2 : Exec w (.op (.exactBin .add 30 slotReg 30) : Code .exact rQF) s1 s2 1 :=
    exec_exactBin (by simp [s1, hs_ne30, hq]) hfit_sum
  set s3 := s2.set 30 (q.val + 2 ^ b - a)
  have e3 : Exec w (.op (.exactBin .sub 30 30 offReg) : Code .exact rQF) s2 s3 1 :=
    exec_exactBin (by simp [s2, s1, hoff_ne30, hoff]; omega) hfit_sub
  set s4 := s3.set 31 (2 ^ b - 1)
  have e4 : Exec w (.op (.const 31 (2 ^ b - 1)) : Code .exact rQF) s3 s4 1 :=
    Exec.const hfit_mask
  set s5 := s4.set dstReg (backSlot b q a).val
  have e5 : Exec w (.op (.exactBin .and dstReg 30 31) : Code .exact rQF) s4 s5 1 :=
    exec_exactBin (by simp +decide [s4, s3, add_sub_and_eq_backSlot_val q ha]) hfit_out
  refine ⟨s5, e1.seq (e2.seq (e3.seq (e4.seq e5))), rfl, by simp [s5], fun j hj1 hj2 hj3 => ?_⟩
  simp [s5, s4, s3, s2, s1, hj1, hj2, hj3]

/-- Word-RAM program reading `(extractPacked (base + off) b d w x.mem q).val` into `dstReg` from
`idxReg` (`q.val`) and `reg 0` (`base`), using scratch registers `30..34` in `11` instructions. -/
@[expose] def readPackedCode (off b d w : ℕ) (idxReg dstReg : Fin rQF) : Code .exact rQF :=
  let p := slotPackShift b d w
  .seq (.op (.const 30 off))
  (.seq (.op (.exactBin .add 30 0 30))
  (.seq (.op (.const 31 p))
  (.seq (.op (.exactBin .shiftRight 32 idxReg 31))
  (.seq (.op (.exactBin .add 30 30 32))
  (.seq (.op (.load 33 30))
  (.seq (.op (.const 31 (2 ^ p - 1)))
  (.seq (.op (.exactBin .and 32 idxReg 31))
  (.seq (.op (.const 31 d))
  (.seq (.op (.exactBin .mul 32 32 31))
  (.seq (.op (.exactBin .shiftRight 33 33 32))
  (.seq (.op (.const 34 (2 ^ d - 1)))
        (.op (.exactBin .and dstReg 33 34)))))))))))))

theorem readPackedCode_exec {base off b d w : ℕ}
    (hb_lt : b < w) (hd : 0 < d) (hdw : 2 * d ≤ w)
    (hfit_end : Fits w (base + off + packedWords b d w))
    {idxReg dstReg : Fin rQF}
    (hidx_lt : idxReg.val < 30)
    (q : Fin (2 ^ b)) {x : Data rQF}
    (hx : x.Bounded w) (h0 : x.regs 0 = base) (hidx : x.regs idxReg = q.val) :
    ∃ y : Data rQF,
      Exec w (readPackedCode off b d w idxReg dstReg) x y 13 ∧
      y.mem = x.mem ∧
      y.regs dstReg = (extractPacked (base + off) b d w x.mem q).val ∧
      ∀ j : Fin rQF, j ≠ dstReg → (j.val < 30 ∨ 35 ≤ j.val) → y.regs j = x.regs j := by
  set p := slotPackShift b d w
  set wIdx := q.val >>> p
  set subIdx := q.val &&& (2 ^ p - 1)
  set sh := subIdx * d
  set wordVal := x.mem (base + off + wIdx)
  have hpow_b : 2 ^ b < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hb_lt
  have hp_le : p ≤ b := slotPackShift_le b d w
  have hpack_lt : 2 ^ p * d < w := two_pow_slotPackShift_mul_lt hd hdw
  have hwIdx_lt : wIdx < packedWords b d w := shiftRight_lt_packedWords b d w q
  have hsub_lt : subIdx < 2 ^ p := and_two_pow_slotPackShift_lt b d w q
  have hsh_lt : sh < w := by
    calc subIdx * d < 2 ^ p * d := Nat.mul_lt_mul_of_pos_right hsub_lt hd
      _ < w := hpack_lt
  have hfit_off : Fits w off := hfit_end.of_le (by omega)
  have hfit_arr : Fits w (base + off) := hfit_end.of_le (by omega)
  have hfit_p : Fits w p := (hp_le.trans_lt hb_lt).trans Nat.lt_two_pow_self
  have hfit_wIdx : Fits w wIdx := hfit_end.of_le (by omega)
  have hfit_addr : Fits w (base + off + wIdx) := hfit_end.of_le (by omega)
  have hfit_pmask : Fits w (2 ^ p - 1) := by
    have : 2 ^ p ≤ 2 ^ b := Nat.pow_le_pow_right two_pos hp_le
    change 2 ^ p - 1 < 2 ^ w
    omega
  have hfit_sub : Fits w subIdx := by
    have : 2 ^ p ≤ 2 ^ b := Nat.pow_le_pow_right two_pos hp_le
    change subIdx < 2 ^ w
    omega
  have hfit_d : Fits w d := (by omega : d < w).trans Nat.lt_two_pow_self
  have hfit_sh : Fits w sh := hsh_lt.trans Nat.lt_two_pow_self
  have hword_lt : wordVal < 2 ^ w := hx.2 (base + off + wIdx)
  have hfit_shr : Fits w (wordVal >>> sh) := (Nat.shiftRight_le _ _).trans_lt hword_lt
  have hpow_d_lt : 2 ^ d < 2 ^ w := Nat.pow_lt_pow_right one_lt_two (by omega)
  have hfit_dmask : Fits w (2 ^ d - 1) := by change 2 ^ d - 1 < 2 ^ w; omega
  have hfit_out : Fits w (extractPacked (base + off) b d w x.mem q).val :=
    (extractPacked (base + off) b d w x.mem q).isLt.trans hpow_d_lt
  have hidx_ne30 : idxReg ≠ 30 := Fin.ne_of_val_ne (by change idxReg.val ≠ 30; omega)
  have hidx_ne31 : idxReg ≠ 31 := Fin.ne_of_val_ne (by change idxReg.val ≠ 31; omega)
  have hidx_ne32 : idxReg ≠ 32 := Fin.ne_of_val_ne (by change idxReg.val ≠ 32; omega)
  have hidx_ne33 : idxReg ≠ 33 := Fin.ne_of_val_ne (by change idxReg.val ≠ 33; omega)
  set s1 := x.set 30 off
  have e1 : Exec w (.op (.const 30 off) : Code .exact rQF) x s1 1 := Exec.const hfit_off
  set s2 := s1.set 30 (base + off)
  have e2 : Exec w (.op (.exactBin .add 30 0 30) : Code .exact rQF) s1 s2 1 :=
    exec_exactBin (by simp +decide [s1, h0]) hfit_arr
  set s3 := s2.set 31 p
  have e3 : Exec w (.op (.const 31 p) : Code .exact rQF) s2 s3 1 := Exec.const hfit_p
  set s4 := s3.set 32 wIdx
  have e4 : Exec w (.op (.exactBin .shiftRight 32 idxReg 31) : Code .exact rQF) s3 s4 1 :=
    exec_exactBin (by simp [s3, s2, s1, hidx_ne30, hidx_ne31, hidx, wIdx]) hfit_wIdx
  set s5 := s4.set 30 (base + off + wIdx)
  have e5 : Exec w (.op (.exactBin .add 30 30 32) : Code .exact rQF) s4 s5 1 :=
    exec_exactBin (by simp +decide [s4, s3, s2]) hfit_addr
  set s6 := s5.set 33 wordVal
  have e6 : Exec w (.op (.load 33 30) : Code .exact rQF) s5 s6 1 := by
    simpa +decide [s6, s5, s4, s3, s2, s1, wordVal] using
      (Exec.load (B := .exact) (w := w) (d := 33) (a := 30) (x := s5))
  set s7 := s6.set 31 (2 ^ p - 1)
  have e7 : Exec w (.op (.const 31 (2 ^ p - 1)) : Code .exact rQF) s6 s7 1 :=
    Exec.const hfit_pmask
  set s8 := s7.set 32 subIdx
  have e8 : Exec w (.op (.exactBin .and 32 idxReg 31) : Code .exact rQF) s7 s8 1 :=
    exec_exactBin (by simp [s7, s6, s5, s4, s3, s2, s1, hidx_ne30, hidx_ne31, hidx_ne32,
      hidx_ne33, hidx, subIdx]) hfit_sub
  set s9 := s8.set 31 d
  have e9 : Exec w (.op (.const 31 d) : Code .exact rQF) s8 s9 1 := Exec.const hfit_d
  set s10 := s9.set 32 sh
  have e10 : Exec w (.op (.exactBin .mul 32 32 31) : Code .exact rQF) s9 s10 1 :=
    exec_exactBin (by simp +decide [s9, s8, sh]) hfit_sh
  set s11 := s10.set 33 (wordVal >>> sh)
  have e11 : Exec w (.op (.exactBin .shiftRight 33 33 32) : Code .exact rQF) s10 s11 1 :=
    exec_exactBin (by simp +decide [s10, s9, s8, s7, s6]) hfit_shr
  set s12 := s11.set 34 (2 ^ d - 1)
  have e12 : Exec w (.op (.const 34 (2 ^ d - 1)) : Code .exact rQF) s11 s12 1 :=
    Exec.const hfit_dmask
  set s13 := s12.set dstReg (extractPacked (base + off) b d w x.mem q).val
  have e13 : Exec w (.op (.exactBin .and dstReg 33 34) : Code .exact rQF) s12 s13 1 :=
    exec_exactBin (by simp +decide [s12, s11, extractPacked, getLimb, wordVal, sh, subIdx, wIdx, p])
      hfit_out
  refine ⟨s13,
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq (e9.seq (e10.seq
      (e11.seq (e12.seq e13))))))))))),
    rfl, by simp [s13], fun j hj1 hj2 => ?_⟩
  have hj30 : j ≠ 30 := Fin.ne_of_val_ne (by change j.val ≠ 30; omega)
  have hj31 : j ≠ 31 := Fin.ne_of_val_ne (by change j.val ≠ 31; omega)
  have hj32 : j ≠ 32 := Fin.ne_of_val_ne (by change j.val ≠ 32; omega)
  have hj33 : j ≠ 33 := Fin.ne_of_val_ne (by change j.val ≠ 33; omega)
  have hj34 : j ≠ 34 := Fin.ne_of_val_ne (by change j.val ≠ 34; omega)
  simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
    hj1, hj30, hj31, hj32, hj33, hj34]

/-- Word-RAM program writing `val < 2 ^ d` (in `valReg`) into slot `q : Fin (2 ^ b)` (in `idxReg`)
of the packed array at `base + off`, using scratch registers `30..35` in `16` instructions. -/
@[expose] def writePackedCode (off b d w : ℕ) (idxReg valReg : Fin rQF) : Code .exact rQF :=
  let p := slotPackShift b d w
  .seq (.op (.const 30 off))
  (.seq (.op (.exactBin .add 30 0 30))
  (.seq (.op (.const 31 p))
  (.seq (.op (.exactBin .shiftRight 32 idxReg 31))
  (.seq (.op (.exactBin .add 30 30 32))
  (.seq (.op (.load 33 30))
  (.seq (.op (.const 31 (2 ^ p - 1)))
  (.seq (.op (.exactBin .and 32 idxReg 31))
  (.seq (.op (.const 31 d))
  (.seq (.op (.exactBin .mul 32 32 31))
  (.seq (.op (.exactBin .shiftRight 34 33 32))
  (.seq (.op (.const 35 (2 ^ d - 1)))
  (.seq (.op (.exactBin .and 34 34 35))
  (.seq (.op (.exactBin .xor 34 34 valReg))
  (.seq (.op (.exactBin .shiftLeft 34 34 32))
  (.seq (.op (.exactBin .xor 33 33 34))
        (.op (.store 30 33)))))))))))))))))

theorem writePackedCode_exec {base off b d w : ℕ}
    (hb_lt : b < w) (hd : 0 < d) (hdw : 2 * d ≤ w)
    (hfit_end : Fits w (base + off + packedWords b d w))
    {idxReg valReg : Fin rQF}
    (hidx_lt : idxReg.val < 30) (hval_lt_reg : valReg.val < 30)
    (q : Fin (2 ^ b)) (val : Fin (2 ^ d)) {x : Data rQF}
    (hx : x.Bounded w) (h0 : x.regs 0 = base)
    (hidx : x.regs idxReg = q.val) (hval : x.regs valReg = val.val) :
    ∃ y : Data rQF,
      Exec w (writePackedCode off b d w idxReg valReg) x y 17 ∧
      y.mem = writePackedMem (base + off) b d w x.mem q val.val ∧
      ∀ j : Fin rQF, (j.val < 30 ∨ 36 ≤ j.val) → y.regs j = x.regs j := by
  set p := slotPackShift b d w
  set wIdx := q.val >>> p
  set subIdx := q.val &&& (2 ^ p - 1)
  set sh := subIdx * d
  set oldWord := x.mem (base + off + wIdx)
  set oldLimb := (oldWord >>> sh) &&& (2 ^ d - 1)
  set diff := oldLimb ^^^ val.val
  set newWord := oldWord ^^^ (diff <<< sh)
  have hpow_b : 2 ^ b < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hb_lt
  have hp_le : p ≤ b := slotPackShift_le b d w
  have hpack_lt : 2 ^ p * d < w := two_pow_slotPackShift_mul_lt hd hdw
  have hwIdx_lt : wIdx < packedWords b d w := shiftRight_lt_packedWords b d w q
  have hsub_lt : subIdx < 2 ^ p := and_two_pow_slotPackShift_lt b d w q
  have hsh_lt : sh < w := by
    calc subIdx * d < 2 ^ p * d := Nat.mul_lt_mul_of_pos_right hsub_lt hd
      _ < w := hpack_lt
  have hfit_off : Fits w off := hfit_end.of_le (by omega)
  have hfit_arr : Fits w (base + off) := hfit_end.of_le (by omega)
  have hfit_p : Fits w p := (hp_le.trans_lt hb_lt).trans Nat.lt_two_pow_self
  have hfit_wIdx : Fits w wIdx := hfit_end.of_le (by omega)
  have hfit_addr : Fits w (base + off + wIdx) := hfit_end.of_le (by omega)
  have hfit_pmask : Fits w (2 ^ p - 1) := by
    have : 2 ^ p ≤ 2 ^ b := Nat.pow_le_pow_right two_pos hp_le
    change 2 ^ p - 1 < 2 ^ w
    omega
  have hfit_sub : Fits w subIdx := by
    have : 2 ^ p ≤ 2 ^ b := Nat.pow_le_pow_right two_pos hp_le
    change subIdx < 2 ^ w
    omega
  have hfit_d : Fits w d := (by omega : d < w).trans Nat.lt_two_pow_self
  have hfit_sh : Fits w sh := hsh_lt.trans Nat.lt_two_pow_self
  have holdWord_lt : oldWord < 2 ^ w := hx.2 (base + off + wIdx)
  have hfit_shr : Fits w (oldWord >>> sh) := (Nat.shiftRight_le _ _).trans_lt holdWord_lt
  have hpow_d_lt : 2 ^ d < 2 ^ w := Nat.pow_lt_pow_right one_lt_two (by omega)
  have hfit_dmask : Fits w (2 ^ d - 1) := by change 2 ^ d - 1 < 2 ^ w; omega
  have holdLimb_lt : oldLimb < 2 ^ d := getLimb_lt d oldWord subIdx
  have hfit_oldLimb : Fits w oldLimb := holdLimb_lt.trans hpow_d_lt
  have hdiff_lt : diff < 2 ^ d := Nat.xor_lt_two_pow holdLimb_lt val.isLt
  have hfit_diff : Fits w diff := hdiff_lt.trans hpow_d_lt
  have hdiff_sh_lt : diff <<< sh < 2 ^ w := by
    rw [Nat.shiftLeft_eq]
    have h1 : diff * 2 ^ sh < 2 ^ d * 2 ^ (subIdx * d) :=
      Nat.mul_lt_mul_of_pos_right hdiff_lt (Nat.two_pow_pos _)
    have h2 : 2 ^ d * 2 ^ (subIdx * d) = 2 ^ ((subIdx + 1) * d) := by
      rw [← pow_add, Nat.add_comm, Nat.succ_mul]
    have h3 : (subIdx + 1) * d ≤ 2 ^ p * d := Nat.mul_le_mul_right d hsub_lt
    have h4 : 2 ^ ((subIdx + 1) * d) ≤ 2 ^ w :=
      Nat.pow_le_pow_right two_pos (h3.trans hpack_lt.le)
    omega
  have hfit_diff_sh : Fits w (diff <<< sh) := hdiff_sh_lt
  have hfit_newWord : Fits w newWord := Nat.xor_lt_two_pow holdWord_lt hdiff_sh_lt
  have hidx_ne30 : idxReg ≠ 30 := Fin.ne_of_val_ne (by change idxReg.val ≠ 30; omega)
  have hidx_ne31 : idxReg ≠ 31 := Fin.ne_of_val_ne (by change idxReg.val ≠ 31; omega)
  have hidx_ne32 : idxReg ≠ 32 := Fin.ne_of_val_ne (by change idxReg.val ≠ 32; omega)
  have hidx_ne33 : idxReg ≠ 33 := Fin.ne_of_val_ne (by change idxReg.val ≠ 33; omega)
  have hval_ne30 : valReg ≠ 30 := Fin.ne_of_val_ne (by change valReg.val ≠ 30; omega)
  have hval_ne31 : valReg ≠ 31 := Fin.ne_of_val_ne (by change valReg.val ≠ 31; omega)
  have hval_ne32 : valReg ≠ 32 := Fin.ne_of_val_ne (by change valReg.val ≠ 32; omega)
  have hval_ne33 : valReg ≠ 33 := Fin.ne_of_val_ne (by change valReg.val ≠ 33; omega)
  have hval_ne34 : valReg ≠ 34 := Fin.ne_of_val_ne (by change valReg.val ≠ 34; omega)
  have hval_ne35 : valReg ≠ 35 := Fin.ne_of_val_ne (by change valReg.val ≠ 35; omega)
  set s1 := x.set 30 off
  have e1 : Exec w (.op (.const 30 off) : Code .exact rQF) x s1 1 := Exec.const hfit_off
  set s2 := s1.set 30 (base + off)
  have e2 : Exec w (.op (.exactBin .add 30 0 30) : Code .exact rQF) s1 s2 1 :=
    exec_exactBin (by simp +decide [s1, h0]) hfit_arr
  set s3 := s2.set 31 p
  have e3 : Exec w (.op (.const 31 p) : Code .exact rQF) s2 s3 1 := Exec.const hfit_p
  set s4 := s3.set 32 wIdx
  have e4 : Exec w (.op (.exactBin .shiftRight 32 idxReg 31) : Code .exact rQF) s3 s4 1 :=
    exec_exactBin (by simp [s3, s2, s1, hidx_ne30, hidx_ne31, hidx, wIdx]) hfit_wIdx
  set s5 := s4.set 30 (base + off + wIdx)
  have e5 : Exec w (.op (.exactBin .add 30 30 32) : Code .exact rQF) s4 s5 1 :=
    exec_exactBin (by simp +decide [s4, s3, s2]) hfit_addr
  set s6 := s5.set 33 oldWord
  have e6 : Exec w (.op (.load 33 30) : Code .exact rQF) s5 s6 1 := by
    simpa +decide [s6, s5, s4, s3, s2, s1, oldWord] using
      (Exec.load (B := .exact) (w := w) (d := 33) (a := 30) (x := s5))
  set s7 := s6.set 31 (2 ^ p - 1)
  have e7 : Exec w (.op (.const 31 (2 ^ p - 1)) : Code .exact rQF) s6 s7 1 :=
    Exec.const hfit_pmask
  set s8 := s7.set 32 subIdx
  have e8 : Exec w (.op (.exactBin .and 32 idxReg 31) : Code .exact rQF) s7 s8 1 :=
    exec_exactBin (by simp [s7, s6, s5, s4, s3, s2, s1, hidx_ne30, hidx_ne31, hidx_ne32,
      hidx_ne33, hidx, subIdx]) hfit_sub
  set s9 := s8.set 31 d
  have e9 : Exec w (.op (.const 31 d) : Code .exact rQF) s8 s9 1 := Exec.const hfit_d
  set s10 := s9.set 32 sh
  have e10 : Exec w (.op (.exactBin .mul 32 32 31) : Code .exact rQF) s9 s10 1 :=
    exec_exactBin (by simp +decide [s9, s8, sh]) hfit_sh
  set s11 := s10.set 34 (oldWord >>> sh)
  have e11 : Exec w (.op (.exactBin .shiftRight 34 33 32) : Code .exact rQF) s10 s11 1 :=
    exec_exactBin (by simp +decide [s10, s9, s8, s7, s6]) hfit_shr
  set s12 := s11.set 35 (2 ^ d - 1)
  have e12 : Exec w (.op (.const 35 (2 ^ d - 1)) : Code .exact rQF) s11 s12 1 :=
    Exec.const hfit_dmask
  set s13 := s12.set 34 oldLimb
  have e13 : Exec w (.op (.exactBin .and 34 34 35) : Code .exact rQF) s12 s13 1 :=
    exec_exactBin (by simp +decide [s12, s11, oldLimb]) hfit_oldLimb
  set s14 := s13.set 34 diff
  have e14 : Exec w (.op (.exactBin .xor 34 34 valReg) : Code .exact rQF) s13 s14 1 :=
    exec_exactBin (by simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
      hval_ne30, hval_ne31, hval_ne32, hval_ne33, hval_ne34, hval_ne35, hval, diff]) hfit_diff
  set s15 := s14.set 34 (diff <<< sh)
  have e15 : Exec w (.op (.exactBin .shiftLeft 34 34 32) : Code .exact rQF) s14 s15 1 :=
    exec_exactBin (by simp +decide [s14, s13, s12, s11, s10]) hfit_diff_sh
  set s16 := s15.set 33 newWord
  have e16 : Exec w (.op (.exactBin .xor 33 33 34) : Code .exact rQF) s15 s16 1 :=
    exec_exactBin (by simp +decide [s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, newWord])
      hfit_newWord
  set s17 := s16.write (base + off + wIdx) newWord
  have e17 : Exec w (.op (.store 30 33) : Code .exact rQF) s16 s17 1 := by
    simpa +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5] using
      (Exec.store (B := .exact) (w := w) (a := 30) (s := 33) (x := s16))
  refine ⟨s17,
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq (e9.seq (e10.seq
      (e11.seq (e12.seq (e13.seq (e14.seq (e15.seq (e16.seq e17))))))))))))))),
    rfl, fun j hj => ?_⟩
  have hj30 : j ≠ 30 := Fin.ne_of_val_ne (by change j.val ≠ 30; omega)
  have hj31 : j ≠ 31 := Fin.ne_of_val_ne (by change j.val ≠ 31; omega)
  have hj32 : j ≠ 32 := Fin.ne_of_val_ne (by change j.val ≠ 32; omega)
  have hj33 : j ≠ 33 := Fin.ne_of_val_ne (by change j.val ≠ 33; omega)
  have hj34 : j ≠ 34 := Fin.ne_of_val_ne (by change j.val ≠ 34; omega)
  have hj35 : j ≠ 35 := Fin.ne_of_val_ne (by change j.val ≠ 35; omega)
  simp [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
    Data.write, hj30, hj31, hj32, hj33, hj34, hj35]

/-! ## Section 4: Remainder hash initialization (`remInitCode`) and evaluation (`remEvalCode`) -/

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

/-- Sample the remainder seed `γ : RemSeed w₀` uniformly and store it at `remSeedAddr base w w₀ n`
using `5` instructions (`1` `rand` call). -/
@[expose] def remInitCode (w w₀ n : ℕ) : Code .exact rQF :=
  .seq (.op (.const 30 (remSeedOff w w₀ n)))
  (.seq (.op (.exactBin .add 30 0 30))
  (.seq (.op (.const 31 (2 ^ (w₀ - 1) - 1)))
  (.seq (.rand 32 31)
        (.op (.store 30 32)))))

/-- Closed-form machine state after `remInitCode w w₀ n` samples `γ`. -/
@[expose] def remInitData (base w w₀ n : ℕ) (x : Data rQF) (γ : ℕ) : Data rQF :=
  (((x.set 30 (remSeedOff w w₀ n)).set 30 (remSeedAddr base w w₀ n)).set
    31 (2 ^ (w₀ - 1) - 1)).set 32 γ |>.write (remSeedAddr base w w₀ n) γ

/-- Exact `ProbComp` semantics of `remInitCode w w₀ n`. -/
@[expose] def remInitComp (base w w₀ n : ℕ) (x : Data rQF) : ProbComp (Data rQF × ℕ) := do
  let γ ← ProbComp.unifFin (2 ^ (w₀ - 1) - 1)
  pure (remInitData base w w₀ n x γ.val, 5)

theorem remInitCode_execRand {base w w₀ n k : ℕ} (hw₀ : w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    {x : Data rQF} (h0 : x.regs 0 = base) :
    ExecRand w (remInitCode w w₀ n) x (remInitComp base w w₀ n x) := by
  have hfit_off : Fits w (remSeedOff w w₀ n) :=
    hfit_space.of_le (by dsimp only [remSeedOff, space]; omega)
  have hfit_addr : Fits w (remSeedAddr base w w₀ n) :=
    hfit_space.of_le (by dsimp only [remSeedAddr, space]; omega)
  have hfit_bound : Fits w (2 ^ (w₀ - 1) - 1) := by
    have h1 : 2 ^ (w₀ - 1) - 1 < 2 ^ (w₀ - 1) := Nat.sub_lt (by positivity) one_pos
    have h2 : 2 ^ (w₀ - 1) ≤ 2 ^ w := Nat.pow_le_pow_right two_pos (by omega)
    exact h1.trans_le h2
  set s1 := x.set 30 (remSeedOff w w₀ n)
  have e1 : Exec w (.op (.const 30 (remSeedOff w w₀ n)) : Code .exact rQF) x s1 1 :=
    Exec.const hfit_off
  set s2 := s1.set 30 (remSeedAddr base w w₀ n)
  have e2 : Exec w (.op (.exactBin .add 30 0 30) : Code .exact rQF) s1 s2 1 :=
    exec_exactBin (by simp +decide [s1, h0, remSeedAddr, remSeedOff]) hfit_addr
  set s3 := s2.set 31 (2 ^ (w₀ - 1) - 1)
  have e3 : Exec w (.op (.const 31 (2 ^ (w₀ - 1) - 1)) : Code .exact rQF) s2 s3 1 :=
    Exec.const hfit_bound
  have hfit_s3 : Fits w (s3.regs 31) := by simp [s3, hfit_bound]
  have e4 := ExecRand.rand (B := .exact) (w := w) (dst := 32) (src := 31) (x := s3) hfit_s3
  have h31 : s3.regs 31 = 2 ^ (w₀ - 1) - 1 := by simp [s3]
  rw [h31] at e4
  have e45 := ExecRand.seq
    (m₂ := fun d : Data rQF => pure (d.write (remSeedAddr base w w₀ n) (d.regs 32), 1))
    e4 (fun z hz => by
      obtain ⟨γ, -, hγ⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
      cases OracleComp.eq_of_mem_supportWith_pure hγ
      have h1 := Exec.store (B := .exact) (w := w) (a := 30) (s := 32) (x := s3.set 32 γ.val)
      have h30 : (s3.set 32 γ.val).regs 30 = remSeedAddr base w w₀ n := by simp +decide [s3, s2]
      rw [h30] at h1
      exact h1.execRand)
  have hall := e1.seqRand (e2.seqRand (e3.seqRand e45))
  simpa only [remInitCode, remInitComp, remInitData, s3, s2, s1,
    bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def,
    Data.set_regs, Function.update_self] using hall

theorem map_extractRemSeed_eval_remInitComp (base w w₀ n : ℕ) (x : Data rQF) :
    ((ProbComp.eval (remInitComp base w w₀ n x)).map fun z =>
      extractRemSeed base w w₀ n z.1.mem) =
      PMF.uniformOfFintype (RemSeed w₀) := by
  let e : Fin (2 ^ (w₀ - 1) - 1 + 1) ≃ RemSeed w₀ :=
    finCongr (Nat.sub_add_cancel Nat.one_le_two_pow)
  have hcomp :
      ((ProbComp.eval (remInitComp base w w₀ n x)).map fun z =>
        extractRemSeed base w w₀ n z.1.mem) =
        (ProbComp.eval (ProbComp.unifFin (2 ^ (w₀ - 1) - 1))).map e := by
    dsimp only [remInitComp]
    rw [ProbComp.eval_bind, PMF.map_bind]
    congr 1
    funext γ
    simp only [ProbComp.eval_pure, PMF.pure_map, Function.comp_apply]
    congr 1
    apply Fin.ext
    have hlt : γ.val < 2 ^ (w₀ - 1) := by
      have := Nat.one_le_two_pow (n := w₀ - 1)
      have := γ.isLt
      omega
    dsimp only [extractRemSeed, remInitData, Data.write, Tabulation.extractWord, e]
    simp [hlt]
  rw [hcomp, ProbComp.eval_unifFin, PMF.uniformOfFintype_map_equiv]

/-- Word-RAM snippet computing `(remHash U w₀ k γ u).val` into register `3` from `reg 0 = base`
and `reg 1 = u.val`, using `ReducedKWise.reduceKeyCode w₀ w₀` in `45` deterministic instructions.
-/
@[expose] def remEvalCode (w w₀ n k : ℕ) : Code .exact rQF :=
  .seq (.op (.const 30 (remSeedOff w w₀ n)))
  (.seq (.op (.exactBin .add 0 0 30))
  (.seq ((ReducedKWise.reduceKeyCode w₀ w₀).rename kwiseMap)
  (.seq (.op (.const 30 (remSeedOff w w₀ n)))
  (.seq (.op (.exactBin .sub 0 0 30))
  (.seq (.op (.const 30 (w₀ - remBits w₀ k)))
        (.op (.exactBin .shiftRight 3 3 30)))))))

theorem remEvalCode_exec {base w U w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n k))
    (γ : RemSeed w₀) (u : Fin U) {x : Data rQF}
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = u.val)
    (hseed : x.mem (remSeedAddr base w w₀ n) = γ.val) :
    ∃ y : Data rQF,
      Exec w (remEvalCode w w₀ n k) x y 45 ∧
      y.mem = x.mem ∧
      y.regs 0 = base ∧
      y.regs 3 = (remHash U w₀ k γ u).val ∧
      ∀ j : Fin rQF, 240 ≤ j.val → y.regs j = x.regs j := by
  have hfit_base : Fits w base :=
    hfit_space.of_le (by dsimp only [space]; omega)
  have hfit_off : Fits w (remSeedOff w w₀ n) :=
    hfit_space.of_le (by dsimp only [remSeedOff, space]; omega)
  have hfit_addr : Fits w (remSeedAddr base w w₀ n) :=
    hfit_space.of_le (by dsimp only [remSeedAddr, space]; omega)
  set s1 := x.set 30 (remSeedOff w w₀ n)
  have e1 : Exec w (.op (.const 30 (remSeedOff w w₀ n)) : Code .exact rQF) x s1 1 :=
    Exec.const hfit_off
  set s2 := s1.set 0 (remSeedAddr base w w₀ n)
  have e2 : Exec w (.op (.exactBin .add 0 0 30) : Code .exact rQF) s1 s2 1 :=
    exec_exactBin (by simp +decide [s1, h0, remSeedAddr, remSeedOff]) hfit_addr
  have hs2_α : (s2.comap kwiseMap).mem ((s2.comap kwiseMap).regs 0) < 2 ^ (w₀ - 1) := by
    change s2.mem (s2.regs 0) < 2 ^ (w₀ - 1)
    simp only [s2, s1, Data.set_mem, Data.set_regs, Function.update_self, hseed]
    exact γ.isLt
  have hs2_u : (s2.comap kwiseMap).regs 1 < 2 ^ w₀ := by
    change s2.regs 1 < 2 ^ w₀
    simp only [s2, s1, Data.set_regs, Function.update_of_ne (by decide : (1 : Fin rQF) ≠ 0),
      Function.update_of_ne (by decide : (1 : Fin rQF) ≠ 30), h1]
    exact u.isLt.trans_le hU
  obtain ⟨y₀, ey₀, hy₀_0, hy₀_3, hy₀_mem⟩ :=
    ReducedKWise.reduceKeyCode_exec (b := w₀) hw₀_pos hw₀ (s2.comap kwiseMap) hs2_α hs2_u
  have e3 := ey₀.rename injective_kwiseMap
  set s3 := y₀.extend kwiseMap s2
  have hs3_mem : s3.mem = x.mem := hy₀_mem
  have hs3_0 : s3.regs 0 = remSeedAddr base w w₀ n := by
    change (s3.comap kwiseMap).regs 0 = remSeedAddr base w w₀ n
    rw [Data.comap_extend injective_kwiseMap, hy₀_0]
    rfl
  have hs3_3 : s3.regs 3 = oddMulModWord w₀ γ.val u.val := by
    change (s3.comap kwiseMap).regs 3 = oddMulModWord w₀ γ.val u.val
    rw [Data.comap_extend injective_kwiseMap, hy₀_3]
    have hmin : min w₀ (3 * w₀) = w₀ := min_eq_left (by omega)
    have h0_s2 : (s2.comap kwiseMap).mem ((s2.comap kwiseMap).regs 0) = γ.val := hseed
    have h1_s2 : (s2.comap kwiseMap).regs 1 = u.val := by
      change s2.regs 1 = u.val
      simp +decide [s2, s1, h1]
    rw [h0_s2, h1_s2, hmin, Nat.sub_self, Nat.shiftRight_zero]
  set s4 := s3.set 30 (remSeedOff w w₀ n)
  have e4 : Exec w (.op (.const 30 (remSeedOff w w₀ n)) : Code .exact rQF) s3 s4 1 :=
    Exec.const hfit_off
  set s5 := s4.set 0 base
  have e5 : Exec w (.op (.exactBin .sub 0 0 30) : Code .exact rQF) s4 s5 1 :=
    exec_exactBin (by simp +decide [s4, hs3_0, remSeedAddr, remSeedOff]) hfit_base
  have hfit_sh : Fits w (w₀ - remBits w₀ k) := by
    have : w₀ - remBits w₀ k ≤ w := (Nat.sub_le _ _).trans hw₀
    exact this.trans_lt Nat.lt_two_pow_self
  have hrem_eq : oddMulModWord w₀ γ.val u.val >>> (w₀ - remBits w₀ k) =
      (remHash U w₀ k γ u).val := by
    have hsh : w₀ - remBits w₀ k = w₀ - (k + 1) := by dsimp only [remBits]; omega
    rw [hsh]
    exact oddMulModWord_shiftRight_eq_multiplyShiftReduced (R := k + 1) hw₀_pos γ u
  have hfit_rem : Fits w (remHash U w₀ k γ u).val := by
    have hlt := (remHash U w₀ k γ u).isLt
    have hpow : 2 ^ remBits w₀ k ≤ 2 ^ w :=
      Nat.pow_le_pow_right two_pos ((remBits_le_w₀ w₀ k).trans hw₀)
    exact hlt.trans_le hpow
  set s6 := s5.set 30 (w₀ - remBits w₀ k)
  have e6 : Exec w (.op (.const 30 (w₀ - remBits w₀ k)) : Code .exact rQF) s5 s6 1 :=
    Exec.const hfit_sh
  set s7 := s6.set 3 (remHash U w₀ k γ u).val
  have e7 : Exec w (.op (.exactBin .shiftRight 3 3 30) : Code .exact rQF) s6 s7 1 :=
    exec_exactBin (by simp +decide [s6, s5, s4, hs3_3, hrem_eq]) hfit_rem
  refine ⟨s7, e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7))))), hs3_mem,
    by simp +decide [s7, s6, s5],
    by simp +decide [s7],
    fun j hj => ?_⟩
  have hj0 : j ≠ 0 := Fin.ne_of_val_ne (by change j.val ≠ 0; omega)
  have hj3 : j ≠ 3 := Fin.ne_of_val_ne (by change j.val ≠ 3; omega)
  have hj30 : j ≠ 30 := Fin.ne_of_val_ne (by change j.val ≠ 30; omega)
  have hs3_j : s3.regs j = s2.regs j := extend_kwiseMap_regs hj
  simp [s7, s6, s5, s4, hs3_j, s2, s1, hj0, hj3, hj30]

/-! ## Section 5: High-level slot-field accessors and slot-array zeroing -/

theorem extractPacked_one_val_eq_toNat (arrBase b w : ℕ) (mem : ℕ → ℕ) (q : Fin (2 ^ b)) :
    (extractPacked arrBase b 1 w mem q).val = (extractBit arrBase b w mem q).toNat := by
  dsimp only [extractBit]
  have hlt : (extractPacked arrBase b 1 w mem q).val < 2 := (extractPacked arrBase b 1 w mem q).isLt
  set v := (extractPacked arrBase b 1 w mem q).val
  interval_cases v <;> rfl

/-- Read `((extractFilterState base w w₀ n k x.mem).isFull q).toNat` into `dstReg`. -/
@[expose] def readFullCode (w w₀ n : ℕ) (idxReg dstReg : Fin rQF) : Code .exact rQF :=
  readPackedCode (fullOff w w₀ n) (quotBits w₀ n) 1 w idxReg dstReg

/-- Read `((extractFilterState base w w₀ n k x.mem).isOcc q).toNat` into `dstReg`. -/
@[expose] def readOccCode (w w₀ n : ℕ) (idxReg dstReg : Fin rQF) : Code .exact rQF :=
  readPackedCode (occOff w w₀ n) (quotBits w₀ n) 1 w idxReg dstReg

/-- Read `((extractFilterState base w w₀ n k x.mem).isRunStart q).toNat` into `dstReg`. -/
@[expose] def readRunStartCode (w w₀ n : ℕ) (idxReg dstReg : Fin rQF) : Code .exact rQF :=
  readPackedCode (runOff w w₀ n) (quotBits w₀ n) 1 w idxReg dstReg

/-- Read `((extractFilterState base w w₀ n k x.mem).remAt q).val` into `dstReg`. -/
@[expose] def readRemCode (w w₀ n k : ℕ) (idxReg dstReg : Fin rQF) : Code .exact rQF :=
  readPackedCode (remOff w w₀ n) (quotBits w₀ n) (remBits w₀ k) w idxReg dstReg

/-- Write `bval.toNat` (in `valReg`) into `isFull q`. -/
@[expose] def writeFullCode (w w₀ n : ℕ) (idxReg valReg : Fin rQF) : Code .exact rQF :=
  writePackedCode (fullOff w w₀ n) (quotBits w₀ n) 1 w idxReg valReg

/-- Write `bval.toNat` (in `valReg`) into `isOcc q`. -/
@[expose] def writeOccCode (w w₀ n : ℕ) (idxReg valReg : Fin rQF) : Code .exact rQF :=
  writePackedCode (occOff w w₀ n) (quotBits w₀ n) 1 w idxReg valReg

/-- Write `bval.toNat` (in `valReg`) into `isRunStart q`. -/
@[expose] def writeRunStartCode (w w₀ n : ℕ) (idxReg valReg : Fin rQF) : Code .exact rQF :=
  writePackedCode (runOff w w₀ n) (quotBits w₀ n) 1 w idxReg valReg

/-- Write `r.val` (in `valReg`) into `remAt q`. -/
@[expose] def writeRemCode (w w₀ n k : ℕ) (idxReg valReg : Fin rQF) : Code .exact rQF :=
  writePackedCode (remOff w w₀ n) (quotBits w₀ n) (remBits w₀ k) w idxReg valReg

theorem readFullCode_exec {base w w₀ n k : ℕ}
    (hb_lt : quotBits w₀ n < w) (hw : 2 ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    {idxReg dstReg : Fin rQF} (hidx_lt : idxReg.val < 30)
    (q : Fin (2 ^ quotBits w₀ n)) {x : Data rQF}
    (hx : x.Bounded w) (h0 : x.regs 0 = base) (hidx : x.regs idxReg = q.val) :
    ∃ y : Data rQF,
      Exec w (readFullCode w w₀ n idxReg dstReg) x y 13 ∧
      y.mem = x.mem ∧
      y.regs dstReg = ((extractFilterState base w w₀ n k x.mem).isFull q).toNat ∧
      ∀ j : Fin rQF, j ≠ dstReg → (j.val < 30 ∨ 35 ≤ j.val) → y.regs j = x.regs j := by
  have hfit_end : Fits w (base + fullOff w w₀ n + packedWords (quotBits w₀ n) 1 w) :=
    hfit_space.of_le (by dsimp only [fullOff, remSeedOff, space]; omega)
  obtain ⟨y, hy_exec, hy_mem, hy_dst, hy_regs⟩ :=
    readPackedCode_exec (dstReg := dstReg) hb_lt one_pos hw hfit_end hidx_lt q hx h0 hidx
  refine ⟨y, hy_exec, hy_mem, ?_, hy_regs⟩
  rw [hy_dst, base_add_fullOff, extractPacked_one_val_eq_toNat]
  rfl

theorem readOccCode_exec {base w w₀ n k : ℕ}
    (hb_lt : quotBits w₀ n < w) (hw : 2 ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    {idxReg dstReg : Fin rQF} (hidx_lt : idxReg.val < 30)
    (q : Fin (2 ^ quotBits w₀ n)) {x : Data rQF}
    (hx : x.Bounded w) (h0 : x.regs 0 = base) (hidx : x.regs idxReg = q.val) :
    ∃ y : Data rQF,
      Exec w (readOccCode w w₀ n idxReg dstReg) x y 13 ∧
      y.mem = x.mem ∧
      y.regs dstReg = ((extractFilterState base w w₀ n k x.mem).isOcc q).toNat ∧
      ∀ j : Fin rQF, j ≠ dstReg → (j.val < 30 ∨ 35 ≤ j.val) → y.regs j = x.regs j := by
  have hfit_end : Fits w (base + occOff w w₀ n + packedWords (quotBits w₀ n) 1 w) :=
    hfit_space.of_le (by dsimp only [occOff, fullOff, remSeedOff, space]; omega)
  obtain ⟨y, hy_exec, hy_mem, hy_dst, hy_regs⟩ :=
    readPackedCode_exec (dstReg := dstReg) hb_lt one_pos hw hfit_end hidx_lt q hx h0 hidx
  refine ⟨y, hy_exec, hy_mem, ?_, hy_regs⟩
  rw [hy_dst, base_add_occOff, extractPacked_one_val_eq_toNat]
  rfl

theorem readRunStartCode_exec {base w w₀ n k : ℕ}
    (hb_lt : quotBits w₀ n < w) (hw : 2 ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    {idxReg dstReg : Fin rQF} (hidx_lt : idxReg.val < 30)
    (q : Fin (2 ^ quotBits w₀ n)) {x : Data rQF}
    (hx : x.Bounded w) (h0 : x.regs 0 = base) (hidx : x.regs idxReg = q.val) :
    ∃ y : Data rQF,
      Exec w (readRunStartCode w w₀ n idxReg dstReg) x y 13 ∧
      y.mem = x.mem ∧
      y.regs dstReg = ((extractFilterState base w w₀ n k x.mem).isRunStart q).toNat ∧
      ∀ j : Fin rQF, j ≠ dstReg → (j.val < 30 ∨ 35 ≤ j.val) → y.regs j = x.regs j := by
  have hfit_end : Fits w (base + runOff w w₀ n + packedWords (quotBits w₀ n) 1 w) :=
    hfit_space.of_le (by dsimp only [runOff, occOff, fullOff, remSeedOff, space]; omega)
  obtain ⟨y, hy_exec, hy_mem, hy_dst, hy_regs⟩ :=
    readPackedCode_exec (dstReg := dstReg) hb_lt one_pos hw hfit_end hidx_lt q hx h0 hidx
  refine ⟨y, hy_exec, hy_mem, ?_, hy_regs⟩
  rw [hy_dst, base_add_runOff, extractPacked_one_val_eq_toNat]
  rfl

theorem readRemCode_exec {base w w₀ n k : ℕ}
    (hb_lt : quotBits w₀ n < w) (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    {idxReg dstReg : Fin rQF} (hidx_lt : idxReg.val < 30)
    (q : Fin (2 ^ quotBits w₀ n)) {x : Data rQF}
    (hx : x.Bounded w) (h0 : x.regs 0 = base) (hidx : x.regs idxReg = q.val) :
    ∃ y : Data rQF,
      Exec w (readRemCode w w₀ n k idxReg dstReg) x y 13 ∧
      y.mem = x.mem ∧
      y.regs dstReg = ((extractFilterState base w w₀ n k x.mem).remAt q).val ∧
      ∀ j : Fin rQF, j ≠ dstReg → (j.val < 30 ∨ 35 ≤ j.val) → y.regs j = x.regs j := by
  have hf_pos : 0 < remBits w₀ k := remBits_pos hw₀_pos
  have h2f : 2 * remBits w₀ k ≤ w := by have := remBits_le_w₀ w₀ k; omega
  have hfit_end : Fits w (base + remOff w w₀ n + packedWords (quotBits w₀ n) (remBits w₀ k) w) :=
    hfit_space.of_le (by dsimp only [remOff, runOff, occOff, fullOff, remSeedOff, space]; omega)
  obtain ⟨y, hy_exec, hy_mem, hy_dst, hy_regs⟩ :=
    readPackedCode_exec (dstReg := dstReg) hb_lt hf_pos h2f hfit_end hidx_lt q hx h0 hidx
  refine ⟨y, hy_exec, hy_mem, ?_, hy_regs⟩
  rw [hy_dst, base_add_remOff]
  rfl

theorem writeFullCode_exec {base w w₀ n k : ℕ}
    (hb_lt : quotBits w₀ n < w) (hw : 2 ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    {idxReg valReg : Fin rQF} (hidx_lt : idxReg.val < 30) (hval_lt : valReg.val < 30)
    (q : Fin (2 ^ quotBits w₀ n)) (bval : Bool) {x : Data rQF}
    (hx : x.Bounded w) (h0 : x.regs 0 = base)
    (hidx : x.regs idxReg = q.val) (hval : x.regs valReg = bval.toNat) :
    ∃ y : Data rQF,
      Exec w (writeFullCode w w₀ n idxReg valReg) x y 17 ∧
      extractFilterState base w w₀ n k y.mem =
        (extractFilterState base w w₀ n k x.mem).setFull q bval ∧
      (∀ a, (a < fullBase base w w₀ n ∨ base + space w w₀ n k ≤ a) → y.mem a = x.mem a) ∧
      ∀ j : Fin rQF, (j.val < 30 ∨ 36 ≤ j.val) → y.regs j = x.regs j := by
  have hfit_end : Fits w (base + fullOff w w₀ n + packedWords (quotBits w₀ n) 1 w) :=
    hfit_space.of_le (by dsimp only [fullOff, remSeedOff, space]; omega)
  let v : Fin (2 ^ 1) := ⟨bval.toNat, toNat_lt_two bval⟩
  obtain ⟨y, hy_exec, hy_mem, hy_regs⟩ :=
    writePackedCode_exec hb_lt one_pos hw hfit_end hidx_lt hval_lt q v hx h0 hidx hval
  rw [base_add_fullOff] at hy_mem
  refine ⟨y, hy_exec, ?_, ?_, hy_regs⟩
  · rw [hy_mem]
    exact extractFilterState_writeFull base w w₀ n k x.mem q bval
  · intro a ha
    rw [hy_mem]
    apply writePackedMem_outside
    rcases ha with hlt | hge
    · exact Or.inl hlt
    · exact Or.inr (by dsimp only [fullBase, remSeedAddr, space] at hge ⊢; omega)

theorem writeOccCode_exec {base w w₀ n k : ℕ}
    (hb_lt : quotBits w₀ n < w) (hw : 2 ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    {idxReg valReg : Fin rQF} (hidx_lt : idxReg.val < 30) (hval_lt : valReg.val < 30)
    (q : Fin (2 ^ quotBits w₀ n)) (bval : Bool) {x : Data rQF}
    (hx : x.Bounded w) (h0 : x.regs 0 = base)
    (hidx : x.regs idxReg = q.val) (hval : x.regs valReg = bval.toNat) :
    ∃ y : Data rQF,
      Exec w (writeOccCode w w₀ n idxReg valReg) x y 17 ∧
      extractFilterState base w w₀ n k y.mem =
        (extractFilterState base w w₀ n k x.mem).setOcc q bval ∧
      (∀ a, (a < fullBase base w w₀ n ∨ base + space w w₀ n k ≤ a) → y.mem a = x.mem a) ∧
      ∀ j : Fin rQF, (j.val < 30 ∨ 36 ≤ j.val) → y.regs j = x.regs j := by
  have hfit_end : Fits w (base + occOff w w₀ n + packedWords (quotBits w₀ n) 1 w) :=
    hfit_space.of_le (by dsimp only [occOff, fullOff, remSeedOff, space]; omega)
  let v : Fin (2 ^ 1) := ⟨bval.toNat, toNat_lt_two bval⟩
  obtain ⟨y, hy_exec, hy_mem, hy_regs⟩ :=
    writePackedCode_exec hb_lt one_pos hw hfit_end hidx_lt hval_lt q v hx h0 hidx hval
  rw [base_add_occOff] at hy_mem
  refine ⟨y, hy_exec, ?_, ?_, hy_regs⟩
  · rw [hy_mem]
    exact extractFilterState_writeOcc base w w₀ n k x.mem q bval
  · intro a ha
    rw [hy_mem]
    apply writePackedMem_outside
    rcases ha with hlt | hge
    · exact Or.inl (by dsimp only [occBase] at hlt ⊢; omega)
    · exact Or.inr (by dsimp only [occBase, fullBase, remSeedAddr, space] at hge ⊢; omega)

theorem writeRunStartCode_exec {base w w₀ n k : ℕ}
    (hb_lt : quotBits w₀ n < w) (hw : 2 ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    {idxReg valReg : Fin rQF} (hidx_lt : idxReg.val < 30) (hval_lt : valReg.val < 30)
    (q : Fin (2 ^ quotBits w₀ n)) (bval : Bool) {x : Data rQF}
    (hx : x.Bounded w) (h0 : x.regs 0 = base)
    (hidx : x.regs idxReg = q.val) (hval : x.regs valReg = bval.toNat) :
    ∃ y : Data rQF,
      Exec w (writeRunStartCode w w₀ n idxReg valReg) x y 17 ∧
      extractFilterState base w w₀ n k y.mem =
        (extractFilterState base w w₀ n k x.mem).setRunStart q bval ∧
      (∀ a, (a < fullBase base w w₀ n ∨ base + space w w₀ n k ≤ a) → y.mem a = x.mem a) ∧
      ∀ j : Fin rQF, (j.val < 30 ∨ 36 ≤ j.val) → y.regs j = x.regs j := by
  have hfit_end : Fits w (base + runOff w w₀ n + packedWords (quotBits w₀ n) 1 w) :=
    hfit_space.of_le (by dsimp only [runOff, occOff, fullOff, remSeedOff, space]; omega)
  let v : Fin (2 ^ 1) := ⟨bval.toNat, toNat_lt_two bval⟩
  obtain ⟨y, hy_exec, hy_mem, hy_regs⟩ :=
    writePackedCode_exec hb_lt one_pos hw hfit_end hidx_lt hval_lt q v hx h0 hidx hval
  rw [base_add_runOff] at hy_mem
  refine ⟨y, hy_exec, ?_, ?_, hy_regs⟩
  · rw [hy_mem]
    exact extractFilterState_writeRunStart base w w₀ n k x.mem q bval
  · intro a ha
    rw [hy_mem]
    apply writePackedMem_outside
    rcases ha with hlt | hge
    · exact Or.inl (by dsimp only [runBase, occBase] at hlt ⊢; omega)
    · exact Or.inr (by dsimp only [runBase, occBase, fullBase, remSeedAddr, space] at hge ⊢; omega)

theorem writeRemCode_exec {base w w₀ n k : ℕ}
    (hb_lt : quotBits w₀ n < w) (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    {idxReg valReg : Fin rQF} (hidx_lt : idxReg.val < 30) (hval_lt : valReg.val < 30)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) {x : Data rQF}
    (hx : x.Bounded w) (h0 : x.regs 0 = base)
    (hidx : x.regs idxReg = q.val) (hval : x.regs valReg = r.val) :
    ∃ y : Data rQF,
      Exec w (writeRemCode w w₀ n k idxReg valReg) x y 17 ∧
      extractFilterState base w w₀ n k y.mem =
        (extractFilterState base w w₀ n k x.mem).setRem q r ∧
      (∀ a, (a < fullBase base w w₀ n ∨ base + space w w₀ n k ≤ a) → y.mem a = x.mem a) ∧
      ∀ j : Fin rQF, (j.val < 30 ∨ 36 ≤ j.val) → y.regs j = x.regs j := by
  have hf_pos : 0 < remBits w₀ k := remBits_pos hw₀_pos
  have h2f : 2 * remBits w₀ k ≤ w := by have := remBits_le_w₀ w₀ k; omega
  have hfit_end : Fits w (base + remOff w w₀ n + packedWords (quotBits w₀ n) (remBits w₀ k) w) :=
    hfit_space.of_le (by dsimp only [remOff, runOff, occOff, fullOff, remSeedOff, space]; omega)
  obtain ⟨y, hy_exec, hy_mem, hy_regs⟩ :=
    writePackedCode_exec hb_lt hf_pos h2f hfit_end hidx_lt hval_lt q r hx h0 hidx hval
  rw [base_add_remOff] at hy_mem
  refine ⟨y, hy_exec, ?_, ?_, hy_regs⟩
  · rw [hy_mem]
    exact extractFilterState_writeRem base w w₀ n k x.mem q r
  · intro a ha
    rw [hy_mem]
    apply writePackedMem_outside
    rcases ha with hlt | hge
    · exact Or.inl (by dsimp only [remBase, runBase, occBase] at hlt ⊢; omega)
    · exact Or.inr (by rw [remBase_add_packedWords_eq]; exact hge)

/-- Loop zeroing `[reg 30, reg 31)` when `reg 32 = 0` and `reg 33 = 1`. -/
@[expose] def zeroFillLoop : Code .exact rQF :=
  .loop (.lt 30 31)
    (.seq (.op (.store 30 32))
          (.op (.exactBin .add 30 30 33)))

theorem zeroFillLoop_exec {w endAddr : ℕ} (hfit_end : Fits w endAddr) :
    ∀ (rem ptr : ℕ) (x : Data rQF),
      ptr + rem = endAddr →
      x.regs 30 = ptr →
      x.regs 31 = endAddr →
      x.regs 32 = 0 →
      x.regs 33 = 1 →
      ∃ y : Data rQF,
        Exec w zeroFillLoop x y (4 * rem + 2) ∧
        y.regs 0 = x.regs 0 ∧
        (∀ a, ptr ≤ a → a < endAddr → y.mem a = 0) ∧
        (∀ a, (a < ptr ∨ endAddr ≤ a) → y.mem a = x.mem a) := by
  intro rem
  induction rem with
  | zero =>
    intro ptr x hsum h30 h31 _ _
    have hc : ¬(Cond.lt 30 31).Holds x := by simp [Cond.Holds, h30, h31]; omega
    exact ⟨x, Exec.loop_exit hc, rfl, fun _ h1 h2 => by omega, fun _ _ => rfl⟩
  | succ rem ih =>
    intro ptr x hsum h30 h31 h32 h33
    have hc : (Cond.lt 30 31).Holds x := by simp [Cond.Holds, h30, h31]; omega
    have hfit_ptr1 : Fits w (ptr + 1) := hfit_end.of_le (by omega)
    set s1 := x.write ptr 0
    have e1 : Exec w (.op (.store 30 32) : Code .exact rQF) x s1 1 := by
      simpa [s1, h30, h32] using (Exec.store (B := .exact) (w := w) (a := 30) (s := 32) (x := x))
    set s2 := s1.set 30 (ptr + 1)
    have e2 : Exec w (.op (.exactBin .add 30 30 33) : Code .exact rQF) s1 s2 1 :=
      exec_exactBin (by simp +decide [s1, Data.write, h30, h33]) hfit_ptr1
    obtain ⟨y, hy_exec, hy_0, hy_zero, hy_frame⟩ :=
      ih (ptr + 1) s2 (by omega)
        (by simp [s2])
        (by simp +decide [s2, s1, Data.write, h31])
        (by simp +decide [s2, s1, Data.write, h32])
        (by simp +decide [s2, s1, Data.write, h33])
    have hiter := Exec.loop_iter hc (e1.seq e2) hy_exec
    refine ⟨y, ?_, ?_, ?_, ?_⟩
    · simpa only [zeroFillLoop, show (1 + 1) + (4 * rem + 2) + 2 = 4 * (rem + 1) + 2 by omega]
        using hiter
    · rw [hy_0]; simp +decide [s2, s1, Data.write]
    · intro a hle hlt
      rcases eq_or_lt_of_le hle with rfl | hgt
      · rw [hy_frame ptr (Or.inl (by omega))]
        simp [s2, s1, Data.write]
      · exact hy_zero a hgt hlt
    · intro a ha
      rw [hy_frame a (by omega)]
      have hne : a ≠ ptr := by omega
      simp [s2, s1, Data.write, Function.update_of_ne hne]

/-- Program zeroing the 4 slot arrays `[fullBase base w w₀ n, base + space w w₀ n k)` from
`reg 0 = base`. -/
@[expose] def zeroSlotsCode (w w₀ n k : ℕ) : Code .exact rQF :=
  .seq (.op (.const 30 (fullOff w w₀ n)))
  (.seq (.op (.exactBin .add 30 0 30))
  (.seq (.op (.const 31 (space w w₀ n k)))
  (.seq (.op (.exactBin .add 31 0 31))
  (.seq (.op (.const 32 0))
  (.seq (.op (.const 33 1))
        zeroFillLoop)))))

/-- Exact step count of `zeroSlotsCode w w₀ n k`. -/
@[expose] def zeroSlotsSteps (w w₀ n k : ℕ) : ℕ :=
  4 * (3 * packedWords (quotBits w₀ n) 1 w + packedWords (quotBits w₀ n) (remBits w₀ k) w) + 8

theorem zeroSlotsCode_exec {base w w₀ n k : ℕ}
    (hfit_space : Fits w (base + space w w₀ n k))
    {x : Data rQF} (h0 : x.regs 0 = base) :
    ∃ y : Data rQF,
      Exec w (zeroSlotsCode w w₀ n k) x y (zeroSlotsSteps w w₀ n k) ∧
      y.regs 0 = base ∧
      extractFilterState base w w₀ n k y.mem =
        FilterState.empty (quotBits w₀ n) (remBits w₀ k) ∧
      (∀ a, (a < fullBase base w w₀ n ∨ base + space w w₀ n k ≤ a) → y.mem a = x.mem a) := by
  have hfit_foff : Fits w (fullOff w w₀ n) :=
    hfit_space.of_le (by dsimp only [fullOff, remSeedOff, space]; omega)
  have hfit_fbase : Fits w (fullBase base w w₀ n) :=
    hfit_space.of_le (by dsimp only [fullBase, remSeedAddr, space]; omega)
  have hfit_sp : Fits w (space w w₀ n k) :=
    hfit_space.of_le (by omega)
  have hfit_0 : Fits w 0 := hfit_space.of_le (Nat.zero_le _)
  have hfit_1 : Fits w 1 := hfit_space.of_le (by dsimp only [space]; omega)
  set s1 := x.set 30 (fullOff w w₀ n)
  have e1 : Exec w (.op (.const 30 (fullOff w w₀ n)) : Code .exact rQF) x s1 1 :=
    Exec.const hfit_foff
  set s2 := s1.set 30 (fullBase base w w₀ n)
  have e2 : Exec w (.op (.exactBin .add 30 0 30) : Code .exact rQF) s1 s2 1 :=
    exec_exactBin (by simp +decide [s1, h0, base_add_fullOff]) hfit_fbase
  set s3 := s2.set 31 (space w w₀ n k)
  have e3 : Exec w (.op (.const 31 (space w w₀ n k)) : Code .exact rQF) s2 s3 1 :=
    Exec.const hfit_sp
  set s4 := s3.set 31 (base + space w w₀ n k)
  have e4 : Exec w (.op (.exactBin .add 31 0 31) : Code .exact rQF) s3 s4 1 :=
    exec_exactBin (by simp +decide [s3, s2, s1, h0]) hfit_space
  set s5 := s4.set 32 0
  have e5 : Exec w (.op (.const 32 0) : Code .exact rQF) s4 s5 1 := Exec.const hfit_0
  set s6 := s5.set 33 1
  have e6 : Exec w (.op (.const 33 1) : Code .exact rQF) s5 s6 1 := Exec.const hfit_1
  set rem := 3 * packedWords (quotBits w₀ n) 1 w + packedWords (quotBits w₀ n) (remBits w₀ k) w
  have hsum : fullBase base w w₀ n + rem = base + space w w₀ n k := by
    dsimp only [fullBase, remSeedAddr, space, rem]
    ring
  obtain ⟨y, hy_exec, hy_0, hy_zero, hy_frame⟩ :=
    zeroFillLoop_exec hfit_space rem (fullBase base w w₀ n) s6 hsum
      (by simp +decide [s6, s5, s4, s3, s2])
      (by simp +decide [s6, s5, s4])
      (by simp +decide [s6, s5])
      (by simp +decide [s6])
  have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq hy_exec)))))
  refine ⟨y, ?_, ?_, extractFilterState_of_zero hy_zero, hy_frame⟩
  · simpa only [zeroSlotsCode, zeroSlotsSteps, rem,
      show 1 + (1 + (1 + (1 + (1 + (1 + (4 * rem + 2)))))) = 4 * rem + 8 by omega] using hall
  · rw [hy_0]; simp +decide [s6, s5, s4, s3, s2, s1, h0]

end Cslib.DataStructure.ApproximateMembership.QuotientFilter
