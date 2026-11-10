/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.ExactLog
public import CslibFrontier.DataStructure.WordRAM.Randomized.StateTransition
public import Mathlib.Data.Nat.Bitwise
import CslibFrontier.Computability.WordRAM.SymbolicExec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Overflow-free bit-packed arrays on the `w`-bit Word RAM

This file defines a bit-packed array primitive storing `N` entries of `k` bits each (`0 ≤ k ≤ w`)
across `packedWords N k w = ⌈N * k / w⌉ + 2` contiguous `w`-bit machine words starting at address
`base`.

To avoid intermediate arithmetic overflow `(idx * k ≥ 2^w)` when `idx < N < 2^w` approaches `2^w`
and `k ≤ w` is `Θ(w)` (so that `idx * k` can reach `2^w`), the word and bit offsets of index `idx`
are computed via the Euclidean decomposition `idx = (idx / w) * w + (idx % w)`:
* `wordOffset k w idx = (idx / w) * k + ((idx % w) * k) / w = (idx * k) / w`,
* `bitOffset k w idx = ((idx % w) * k) % w = (idx * k) % w`.
Because `(idx % w) * k ≤ (w - 1) * w < 2^w` holds for every word width `w ≥ 1`
(`pred_mul_self_lt_two_pow`), every intermediate value fits strictly inside `[0, 2^w)`.

Each `k`-bit entry at `(wOff, bOff)` splits into `lowWidth = min k (w - bOff)` low bits at offset
`bOff` of word `base + wOff` and `highWidth = k - lowWidth` high bits at offset `0` of word
`base + wOff + 1`, updated in place via bitwise XOR. Unlike `QuotientFilter`'s single-word
`extractPacked`/`writePackedMem` (which packs `⌊w / k⌋` entries per word without crossing word
boundaries and wastes up to half of each word when `k > w / 2`), allowing entries to straddle
adjacent words achieves the tight `⌈N * k / w⌉ + 2` word bound needed for succinctness. Unlike
`Cslib.BitString.readPackedField`, which is a pure bit-level specification over a tuple of words
with no Word-RAM machine code or memory layout, this module provides `O(1)`-step Word-RAM read and
write programs over `ℕ → ℕ`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.packedWords`, `wordOffset`, `bitOffset`,
  `lowWidth`, `highWidth`: space and index-offset functions.
* `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.readPacked`, `writePacked`: pure bit-packed
  read and write operations on word memory `ℕ → ℕ`.
* `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.readPackedCode`, `writePackedCode`:
  `O(1)`-step structured Word-RAM programs over `Basis.exact` implementing `readPacked` and
  `writePacked`.

## Main results

* `div_add_packedWords_le`, `packedWords_add_le`, `div_add_mul_packedWords_le`: ceiling-division
  subadditivity bounds for `packedWords`.
* `pred_mul_self_lt_two_pow`, `mod_mul_lt_two_pow`: `(w - 1) * w < 2 ^ w` and
  `(idx % w) * k < 2 ^ w` for all `w ≥ 1` and `k ≤ w`.
* `wordOffset_eq_mul_div`, `bitOffset_eq_mul_mod`: equivalence of the overflow-free formula with
  `(idx * k) / w` and `(idx * k) % w`.
* `readPacked_writePacked_self`, `readPacked_writePacked_of_ne`, `writePacked_outside`,
  `readPacked_zero`: exact array laws for `readPacked` and `writePacked`.
* `readPackedCode_execWithin`, `writePackedCode_execWithin`: `O(1)`-step execution certificates for
  `readPackedCode` and `writePackedCode`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray

/-! ## Section 1: Overflow-free index arithmetic and word bounds -/

/-- Number of `w`-bit words `(N * k + w - 1) / w + 2` reserved for `N` packed `k`-bit entries.
The `+ 2` slack ensures that for every `idx < N`, both `wordOffset k w idx` and
`wordOffset k w idx + 1` lie strictly inside `[0, packedWords N k w)`. -/
@[expose]
def packedWords (N k w : ℕ) : ℕ :=
  (N * k + w - 1) / w + 2

/-- Adding an auxiliary bit-packed array `packedWords N_aux k_aux w` to an existing word bound
`((B + w - 1) / w) + C₀` increases the bit numerator to `B + N_aux * k_aux` and the additive word
constant by at most `3`. -/
theorem div_add_packedWords_le (B C₀ N_aux k_aux w : ℕ) :
    ((B + w - 1) / w + C₀) + packedWords N_aux k_aux w ≤
      (B + N_aux * k_aux + w - 1) / w + (C₀ + 3) := by
  unfold packedWords
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp
  · have hdiv : (B + w - 1) / w + (N_aux * k_aux + w - 1) / w ≤
        (B + N_aux * k_aux + w - 1) / w + 1 := by
      have h1 := Nat.div_add_mod (B + w - 1) w
      have h2 := Nat.div_add_mod (N_aux * k_aux + w - 1) w
      have h3 := Nat.div_add_mod (B + N_aux * k_aux + w - 1) w
      have hm3 : (B + N_aux * k_aux + w - 1) % w < w := Nat.mod_lt _ hw
      have hlt :
          w * ((B + w - 1) / w + (N_aux * k_aux + w - 1) / w) <
            w * ((B + N_aux * k_aux + w - 1) / w + 2) := by
        rw [Nat.left_distrib, Nat.left_distrib, Nat.mul_two]
        omega
      have hlt' := (Nat.mul_lt_mul_left hw).mp hlt
      omega
    omega

/-- Ceiling-division subadditivity for `packedWords`:
`packedWords N₁ k₁ w + packedWords N₂ k₂ w ≤ (N₁ * k₁ + N₂ * k₂ + w - 1) / w + 5`. -/
theorem packedWords_add_le (N₁ k₁ N₂ k₂ w : ℕ) :
    packedWords N₁ k₁ w + packedWords N₂ k₂ w ≤
      (N₁ * k₁ + N₂ * k₂ + w - 1) / w + 5 :=
  div_add_packedWords_le (N₁ * k₁) 2 N₂ k₂ w

/-- Adding `c` copies of `packedWords N_aux k_aux w` increases the bit numerator to
`B + (c * N_aux) * k_aux` and the additive word constant by at most `3 * c`. -/
theorem div_add_mul_packedWords_le (c B C₀ N_aux k_aux w : ℕ) :
    ((B + w - 1) / w + C₀) + c * packedWords N_aux k_aux w ≤
      (B + (c * N_aux) * k_aux + w - 1) / w + (C₀ + 3 * c) := by
  induction c generalizing B C₀ with
  | zero => simp
  | succ c ih =>
    have h1 := div_add_packedWords_le B C₀ N_aux k_aux w
    have h2 := ih (B + N_aux * k_aux) (C₀ + 3)
    have hmul : (c + 1) * packedWords N_aux k_aux w =
        packedWords N_aux k_aux w + c * packedWords N_aux k_aux w := by ring
    have hB : B + N_aux * k_aux + (c * N_aux) * k_aux = B + ((c + 1) * N_aux) * k_aux := by ring
    rw [hB] at h2
    omega

/-- Overflow-free word offset `(idx / w) * k + ((idx % w) * k) / w`, equal to `(idx * k) / w`. -/
@[expose]
def wordOffset (k w idx : ℕ) : ℕ :=
  (idx / w) * k + ((idx % w) * k) / w

/-- Overflow-free bit offset `((idx % w) * k) % w < w`, equal to `(idx * k) % w`. -/
@[expose]
def bitOffset (k w idx : ℕ) : ℕ :=
  ((idx % w) * k) % w

/-- Number of bits `min k (w - bitOffset k w idx)` of entry `idx` stored in word
`base + wordOffset k w idx`. -/
@[expose]
def lowWidth (k w idx : ℕ) : ℕ :=
  min k (w - bitOffset k w idx)

/-- Number of bits `k - lowWidth k w idx` of entry `idx` stored in word
`base + wordOffset k w idx + 1`. -/
@[expose]
def highWidth (k w idx : ℕ) : ℕ :=
  k - lowWidth k w idx

/-- For every `w ≥ 1`, `(w - 1) * w < 2 ^ w`. -/
theorem pred_mul_self_lt_two_pow : ∀ {w : ℕ}, 1 ≤ w → (w - 1) * w < 2 ^ w
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | w + 4, _ => by
    have ih := pred_mul_self_lt_two_pow (w := w + 3) (by omega)
    have h2 : 2 * (w + 3) ≤ 2 ^ (w + 3) := Nat.mul_le_pow (a := 2) (by decide) (w + 3)
    have hrew : (w + 4 - 1) * (w + 4) = (w + 3 - 1) * (w + 3) + 2 * (w + 3) := by
      change (w + 3) * (w + 4) = (w + 2) * (w + 3) + 2 * (w + 3)
      ring
    rw [hrew, Nat.pow_succ]
    omega

/-- Whenever `1 ≤ w` and `k ≤ w`, the product `(idx % w) * k` is strictly less than `2 ^ w`. -/
theorem mod_mul_lt_two_pow {w k : ℕ} (hw : 1 ≤ w) (hkw : k ≤ w) (idx : ℕ) :
    (idx % w) * k < 2 ^ w := by
  have hmod : idx % w ≤ w - 1 := by
    have := Nat.mod_lt idx (by omega : 0 < w)
    omega
  exact (Nat.mul_le_mul hmod hkw).trans_lt (pred_mul_self_lt_two_pow hw)

/-- `wordOffset k w idx` equals `(idx * k) / w` for every `w > 0`. -/
theorem wordOffset_eq_mul_div {k w idx : ℕ} (hw : 0 < w) :
    wordOffset k w idx = (idx * k) / w := by
  unfold wordOffset
  have hdecomp : idx * k = (idx % w) * k + ((idx / w) * k) * w := by
    calc idx * k = (w * (idx / w) + idx % w) * k := by rw [Nat.div_add_mod]
      _ = (idx % w) * k + ((idx / w) * k) * w := by ring
  rw [hdecomp, Nat.add_mul_div_right _ _ hw, Nat.add_comm]

/-- `bitOffset k w idx` equals `(idx * k) % w`. -/
theorem bitOffset_eq_mul_mod (k w idx : ℕ) :
    bitOffset k w idx = (idx * k) % w := by
  unfold bitOffset
  have hdecomp : idx * k = (idx % w) * k + ((idx / w) * k) * w := by
    calc idx * k = (w * (idx / w) + idx % w) * k := by rw [Nat.div_add_mod]
      _ = (idx % w) * k + ((idx / w) * k) * w := by ring
  rw [hdecomp, Nat.add_mul_mod_self_right]

/-- `bitOffset k w idx < w` whenever `0 < w`. -/
theorem bitOffset_lt {k w idx : ℕ} (hw : 0 < w) :
    bitOffset k w idx < w :=
  Nat.mod_lt _ hw

/-- Fundamental global bit identity: `wordOffset k w idx * w + bitOffset k w idx = idx * k`. -/
theorem wordOffset_mul_add_bitOffset {k w idx : ℕ} :
    wordOffset k w idx * w + bitOffset k w idx = idx * k := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [bitOffset]
  rw [wordOffset_eq_mul_div hw, bitOffset_eq_mul_mod, Nat.mul_comm _ w, Nat.div_add_mod]

/-- For every `idx < N`, `wordOffset k w idx + 1 < packedWords N k w`. -/
theorem wordOffset_add_one_lt_packedWords {N k w idx : ℕ} (hw : 0 < w) (hidx : idx < N) :
    wordOffset k w idx + 1 < packedWords N k w := by
  rw [wordOffset_eq_mul_div hw]
  unfold packedWords
  have hle : (idx * k) / w ≤ (N * k + w - 1) / w := by
    refine Nat.div_le_div_right ?_
    have : idx * k ≤ N * k := Nat.mul_le_mul_right k hidx.le
    omega
  omega

/-- For every `idx < N`, `wordOffset k w idx < packedWords N k w`. -/
theorem wordOffset_lt_packedWords {N k w idx : ℕ} (hw : 0 < w) (hidx : idx < N) :
    wordOffset k w idx < packedWords N k w :=
  Nat.lt_of_succ_lt (wordOffset_add_one_lt_packedWords hw hidx)

/-- `lowWidth k w idx + highWidth k w idx = k`. -/
theorem lowWidth_add_highWidth (k w idx : ℕ) :
    lowWidth k w idx + highWidth k w idx = k :=
  Nat.add_sub_of_le (Nat.min_le_left _ _)

/-- `bitOffset k w idx + lowWidth k w idx ≤ w` whenever `0 < w`. -/
theorem bitOffset_add_lowWidth_le {k w idx : ℕ} (hw : 0 < w) :
    bitOffset k w idx + lowWidth k w idx ≤ w := by
  unfold lowWidth
  have := Nat.min_le_right k (w - bitOffset k w idx)
  have hlt : bitOffset k w idx < w := bitOffset_lt hw
  omega

/-- Whenever `highWidth k w idx > 0` and `0 < w`, `bitOffset k w idx + lowWidth k w idx = w`. -/
theorem bitOffset_add_lowWidth_eq_of_highWidth_pos {k w idx : ℕ} (hw : 0 < w)
    (hh : 0 < highWidth k w idx) :
    bitOffset k w idx + lowWidth k w idx = w := by
  unfold highWidth lowWidth at hh
  unfold lowWidth
  have hb : bitOffset k w idx < w := bitOffset_lt hw
  have hlt : w - bitOffset k w idx < k := by omega
  rw [Nat.min_eq_right hlt.le]
  omega

/-- Whenever `k ≤ w`, `highWidth k w idx < w` for `w > 0`. -/
theorem highWidth_lt {k w idx : ℕ} (hw : 0 < w) (hkw : k ≤ w) :
    highWidth k w idx < w := by
  unfold highWidth lowWidth
  have hb : bitOffset k w idx < w := bitOffset_lt hw
  omega

/-! ## Section 2: Bitwise shift/mask algebra and disjoint-interval non-interference -/

/-- Shifting `x < 2 ^ len` left by `a` and right by `a`, then masking to `len` bits, recovers
`x`. -/
theorem shiftLeft_shiftRight_and_self {x a len : ℕ} (hx : x < 2 ^ len) :
    ((x <<< a) >>> a) &&& (2 ^ len - 1) = x := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    Nat.mul_div_cancel _ (by positivity), Nat.mod_eq_of_lt hx]

/-- Shifting `x < 2 ^ len` left by `a`, right by `b`, and masking to `len'` bits gives `0` whenever
the intervals `[a, a + len)` and `[b, b + len')` are disjoint (`a + len ≤ b ∨ b + len' ≤ a`). -/
theorem shiftLeft_shiftRight_and_eq_zero {x a len b len' : ℕ} (hx : x < 2 ^ len)
    (hdisj : a + len ≤ b ∨ b + len' ≤ a) :
    ((x <<< a) >>> b) &&& (2 ^ len' - 1) = 0 := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rcases hdisj with hab | hba
  · have hlt : x * 2 ^ a < 2 ^ b :=
      calc x * 2 ^ a < 2 ^ len * 2 ^ a := Nat.mul_lt_mul_of_pos_right hx (by positivity)
        _ = 2 ^ (a + len) := by rw [← Nat.pow_add, Nat.add_comm]
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) hab
    rw [Nat.div_eq_of_lt hlt, Nat.zero_mod]
  · have hpow : 2 ^ a = 2 ^ (a - (b + len') + len') * 2 ^ b := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hpow, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by positivity), Nat.pow_add,
      ← Nat.mul_assoc, Nat.mul_mod_left]

/-- Extracting `len'` bits at offset `b` after XORing a word with `δ <<< a` (`δ < 2 ^ len`) leaves
the extracted bits unchanged whenever `[a, a + len)` and `[b, b + len')` are disjoint. -/
theorem extract_xor_shiftLeft_of_disjoint (word : ℕ) {δ a len b len' : ℕ} (hδ : δ < 2 ^ len)
    (hdisj : a + len ≤ b ∨ b + len' ≤ a) :
    (((word ^^^ (δ <<< a)) >>> b) &&& (2 ^ len' - 1)) =
      ((word >>> b) &&& (2 ^ len' - 1)) := by
  rw [Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right,
    shiftLeft_shiftRight_and_eq_zero hδ hdisj, Nat.xor_zero]

/-- Extracting `len` bits at offset `a` after replacing the field `old` with `val < 2 ^ len` via
`word ^^^ ((old ^^^ val) <<< a)` returns `val`. -/
theorem extract_xor_shiftLeft_self (word a len : ℕ) {val : ℕ} (hval : val < 2 ^ len) :
    let old := (word >>> a) &&& (2 ^ len - 1)
    (((word ^^^ ((old ^^^ val) <<< a)) >>> a) &&& (2 ^ len - 1)) = val := by
  intro old
  have hold : old < 2 ^ len := by
    dsimp only [old]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hxor : old ^^^ val < 2 ^ len := Nat.xor_lt_two_pow hold hval
  rw [Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right,
    shiftLeft_shiftRight_and_self hxor]
  change old ^^^ (old ^^^ val) = val
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-- Recombining the low `k₀` bits `val &&& (2 ^ k₀ - 1)` and high `k₁` bits
`(val >>> k₀) &&& (2 ^ k₁ - 1)` recovers `val` whenever `val < 2 ^ (k₀ + k₁)`. -/
theorem low_xor_high_shiftLeft {val k₀ k₁ : ℕ} (hval : val < 2 ^ (k₀ + k₁)) :
    (val &&& (2 ^ k₀ - 1)) ^^^ (((val >>> k₀) &&& (2 ^ k₁ - 1)) <<< k₀) = val := by
  have hlow : val &&& (2 ^ k₀ - 1) = val % 2 ^ k₀ := Nat.and_two_pow_sub_one_eq_mod val k₀
  have hdiv_lt : val / 2 ^ k₀ < 2 ^ k₁ := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add, Nat.add_comm]
    exact hval
  have hhigh : (val >>> k₀) &&& (2 ^ k₁ - 1) = val / 2 ^ k₀ := by
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hdiv_lt]
  rw [hlow, hhigh]
  -- Since `val % 2 ^ k₀ < 2 ^ k₀`, XOR with `(val / 2 ^ k₀) <<< k₀` equals addition.
  have hxor :
      (val % 2 ^ k₀) ^^^ ((val / 2 ^ k₀) <<< k₀) =
        ((val / 2 ^ k₀) <<< k₀) + val % 2 ^ k₀ := by
    rw [Nat.xor_comm]
    -- Use `Nat.testBit` to show `((val / 2 ^ k₀) <<< k₀) ^^^ (val % 2 ^ k₀) = val`.
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_xor, Nat.shiftLeft_eq, Nat.mul_comm _ (2 ^ k₀)]
    by_cases hi : i < k₀
    · have h1 : ((2 ^ k₀ * (val / 2 ^ k₀)).testBit i) = false := by
        rw [Nat.mul_comm, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
        simp [ show ¬(k₀ ≤ i) by omega]
      have h2 : (val % 2 ^ k₀).testBit i = val.testBit i :=
        Nat.testBit_mod_two_pow val k₀ i |>.trans (by simp [hi])
      have hsum : 2 ^ k₀ * (val / 2 ^ k₀) + val % 2 ^ k₀ = val := Nat.div_add_mod val (2 ^ k₀)
      rw [hsum, h1, h2, Bool.false_xor]
    · have h2 : (val % 2 ^ k₀).testBit i = false := by
        rw [Nat.testBit_mod_two_pow]
        simp [hi]
      have h1 : (2 ^ k₀ * (val / 2 ^ k₀)).testBit i = val.testBit i := by
        rw [Nat.mul_comm, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
        have hge : k₀ ≤ i := by omega
        simp only [hge, decide_true, Bool.true_and, Nat.testBit_div_two_pow]
        congr 1
        omega
      have hsum : 2 ^ k₀ * (val / 2 ^ k₀) + val % 2 ^ k₀ = val := Nat.div_add_mod val (2 ^ k₀)
      rw [hsum, h1, h2, Bool.xor_false]
  rw [hxor, Nat.shiftLeft_eq, Nat.mul_comm, Nat.div_add_mod]

/-! ## Section 3: Pure bit-packed array read/write and read-after-write laws -/

/-- Read the `k`-bit entry at index `idx` from bit-packed array at `base` on a `w`-bit machine. -/
@[expose]
def readPacked (base k w : ℕ) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  let wOff := wordOffset k w idx
  let bOff := bitOffset k w idx
  let k₀ := lowWidth k w idx
  let k₁ := highWidth k w idx
  let low := (mem (base + wOff) >>> bOff) &&& (2 ^ k₀ - 1)
  let high := (mem (base + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)
  low ^^^ (high <<< k₀)

/-- Write `val` (`< 2 ^ k`) into the `k`-bit entry at index `idx` of bit-packed array at `base`. -/
@[expose]
def writePacked (base k w : ℕ) (mem : ℕ → ℕ) (idx val : ℕ) : ℕ → ℕ :=
  let wOff := wordOffset k w idx
  let bOff := bitOffset k w idx
  let k₀ := lowWidth k w idx
  let k₁ := highWidth k w idx
  let old₀ := (mem (base + wOff) >>> bOff) &&& (2 ^ k₀ - 1)
  let val₀ := val &&& (2 ^ k₀ - 1)
  let mem₁ := Function.update mem (base + wOff)
    (mem (base + wOff) ^^^ ((old₀ ^^^ val₀) <<< bOff))
  let old₁ := (mem₁ (base + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)
  let val₁ := (val >>> k₀) &&& (2 ^ k₁ - 1)
  Function.update mem₁ (base + wOff + 1)
    (mem₁ (base + wOff + 1) ^^^ (((old₁ ^^^ val₁) <<< 0)))

/-- Every value returned by `readPacked base k w mem idx` fits in `k` bits (`< 2 ^ k`). -/
theorem readPacked_lt (base k w : ℕ) (mem : ℕ → ℕ) (idx : ℕ) :
    readPacked base k w mem idx < 2 ^ k := by
  unfold readPacked
  dsimp only
  conv_rhs => rw [← lowWidth_add_highWidth k w idx]
  have hlow : ((mem (base + wordOffset k w idx) >>> bitOffset k w idx) &&&
      (2 ^ lowWidth k w idx - 1)) < 2 ^ lowWidth k w idx := by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hhigh : (((mem (base + wordOffset k w idx + 1) >>> 0) &&&
      (2 ^ highWidth k w idx - 1)) <<< lowWidth k w idx) <
      2 ^ (lowWidth k w idx + highWidth k w idx) := by
    rw [Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_comm]
    refine Nat.mul_lt_mul_of_pos_left ?_ (by positivity)
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  exact Nat.xor_lt_two_pow (hlow.trans_le (Nat.pow_le_pow_right (by decide) (by omega))) hhigh

/-- Reading from zeroed words returns `0`. -/
theorem readPacked_zero {base k w : ℕ} {mem : ℕ → ℕ} {idx : ℕ}
    (h0 : mem (base + wordOffset k w idx) = 0)
    (h1 : mem (base + wordOffset k w idx + 1) = 0) :
    readPacked base k w mem idx = 0 := by
  unfold readPacked
  simp [h0, h1]

/-- Reading index `idx` immediately after writing `val < 2 ^ k` at `idx` returns `val`. -/
theorem readPacked_writePacked_self (base k w : ℕ) (mem : ℕ → ℕ) (idx : ℕ) {val : ℕ}
    (hval : val < 2 ^ k) :
    readPacked base k w (writePacked base k w mem idx val) idx = val := by
  unfold readPacked writePacked
  dsimp only
  set wOff := wordOffset k w idx
  set bOff := bitOffset k w idx
  set k₀ := lowWidth k w idx
  set k₁ := highWidth k w idx
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
    dsimp only [mem₁]
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
  have hex0 := extract_xor_shiftLeft_self (mem (base + wOff)) bOff k₀ hval0_lt
  have hex1 := extract_xor_shiftLeft_self (mem₁ (base + wOff + 1)) 0 k₁ hval1_lt
  dsimp only at hex0 hex1
  rw [hex0, hex1]
  have hval' : val < 2 ^ (k₀ + k₁) := by
    rwa [lowWidth_add_highWidth k w idx]
  exact low_xor_high_shiftLeft hval'

/-- Updating word `addr_w` by XORing at `[a, a + len)` preserves extracting `[b, b + len')` from
`addr_r` whenever every overlap `addr_w = addr_r` has disjoint bit intervals
(`a + len ≤ b ∨ b + len' ≤ a`). -/
theorem extract_update_xor_of_disjoint (mem : ℕ → ℕ) (addr_w addr_r : ℕ)
    {δ a len b len' : ℕ} (hδ : δ < 2 ^ len)
    (hdisj : addr_w = addr_r → a + len ≤ b ∨ b + len' ≤ a) :
    (((Function.update mem addr_w (mem addr_w ^^^ (δ <<< a)) addr_r) >>> b) &&&
        (2 ^ len' - 1)) =
      ((mem addr_r >>> b) &&& (2 ^ len' - 1)) := by
  by_cases heq : addr_r = addr_w
  · subst heq
    rw [Function.update_self]
    exact extract_xor_shiftLeft_of_disjoint (mem addr_r) hδ (hdisj rfl)
  · rw [Function.update_of_ne heq]

/-- Reading index `idx' ≠ idx` after writing at `idx` returns the original value at `idx'`. -/
theorem readPacked_writePacked_of_ne {base k w : ℕ} (hw : 0 < w) (mem : ℕ → ℕ)
    {idx idx' : ℕ} (hne : idx' ≠ idx) (val : ℕ) :
    readPacked base k w (writePacked base k w mem idx val) idx' =
      readPacked base k w mem idx' := by
  rcases Nat.eq_zero_or_pos k with rfl | _hk_pos
  · unfold readPacked lowWidth highWidth
    simp
  unfold readPacked writePacked
  dsimp only
  set wOff := wordOffset k w idx
  set bOff := bitOffset k w idx
  set k₀ := lowWidth k w idx
  set k₁ := highWidth k w idx
  set wOff' := wordOffset k w idx'
  set bOff' := bitOffset k w idx'
  set k₀' := lowWidth k w idx'
  set k₁' := highWidth k w idx'
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
  have hglob : idx * k + k ≤ idx' * k ∨ idx' * k + k ≤ idx * k := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · right
      calc idx' * k + k = (idx' + 1) * k := by ring
        _ ≤ idx * k := Nat.mul_le_mul_right k hlt
    · left
      calc idx * k + k = (idx + 1) * k := by ring
        _ ≤ idx' * k := Nat.mul_le_mul_right k hgt
  have hid0 : wOff * w + bOff = idx * k := wordOffset_mul_add_bitOffset
  have hid0' : wOff' * w + bOff' = idx' * k := wordOffset_mul_add_bitOffset
  have hsum : k₀ + k₁ = k := lowWidth_add_highWidth k w idx
  have hsum' : k₀' + k₁' = k := lowWidth_add_highWidth k w idx'
  have hle0 : bOff + k₀ ≤ w := bitOffset_add_lowWidth_le hw
  have hle0' : bOff' + k₀' ≤ w := bitOffset_add_lowWidth_le hw
  have hw_add : (wOff + 1) * w = wOff * w + w := Nat.succ_mul wOff w
  have hw_add' : (wOff' + 1) * w = wOff' * w + w := Nat.succ_mul wOff' w
  have hlow_eq :
      ((mem₂ (base + wOff') >>> bOff') &&& (2 ^ k₀' - 1)) =
        ((mem (base + wOff') >>> bOff') &&& (2 ^ k₀' - 1)) := by
    rw [extract_update_xor_of_disjoint mem₁ (base + wOff + 1) (base + wOff') hδ1 (fun haddr => by
      rcases Nat.eq_zero_or_pos k₁ with hk1_0 | hk1_pos
      · left; omega
      · have hbw : bOff + k₀ = w := bitOffset_add_lowWidth_eq_of_highWidth_pos hw hk1_pos
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
    · have hbw' : bOff' + k₀' = w := bitOffset_add_lowWidth_eq_of_highWidth_pos hw hk1'_pos
      rw [extract_update_xor_of_disjoint mem₁ (base + wOff + 1) (base + wOff' + 1) hδ1
        (fun haddr => by
          rcases Nat.eq_zero_or_pos k₁ with hk1_0 | hk1_pos
          · left; omega
          · have hbw : bOff + k₀ = w := bitOffset_add_lowWidth_eq_of_highWidth_pos hw hk1_pos
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

/-- Writing at `idx < N` leaves all memory addresses outside `[base, base + packedWords N k w)`
unchanged. -/
theorem writePacked_outside {base N k w : ℕ} (hw : 0 < w) (mem : ℕ → ℕ)
    {idx : ℕ} (hidx : idx < N) (val : ℕ) {addr : ℕ}
    (haddr : ¬(base ≤ addr ∧ addr < base + packedWords N k w)) :
    writePacked base k w mem idx val addr = mem addr := by
  unfold writePacked
  have hlt1 : wordOffset k w idx + 1 < packedWords N k w :=
    wordOffset_add_one_lt_packedWords hw hidx
  have hne1 : addr ≠ base + wordOffset k w idx + 1 := by omega
  have hne0 : addr ≠ base + wordOffset k w idx := by omega
  rw [Function.update_of_ne hne1, Function.update_of_ne hne0]

/-- `readPacked` depends only on memory addresses in `[base, base + packedWords N k w)`. -/
theorem readPacked_congr {base N k w : ℕ} (hw : 0 < w) {mem₁ mem₂ : ℕ → ℕ}
    (h : ∀ addr, base ≤ addr ∧ addr < base + packedWords N k w → mem₁ addr = mem₂ addr)
    {idx : ℕ} (hidx : idx < N) :
    readPacked base k w mem₁ idx = readPacked base k w mem₂ idx := by
  unfold readPacked
  dsimp only
  have hlt1 : wordOffset k w idx + 1 < packedWords N k w :=
    wordOffset_add_one_lt_packedWords hw hidx
  have h0 : mem₁ (base + wordOffset k w idx) = mem₂ (base + wordOffset k w idx) :=
    h _ ⟨by omega, by omega⟩
  have h1 : mem₁ (base + wordOffset k w idx + 1) = mem₂ (base + wordOffset k w idx + 1) :=
    h _ ⟨by omega, by omega⟩
  rw [h0, h1]

/-- Whenever `k ≤ w` and `0 < highWidth k w idx`, `lowWidth k w idx < w`. -/
theorem lowWidth_lt_of_highWidth_pos {k w idx : ℕ} (hkw : k ≤ w)
    (hh : 0 < highWidth k w idx) :
    lowWidth k w idx < w := by
  have hsum := lowWidth_add_highWidth k w idx
  omega

/-- If `x < 2 ^ a` and `a + b ≤ w`, then `x <<< b < 2 ^ w`. -/
theorem shiftLeft_lt_two_pow_of_lt {x a b w : ℕ} (hx : x < 2 ^ a) (hab : a + b ≤ w) :
    x <<< b < 2 ^ w := by
  rw [Nat.shiftLeft_eq]
  calc x * 2 ^ b < 2 ^ a * 2 ^ b := Nat.mul_lt_mul_of_pos_right hx (by positivity)
    _ = 2 ^ (a + b) := (Nat.pow_add 2 a b).symm
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hab

/-- `writePacked base k w mem idx val` preserves word-boundedness (`< 2 ^ w`) at every memory
address whenever `0 < w` and `k ≤ w`. -/
theorem writePacked_lt_two_pow {base k w : ℕ} (hw : 0 < w) (hkw : k ≤ w) {mem : ℕ → ℕ}
    (hmem : ∀ addr, mem addr < 2 ^ w) (idx val : ℕ) (addr : ℕ) :
    writePacked base k w mem idx val addr < 2 ^ w := by
  unfold writePacked
  set wOff := wordOffset k w idx
  set bOff := bitOffset k w idx
  set k₀ := lowWidth k w idx
  set k₁ := highWidth k w idx
  set old₀ := (mem (base + wOff) >>> bOff) &&& (2 ^ k₀ - 1)
  set val₀ := val &&& (2 ^ k₀ - 1)
  set mem₁ := Function.update mem (base + wOff)
    (mem (base + wOff) ^^^ ((old₀ ^^^ val₀) <<< bOff))
  set old₁ := (mem₁ (base + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)
  set val₁ := (val >>> k₀) &&& (2 ^ k₁ - 1)
  have hδ0 : old₀ ^^^ val₀ < 2 ^ k₀ := by
    refine Nat.xor_lt_two_pow ?_ ?_ <;>
    · dsimp only [old₀, val₀]
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by positivity)
  have hsh0 : (old₀ ^^^ val₀) <<< bOff < 2 ^ w := by
    refine shiftLeft_lt_two_pow_of_lt hδ0 ?_
    have := bitOffset_add_lowWidth_le (k := k) (idx := idx) hw
    omega
  have hmem₁ : ∀ a, mem₁ a < 2 ^ w := by
    intro a
    dsimp only [mem₁]
    by_cases ha : a = base + wOff
    · subst ha
      rw [Function.update_self]
      exact Nat.xor_lt_two_pow (hmem _) hsh0
    · rw [Function.update_of_ne ha]
      exact hmem a
  have hδ1 : old₁ ^^^ val₁ < 2 ^ k₁ := by
    refine Nat.xor_lt_two_pow ?_ ?_ <;>
    · dsimp only [old₁, val₁]
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by positivity)
  have hsh1 : (old₁ ^^^ val₁) <<< 0 < 2 ^ w := by
    refine shiftLeft_lt_two_pow_of_lt hδ1 ?_
    have := lowWidth_add_highWidth k w idx
    omega
  by_cases ha : addr = base + wOff + 1
  · subst ha
    rw [Function.update_self]
    exact Nat.xor_lt_two_pow (hmem₁ _) hsh1
  · rw [Function.update_of_ne ha]
    exact hmem₁ addr

/-! ## Section 4: Structured Word-RAM programs (`readPackedCode` and `writePackedCode`) -/

open Cslib.WordRAM Cslib.WordRAM.ExactLog

/-- First half of `addrSetupCode`: given `reg 0 = base + offset`, `reg 1 = idx`, `reg 8 = w`, and
`reg 9 = k`, computes `addr₀` (`reg 3`), `addr₁` (`reg 4`), and `bOff` (`reg 5`) in `10`
deterministic instructions while preserving `reg 0, 1, 2, 8, 9`. -/
@[expose] def offsetSetupCode : Code .exact 10 :=
  .seq (.op (.exactBin .div 3 1 8))
  (.seq (.op (.exactBin .mul 3 3 9))
  (.seq (.op (.exactBin .mod 5 1 8))
  (.seq (.op (.exactBin .mul 5 5 9))
  (.seq (.op (.exactBin .div 4 5 8))
  (.seq (.op (.exactBin .add 3 3 4))
  (.seq (.op (.exactBin .mod 5 5 8))
  (.seq (.op (.exactBin .add 3 0 3))
  (.seq (.op (.const 4 1))
        (.op (.exactBin .add 4 3 4))))))))))

/-- Second half of `addrSetupCode`: given `reg 5 = bOff`, `reg 8 = w`, and `reg 9 = k`, computes
`k₀` (`reg 6`), `mask₀ = 2 ^ k₀ - 1` (`reg 7`), and `mask₁ = 2 ^ k₁ - 1` (`reg 8`) in at most
`15` deterministic instructions without overflowing `< 2 ^ w` even when `k₀ = w`. -/
@[expose] def maskSetupCode : Code .exact 10 :=
  .seq (.op (.exactBin .sub 6 8 5))
  (.seq (.branch (.lt 9 6) (.op (.copy 6 9)) (.op (.copy 6 6)))
  (.seq (.op (.exactBin .sub 8 9 6))
  (.seq (.op (.const 9 1))
  (.seq (.op (.exactBin .shiftLeft 8 9 8))
  (.seq (.op (.exactBin .sub 8 8 9))
  (.seq (.op (.const 7 0))
        (.branch (.eq 6 7)
          (.op (.copy 7 7))
          (.seq (.op (.exactBin .sub 7 6 9))
          (.seq (.op (.exactBin .shiftLeft 7 9 7))
          (.seq (.op (.exactBin .sub 9 7 9))
                (.op (.exactBin .add 7 7 9))))))))))))

/-- Parameter-free address and bit-mask setup subprogram on `Data 10`:
Given `reg 0 = base + offset`, `reg 1 = idx`, `reg 8 = w`, and `reg 9 = k` (preserving
`reg 0, 1, 2`), computes:
* `reg 3 = base + offset + wordOffset k w idx`,
* `reg 4 = base + offset + wordOffset k w idx + 1`,
* `reg 5 = bitOffset k w idx`,
* `reg 6 = lowWidth k w idx`,
* `reg 7 = 2 ^ lowWidth k w idx - 1`,
* `reg 8 = 2 ^ highWidth k w idx - 1`. -/
@[expose] def addrSetupCode : Code .exact 10 :=
  .seq offsetSetupCode maskSetupCode

/-- Read suffix on `Data 10` after `addrSetupCode`: loads the two words at `reg 3` and `reg 4`,
extracts and combines the low and high bit slices into `reg 2`. -/
@[expose] def readPackedFinishCode : Code .exact 10 :=
  .seq (.op (.load 9 3))
  (.seq (.op (.exactBin .shiftRight 9 9 5))
  (.seq (.op (.exactBin .and 9 9 7))
  (.seq (.op (.load 2 4))
  (.seq (.op (.const 7 0))
  (.seq (.op (.exactBin .shiftRight 2 2 7))
  (.seq (.op (.exactBin .and 2 2 8))
  (.seq (.op (.exactBin .shiftLeft 2 2 6))
        (.op (.exactBin .xor 2 9 2)))))))))

/-- Parameter-free structured Word-RAM program on `Data 10` that reads
`readPacked (base + offset) k w mem idx` into `reg 2`, given `reg 0 = base + offset`, `reg 1 = idx`,
`reg 8 = w`, and `reg 9 = k`, preserving `reg 0`, `reg 1`, and `mem`. -/
@[expose] def readPackedCode : Code .exact 10 :=
  .seq addrSetupCode readPackedFinishCode

/-- Write suffix on `Data 10` after `addrSetupCode`: updates the low bit slice at `reg 3` and the
high bit slice at `reg 4` from `reg 2 = val`, preserving `reg 0, 1, 2`. -/
@[expose] def writePackedFinishCode : Code .exact 10 :=
  .seq (.op (.load 9 3))
  (.seq (.op (.exactBin .shiftRight 9 9 5))
  (.seq (.op (.exactBin .and 9 9 7))
  (.seq (.op (.exactBin .and 7 2 7))
  (.seq (.op (.exactBin .xor 9 9 7))
  (.seq (.op (.exactBin .shiftLeft 9 9 5))
  (.seq (.op (.load 7 3))
  (.seq (.op (.exactBin .xor 9 7 9))
  (.seq (.op (.store 3 9))
  (.seq (.op (.const 5 0))
  (.seq (.op (.load 9 4))
  (.seq (.op (.exactBin .shiftRight 9 9 5))
  (.seq (.op (.exactBin .and 9 9 8))
  (.seq (.op (.exactBin .shiftRight 7 2 6))
  (.seq (.op (.exactBin .and 7 7 8))
  (.seq (.op (.exactBin .xor 9 9 7))
  (.seq (.op (.exactBin .shiftLeft 9 9 5))
  (.seq (.op (.load 7 4))
  (.seq (.op (.exactBin .xor 9 7 9))
        (.op (.store 4 9))))))))))))))))))))

/-- Parameter-free structured Word-RAM program on `Data 10` that writes `val` (`reg 2`) at `idx`
(`reg 1`) of the bit-packed array at `base + offset` (`reg 0 = base + offset`, `reg 8 = w`,
`reg 9 = k`), preserving `reg 0, 1, 2`. -/
@[expose] def writePackedCode : Code .exact 10 :=
  .seq addrSetupCode writePackedFinishCode

/-- `offsetSetupCode` executes deterministically in `10` instructions. -/
theorem offsetSetupCode_execWithin {base offset N k w idx : ℕ} {x : Data 10}
    (hw : 0 < w) (hkw : k ≤ w) (hidx : idx < N)
    (hbase : x.regs 0 = base + offset) (hr1 : x.regs 1 = idx)
    (hr8 : x.regs 8 = w) (hr9 : x.regs 9 = k)
    (hfit_idx : Fits w idx)
    (hfit_end : Fits w (base + offset + packedWords N k w)) :
    ∃ x₁ : Data 10,
      Exec w offsetSetupCode x x₁ 10 ∧
      x₁.mem = x.mem ∧
      x₁.regs 0 = base + offset ∧
      x₁.regs 1 = idx ∧
      x₁.regs 2 = x.regs 2 ∧
      x₁.regs 3 = base + offset + wordOffset k w idx ∧
      x₁.regs 4 = base + offset + wordOffset k w idx + 1 ∧
      x₁.regs 5 = bitOffset k w idx ∧
      x₁.regs 8 = w ∧
      x₁.regs 9 = k := by
  have hfit_w : Fits w w := Nat.lt_two_pow_self
  have hlt1 : wordOffset k w idx + 1 < packedWords N k w :=
    wordOffset_add_one_lt_packedWords hw hidx
  have hfit_addr1 : Fits w (base + offset + wordOffset k w idx + 1) :=
    hfit_end.of_le (by omega)
  have hfit_addr0 : Fits w (base + offset + wordOffset k w idx) :=
    hfit_addr1.of_le (by omega)
  have hfit_wOff : Fits w (wordOffset k w idx) := hfit_addr0.of_le (by omega)
  have hfit_div_w : Fits w (idx / w) := hfit_idx.of_le (Nat.div_le_self idx w)
  have hfit_div_mul : Fits w ((idx / w) * k) :=
    hfit_wOff.of_le (Nat.le_add_right _ _)
  have hfit_mod_w : Fits w (idx % w) := hfit_w.of_le (Nat.mod_lt idx hw).le
  have hfit_mod_mul : Fits w ((idx % w) * k) := mod_mul_lt_two_pow hw hkw idx
  have hfit_mod_div : Fits w (((idx % w) * k) / w) :=
    hfit_mod_mul.of_le (Nat.div_le_self _ _)
  have hbOff_lt : bitOffset k w idx < w := bitOffset_lt hw
  set s3 := x.set 3 (idx / w)
  have e3 : Exec w (.op (.exactBin .div 3 1 8) : Code .exact 10) x s3 1 :=
    exec_exactBin (by simp [hr1, hr8, Nat.ne_of_gt hw]) hfit_div_w
  set s4 := s3.set 3 ((idx / w) * k)
  have e4 : Exec w (.op (.exactBin .mul 3 3 9) : Code .exact 10) s3 s4 1 :=
    exec_exactBin (by simp +decide [s3, hr9]) hfit_div_mul
  set s5 := s4.set 5 (idx % w)
  have e5 : Exec w (.op (.exactBin .mod 5 1 8) : Code .exact 10) s4 s5 1 :=
    exec_exactBin (by simp [s4, s3, hr1, hr8, Nat.ne_of_gt hw]) hfit_mod_w
  set s6 := s5.set 5 ((idx % w) * k)
  have e6 : Exec w (.op (.exactBin .mul 5 5 9) : Code .exact 10) s5 s6 1 :=
    exec_exactBin (by simp +decide [s5, s4, s3, hr9]) hfit_mod_mul
  set s7 := s6.set 4 (((idx % w) * k) / w)
  have e7 : Exec w (.op (.exactBin .div 4 5 8) : Code .exact 10) s6 s7 1 :=
    exec_exactBin (by simp [s6, s5, s4, s3, hr8, Nat.ne_of_gt hw]) hfit_mod_div
  set s8 := s7.set 3 (wordOffset k w idx)
  have e8 : Exec w (.op (.exactBin .add 3 3 4) : Code .exact 10) s7 s8 1 :=
    exec_exactBin (by simp +decide [s7, s6, s5, s4, wordOffset]) hfit_wOff
  set s9 := s8.set 5 (bitOffset k w idx)
  have e9 : Exec w (.op (.exactBin .mod 5 5 8) : Code .exact 10) s8 s9 1 :=
    exec_exactBin (by simp [s8, s7, s6, s5, s4, s3, hr8, bitOffset, Nat.ne_of_gt hw]) (by fits)
  have hs9_0 : s9.regs 0 = base + offset := by simp +decide [s9, s8, s7, s6, s5, s4, s3, hbase]
  have hs9_1 : s9.regs 1 = idx := by simp +decide [s9, s8, s7, s6, s5, s4, s3, hr1]
  have hs9_2 : s9.regs 2 = x.regs 2 := by simp +decide [s9, s8, s7, s6, s5, s4, s3]
  have hs9_3 : s9.regs 3 = wordOffset k w idx := by simp +decide [s9, s8]
  have hs9_5 : s9.regs 5 = bitOffset k w idx := by simp +decide [s9]
  have hs9_8 : s9.regs 8 = w := by simp +decide [s9, s8, s7, s6, s5, s4, s3, hr8]
  have hs9_9 : s9.regs 9 = k := by simp +decide [s9, s8, s7, s6, s5, s4, s3, hr9]
  set s12 := s9.set 3 (base + offset + wordOffset k w idx)
  have e12 : Exec w (.op (.exactBin .add 3 0 3) : Code .exact 10) s9 s12 1 :=
    exec_exactBin (by simp +decide [hs9_0, hs9_3]) hfit_addr0
  set s13 := s12.set 4 1
  have e13 : Exec w (.op (.const 4 1) : Code .exact 10) s12 s13 1 := Exec.const (by fits)
  set s14 := s13.set 4 (base + offset + wordOffset k w idx + 1)
  have e14 : Exec w (.op (.exactBin .add 4 3 4) : Code .exact 10) s13 s14 1 :=
    exec_exactBin (by simp +decide [s13, s12]) hfit_addr1
  refine ⟨s14, e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq (e9.seq (e12.seq (e13.seq e14)))))))),
    rfl, ?_⟩
  simp +decide [s14, s13, s12, hs9_0, hs9_1, hs9_2, hs9_5, hs9_8, hs9_9]

/-- `addrSetupCode` executes deterministically in at most `25` instructions. -/
theorem addrSetupCode_execWithin {base offset N k w idx : ℕ} {x : Data 10}
    (hw : 0 < w) (hkw : k ≤ w) (hidx : idx < N)
    (hbase : x.regs 0 = base + offset) (hr1 : x.regs 1 = idx)
    (hr8 : x.regs 8 = w) (hr9 : x.regs 9 = k)
    (hfit_idx : Fits w idx)
    (hfit_end : Fits w (base + offset + packedWords N k w)) :
    ∃ x₁ : Data 10,
      ExecWithin w addrSetupCode x x₁ 25 ∧
      x₁.mem = x.mem ∧
      x₁.regs 0 = base + offset ∧
      x₁.regs 1 = idx ∧
      x₁.regs 2 = x.regs 2 ∧
      x₁.regs 3 = base + offset + wordOffset k w idx ∧
      x₁.regs 4 = base + offset + wordOffset k w idx + 1 ∧
      x₁.regs 5 = bitOffset k w idx ∧
      x₁.regs 6 = lowWidth k w idx ∧
      x₁.regs 7 = 2 ^ lowWidth k w idx - 1 ∧
      x₁.regs 8 = 2 ^ highWidth k w idx - 1 := by
  obtain ⟨s14, he_off, hmem14, hs14_0, hs14_1, hs14_2, hs14_3, hs14_4, hs14_5, hs14_8, hs14_9⟩ :=
    offsetSetupCode_execWithin hw hkw hidx hbase hr1 hr8 hr9 hfit_idx hfit_end
  have hbOff_lt : bitOffset k w idx < w := bitOffset_lt hw
  have hk0_le_k : lowWidth k w idx ≤ k := Nat.min_le_left _ _
  have hk1_lt_w : highWidth k w idx < w := highWidth_lt hw hkw
  have hk1 : k - lowWidth k w idx = highWidth k w idx := rfl
  have hfit_le (v : ℕ) (hv : v ≤ w) : Fits w v := Nat.lt_two_pow_self.trans_le' hv
  have hfit_pow (v : ℕ) (hv : v < w) : Fits w (2 ^ v) := Nat.pow_lt_pow_right one_lt_two hv
  have hfit_pow_sub (v : ℕ) (hv : v ≤ w) : Fits w (2 ^ v - 1) :=
    (Nat.sub_lt (Nat.two_pow_pos _) one_pos).trans_le (Nat.pow_le_pow_right two_pos hv)
  have hsum : ¬lowWidth k w idx = 0 →
      2 ^ (lowWidth k w idx - 1) + (2 ^ (lowWidth k w idx - 1) - 1) = 2 ^ lowWidth k w idx - 1 := by
    intro h
    have : 2 ^ lowWidth k w idx = 2 ^ (lowWidth k w idx - 1) * 2 := by
      rw [← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.pos_of_ne_zero h)]
    have := @Nat.one_le_two_pow (lowWidth k w idx - 1)
    omega
  refine WP.exists_execWithin ?_
  unfold addrSetupCode maskSetupCode
  refine WP.seq (WP.of_execWithin he_off.within ?_)
  wram_exec -split [hs14_5, hs14_8, hfit_le]
  refine WP.cut (fun y t => t ≤ 3 ∧
    y = (s14.set 6 (w - bitOffset k w idx)).set 6 (lowWidth k w idx)) ?_ ?_
  · wram_exec [hs14_9]
    · rw [lowWidth, Nat.min_eq_left hc.le]
    · rw [lowWidth, Nat.min_eq_right (by omega)]
  · rintro y t ⟨ht, rfl⟩
    wram_exec [hs14_9, hk1, hfit_le, hfit_pow, hfit_pow_sub, hsum, Nat.one_shiftLeft,
      Nat.one_le_two_pow]
    all_goals wram_simp [hs14_0, hs14_1, hs14_2, hs14_3, hs14_4, hs14_5, hmem14, hc, pow_zero]

/-- `readPackedCode` executes deterministically in at most `34` instructions, placing
`readPacked (base + offset) k w x.mem idx` into `reg 2` while preserving `reg 0`, `reg 1`, and
`x.mem`. -/
theorem readPackedCode_execWithin {base offset N k w idx : ℕ} {x : Data 10}
    (hw : 0 < w) (hkw : k ≤ w) (hidx : idx < N)
    (hx : x.Bounded w)
    (hbase : x.regs 0 = base + offset) (hr1 : x.regs 1 = idx)
    (hr8 : x.regs 8 = w) (hr9 : x.regs 9 = k)
    (hfit_end : Fits w (base + offset + packedWords N k w)) :
    ∃ x₂ : Data 10,
      ExecWithin w readPackedCode x x₂ 34 ∧
      x₂.mem = x.mem ∧
      x₂.regs 0 = base + offset ∧
      x₂.regs 1 = idx ∧
      x₂.regs 2 = readPacked (base + offset) k w x.mem idx := by
  have hfit_idx : Fits w idx := hr1 ▸ hx.1 1
  obtain ⟨x₁, hex₁, hmem₁, hr0, hr1', _, hr3, hr4, hr5, hr6, hr7, hr8'⟩ :=
    addrSetupCode_execWithin hw hkw hidx hbase hr1 hr8 hr9 hfit_idx hfit_end
  set wOff := wordOffset k w idx
  set bOff := bitOffset k w idx
  set k₀ := lowWidth k w idx
  set k₁ := highWidth k w idx
  set addr₀ := base + offset + wOff
  set addr₁ := base + offset + wOff + 1
  have hm0_fit : Fits w (x.mem addr₀) := hx.2 addr₀
  have hshr0_fit : Fits w (x.mem addr₀ >>> bOff) :=
    hm0_fit.of_le (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _)
  have hlow_lt : (x.mem addr₀ >>> bOff) &&& (2 ^ k₀ - 1) < 2 ^ k₀ := by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hk0_le_w : k₀ ≤ w := (Nat.min_le_left _ _).trans hkw
  have hlow_fit : Fits w ((x.mem addr₀ >>> bOff) &&& (2 ^ k₀ - 1)) :=
    hlow_lt.trans_le (Nat.pow_le_pow_right (by decide) hk0_le_w)
  have hshr1_fit : Fits w (x.mem addr₁ >>> 0) := hx.2 addr₁
  have hhigh_lt : (x.mem addr₁ >>> 0) &&& (2 ^ k₁ - 1) < 2 ^ k₁ := by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hk1_le_w : k₁ ≤ w := by
    have := lowWidth_add_highWidth k w idx
    omega
  have hhigh_fit : Fits w ((x.mem addr₁ >>> 0) &&& (2 ^ k₁ - 1)) :=
    hhigh_lt.trans_le (Nat.pow_le_pow_right (by decide) hk1_le_w)
  have hshl_fit : Fits w (((x.mem addr₁ >>> 0) &&& (2 ^ k₁ - 1)) <<< k₀) := by
    refine shiftLeft_lt_two_pow_of_lt hhigh_lt ?_
    have := lowWidth_add_highWidth k w idx
    omega
  have hread : ((x.mem addr₀ >>> bOff) &&& (2 ^ k₀ - 1)) ^^^
      (((x.mem addr₁ >>> 0) &&& (2 ^ k₁ - 1)) <<< k₀) = readPacked (base + offset) k w x.mem idx :=
    rfl
  have hread_fit : Fits w (readPacked (base + offset) k w x.mem idx) :=
    (readPacked_lt (base + offset) k w x.mem idx).trans_le
      (Nat.pow_le_pow_right (by decide) hkw)
  refine WP.exists_execWithin ?_
  unfold readPackedCode readPackedFinishCode
  refine WP.seq (WP.of_execWithin hex₁ ?_)
  wram_exec [hr3, hr4, hr5, hr6, hr7, hr8', hmem₁, hshr0_fit, hlow_fit, hshr1_fit, hhigh_fit,
    hshl_fit, hread, hread_fit]
  wram_simp [hr0, hr1', hmem₁]

/-- `writePackedCode` executes deterministically in at most `45` instructions, updating
`x.mem` to `writePacked (base + offset) k w x.mem idx val` while preserving `reg 0 = base + offset`,
`reg 1 = idx`, and `reg 2 = val`. -/
theorem writePackedCode_execWithin {base offset N k w idx val : ℕ} {x : Data 10}
    (hw : 0 < w) (hkw : k ≤ w) (hidx : idx < N)
    (hx : x.Bounded w)
    (hbase : x.regs 0 = base + offset) (hr1 : x.regs 1 = idx) (hr2 : x.regs 2 = val)
    (hr8 : x.regs 8 = w) (hr9 : x.regs 9 = k)
    (hfit_end : Fits w (base + offset + packedWords N k w)) :
    ∃ x₂ : Data 10,
      ExecWithin w writePackedCode x x₂ 45 ∧
      x₂.mem = writePacked (base + offset) k w x.mem idx val ∧
      x₂.regs 0 = base + offset ∧
      x₂.regs 1 = idx ∧
      x₂.regs 2 = val := by
  have hfit_idx : Fits w idx := hr1 ▸ hx.1 1
  have hfit_val : Fits w val := hr2 ▸ hx.1 2
  obtain ⟨x₁, hex₁, hmem₁, hr0, hr1', hr2', hr3, hr4, hr5, hr6, hr7, hr8'⟩ :=
    addrSetupCode_execWithin hw hkw hidx hbase hr1 hr8 hr9 hfit_idx hfit_end
  rw [hr2] at hr2'
  set wOff := wordOffset k w idx
  set bOff := bitOffset k w idx
  set k₀ := lowWidth k w idx
  set k₁ := highWidth k w idx
  set addr₀ := (base + offset) + wOff
  set addr₁ := (base + offset) + wOff + 1
  have hk0_le_w : k₀ ≤ w := (Nat.min_le_left _ _).trans hkw
  have hk1_le_w : k₁ ≤ w := by
    have := lowWidth_add_highWidth k w idx
    omega
  have hmask_lt (v j : ℕ) : v &&& (2 ^ j - 1) < 2 ^ j := by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hshr_fit (v j : ℕ) (hv : Fits w v) : Fits w (v >>> j) :=
    hv.of_le (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _)
  generalize hold₀ : (x.mem addr₀ >>> bOff) &&& (2 ^ k₀ - 1) = old₀
  generalize hval₀ : val &&& (2 ^ k₀ - 1) = val₀
  generalize hold₁ : (x.mem addr₁ >>> 0) &&& (2 ^ k₁ - 1) = old₁
  generalize hval₁ : (val >>> k₀) &&& (2 ^ k₁ - 1) = val₁
  have hold0_lt : old₀ < 2 ^ k₀ := hold₀ ▸ hmask_lt _ _
  have hval0_lt : val₀ < 2 ^ k₀ := hval₀ ▸ hmask_lt _ _
  have hold1_lt : old₁ < 2 ^ k₁ := hold₁ ▸ hmask_lt _ _
  have hval1_lt : val₁ < 2 ^ k₁ := hval₁ ▸ hmask_lt _ _
  have hfit_of {v j : ℕ} (hv : v < 2 ^ j) (hj : j ≤ w) : Fits w v :=
    hv.trans_le (Nat.pow_le_pow_right (by decide) hj)
  have hxor_fit {a b : ℕ} (ha : Fits w a) (hb : Fits w b) : Fits w (a ^^^ b) :=
    Nat.xor_lt_two_pow ha hb
  have hδ0_lt : old₀ ^^^ val₀ < 2 ^ k₀ := Nat.xor_lt_two_pow hold0_lt hval0_lt
  have hδ1_lt : old₁ ^^^ val₁ < 2 ^ k₁ := Nat.xor_lt_two_pow hold1_lt hval1_lt
  have hsh0_fit : Fits w ((old₀ ^^^ val₀) <<< bOff) := by
    refine shiftLeft_lt_two_pow_of_lt hδ0_lt ?_
    have := bitOffset_add_lowWidth_le (k := k) (idx := idx) hw
    omega
  have hsh1_fit : Fits w ((old₁ ^^^ val₁) <<< 0) := hfit_of hδ1_lt hk1_le_w
  refine WP.exists_execWithin ?_
  unfold writePackedCode writePackedFinishCode
  refine WP.seq (WP.of_execWithin hex₁ ?_)
  wram_exec [hr2', hr3, hr4, hr5, hr6, hr7, hr8', hmem₁, hold₀, hval₀, hold₁, hval₁,
    hshr_fit _ _ (hx.2 addr₀), hshr_fit _ _ (hx.2 addr₁), hshr_fit _ _ hfit_val,
    hfit_of hold0_lt hk0_le_w, hfit_of hval0_lt hk0_le_w, hfit_of hold1_lt hk1_le_w,
    hfit_of hval1_lt hk1_le_w, hfit_of hδ0_lt hk0_le_w, hfit_of hδ1_lt hk1_le_w, hsh0_fit,
    hsh1_fit, hxor_fit (hx.2 addr₀) hsh0_fit, hxor_fit (hx.2 addr₁) hsh1_fit]
  refine ⟨?_, by wram_simp [hr0, hr1', hr2']⟩
  subst hold₀ hval₀ hold₁ hval₁
  have hne : base + offset + wordOffset k w idx + 1 ≠ base + offset + wordOffset k w idx := by omega
  simp only [Data.write_mem, Data.set_mem, hmem₁, writePacked, Function.update_of_ne hne]
  rfl

end Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
