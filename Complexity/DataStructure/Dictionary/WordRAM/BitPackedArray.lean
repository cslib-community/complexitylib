/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.WordRAM.ExactLog
public import Complexity.DataStructure.WordRAM.Randomized.StateTransition
public import Mathlib.Data.Nat.Bitwise
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
`base + wOff + 1`, updated in place via bitwise XOR. Unlike single-word packing primitives such as
`QuotientFilter`'s `extractPacked`/`writePackedMem` or `Cslib.BitString.readPackedField` (which pack
`⌊w / k⌋` entries per word without crossing word boundaries and thus waste up to half of each word
when `k > w / 2`), allowing entries to straddle adjacent words achieves the tight `⌈N * k / w⌉ + 2`
word bound needed for succinctness.

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
theorem wordOffset_mul_add_bitOffset {k w idx : ℕ} (hw : 0 < w) :
    wordOffset k w idx * w + bitOffset k w idx = idx * k := by
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
  have hid0 : wOff * w + bOff = idx * k := wordOffset_mul_add_bitOffset hw
  have hid0' : wOff' * w + bOff' = idx' * k := wordOffset_mul_add_bitOffset hw
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
  have hfit_one : Fits w 1 := hfit_addr1.of_le (by omega)
  have hfit_div_w : Fits w (idx / w) := hfit_idx.of_le (Nat.div_le_self idx w)
  have hfit_div_mul : Fits w ((idx / w) * k) :=
    hfit_wOff.of_le (Nat.le_add_right _ _)
  have hfit_mod_w : Fits w (idx % w) := hfit_w.of_le (Nat.mod_lt idx hw).le
  have hfit_mod_mul : Fits w ((idx % w) * k) := mod_mul_lt_two_pow hw hkw idx
  have hfit_mod_div : Fits w (((idx % w) * k) / w) :=
    hfit_mod_mul.of_le (Nat.div_le_self _ _)
  have hbOff_lt : bitOffset k w idx < w := bitOffset_lt hw
  have hfit_bOff : Fits w (bitOffset k w idx) := hfit_w.of_le hbOff_lt.le
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
    exec_exactBin (by simp [s8, s7, s6, s5, s4, s3, hr8, bitOffset, Nat.ne_of_gt hw]) hfit_bOff
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
  have e13 : Exec w (.op (.const 4 1) : Code .exact 10) s12 s13 1 := Exec.const hfit_one
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
  have hfit_w : Fits w w := Nat.lt_two_pow_self
  have hfit_k : Fits w k := hfit_w.of_le hkw
  have hfit_one : Fits w 1 := (Nat.pow_lt_pow_iff_right one_lt_two).mpr hw
  have hfit_zero : Fits w 0 := hfit_one.of_le (by omega)
  have hbOff_lt : bitOffset k w idx < w := bitOffset_lt hw
  have hfit_sub_b : Fits w (w - bitOffset k w idx) := hfit_w.of_le (by omega)
  have hk0_le_k : lowWidth k w idx ≤ k := Nat.min_le_left _ _
  have hfit_k1 : Fits w (highWidth k w idx) := hfit_k.of_le (by unfold highWidth; omega)
  set s15 := s14.set 6 (w - bitOffset k w idx)
  have heval15 : BinOp.evalExact .sub (s14.regs 8) (s14.regs 5) = some (w - bitOffset k w idx) := by
    simp [BinOp.evalExact, hs14_5, hs14_8, hbOff_lt.le]
  have e15 : Exec w (.op (.exactBin .sub 6 8 5) : Code .exact 10) s14 s15 1 :=
    exec_exactBin heval15 hfit_sub_b
  have hs15_9 : s15.regs 9 = k := by simp +decide [s15, hs14_9]
  set s16 := s15.set 6 (lowWidth k w idx)
  have e16 : ExecWithin w (.branch (.lt 9 6) (.op (.copy 6 9)) (.op (.copy 6 6)) : Code .exact 10)
      s15 s16 3 := by
    by_cases hlt_k : k < w - bitOffset k w idx
    · have hc : (Cond.lt (9 : Fin 10) 6).Holds s15 := by
        simp +decide [Cond.Holds, s15, hs15_9, hlt_k]
      have hmin : lowWidth k w idx = k := Nat.min_eq_left hlt_k.le
      have ec : Exec w (.op (.copy 6 9) : Code .exact 10) s15 s16 1 := by
        simpa +decide [s16, hmin, hs15_9]
          using (Exec.copy (B := .exact) (w := w) (d := 6) (s := 9) (x := s15))
      exact ⟨1 + 1, by omega, Exec.branch_pos hc ec⟩
    · have hc : ¬(Cond.lt (9 : Fin 10) 6).Holds s15 := by
        simp +decide [Cond.Holds, s15, hs15_9, hlt_k]
      have hmin : lowWidth k w idx = w - bitOffset k w idx :=
        Nat.min_eq_right (not_lt.mp hlt_k)
      have ec : Exec w (.op (.copy 6 6) : Code .exact 10) s15 s16 1 := by
        simpa +decide [s16, hmin, s15]
          using (Exec.copy (B := .exact) (w := w) (d := 6) (s := 6) (x := s15))
      exact ⟨1 + 2, by omega, Exec.branch_neg hc ec⟩
  set s17 := s16.set 8 (highWidth k w idx)
  have e17 : Exec w (.op (.exactBin .sub 8 9 6) : Code .exact 10) s16 s17 1 :=
    exec_exactBin (by
      simp [BinOp.evalExact, s16, hs15_9, hk0_le_k, highWidth]) hfit_k1
  have hk1_lt_w : highWidth k w idx < w := highWidth_lt hw hkw
  have hfit_pow1 : Fits w (2 ^ highWidth k w idx) :=
    (Nat.pow_lt_pow_iff_right one_lt_two).mpr hk1_lt_w
  have hfit_mask1 : Fits w (2 ^ highWidth k w idx - 1) := hfit_pow1.of_le (Nat.sub_le _ _)
  set s18 := s17.set 9 1
  have e18 : Exec w (.op (.const 9 1) : Code .exact 10) s17 s18 1 := Exec.const hfit_one
  set s19 := s18.set 8 (2 ^ highWidth k w idx)
  have e19 : Exec w (.op (.exactBin .shiftLeft 8 9 8) : Code .exact 10) s18 s19 1 :=
    exec_exactBin (by simp +decide [s18, s17, Nat.shiftLeft_eq]) hfit_pow1
  set s20 := s19.set 8 (2 ^ highWidth k w idx - 1)
  have e20 : Exec w (.op (.exactBin .sub 8 8 9) : Code .exact 10) s19 s20 1 :=
    exec_exactBin (by simp [BinOp.evalExact, s19, s18, Nat.one_le_two_pow]) hfit_mask1
  set s21 := s20.set 7 0
  have e21 : Exec w (.op (.const 7 0) : Code .exact 10) s20 s21 1 := Exec.const hfit_zero
  have hs21_mem : s21.mem = x.mem := hmem14
  have hs21_0 : s21.regs 0 = base + offset := by
    simp +decide [s21, s20, s19, s18, s17, s16, s15, hs14_0]
  have hs21_1 : s21.regs 1 = idx := by
    simp +decide [s21, s20, s19, s18, s17, s16, s15, hs14_1]
  have hs21_2 : s21.regs 2 = x.regs 2 := by
    simp +decide [s21, s20, s19, s18, s17, s16, s15, hs14_2]
  have hs21_3 : s21.regs 3 = base + offset + wordOffset k w idx := by
    simp +decide [s21, s20, s19, s18, s17, s16, s15, hs14_3]
  have hs21_4 : s21.regs 4 = base + offset + wordOffset k w idx + 1 := by
    simp +decide [s21, s20, s19, s18, s17, s16, s15, hs14_4]
  have hs21_5 : s21.regs 5 = bitOffset k w idx := by
    simp +decide [s21, s20, s19, s18, s17, s16, s15, hs14_5]
  have hs21_6 : s21.regs 6 = lowWidth k w idx := by
    simp +decide [s21, s20, s19, s18, s17, s16]
  have hs21_8 : s21.regs 8 = 2 ^ highWidth k w idx - 1 := by
    simp +decide [s21, s20]
  have hs21_9 : s21.regs 9 = 1 := by
    simp +decide [s21, s20, s19, s18]
  have e_mask : ∃ x₁ : Data 10,
      ExecWithin w
        (.branch (.eq 6 7)
          (.op (.copy 7 7))
          (.seq (.op (.exactBin .sub 7 6 9))
          (.seq (.op (.exactBin .shiftLeft 7 9 7))
          (.seq (.op (.exactBin .sub 9 7 9))
                (.op (.exactBin .add 7 7 9))))) : Code .exact 10)
        s21 x₁ 6 ∧
      x₁.mem = s21.mem ∧
      x₁.regs 0 = s21.regs 0 ∧
      x₁.regs 1 = s21.regs 1 ∧
      x₁.regs 2 = s21.regs 2 ∧
      x₁.regs 3 = s21.regs 3 ∧
      x₁.regs 4 = s21.regs 4 ∧
      x₁.regs 5 = s21.regs 5 ∧
      x₁.regs 6 = s21.regs 6 ∧
      x₁.regs 7 = 2 ^ lowWidth k w idx - 1 ∧
      x₁.regs 8 = s21.regs 8 := by
    by_cases hk0_0 : lowWidth k w idx = 0
    · have hc : (Cond.eq (6 : Fin 10) 7).Holds s21 := by
        simp +decide [Cond.Holds, s21, hs21_6, hk0_0]
      have hs21_set7 : s21.set 7 (s21.regs 7) = s21 := by
        cases s21; simp [Data.set]
      have ec : Exec w (.op (.copy 7 7) : Code .exact 10) s21 s21 1 := by
        simpa [hs21_set7] using (Exec.copy (B := .exact) (w := w) (d := 7) (s := 7) (x := s21))
      refine ⟨s21, ⟨1 + 1, by omega, Exec.branch_pos hc ec⟩,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
      simp +decide [s21, hk0_0]
    · have hc : ¬(Cond.eq (6 : Fin 10) 7).Holds s21 := by
        simp +decide [Cond.Holds, s21, hs21_6, hk0_0]
      have hk0_pos : 1 ≤ lowWidth k w idx := Nat.pos_of_ne_zero hk0_0
      have hk0_le_w : lowWidth k w idx ≤ w := hk0_le_k.trans hkw
      have hk0_sub_lt : lowWidth k w idx - 1 < w := by omega
      have hfit_sub1 : Fits w (lowWidth k w idx - 1) := hfit_w.of_le hk0_sub_lt.le
      have hfit_pow0 : Fits w (2 ^ (lowWidth k w idx - 1)) :=
        (Nat.pow_lt_pow_iff_right one_lt_two).mpr hk0_sub_lt
      have hfit_sub_pow0 : Fits w (2 ^ (lowWidth k w idx - 1) - 1) :=
        hfit_pow0.of_le (Nat.sub_le _ _)
      have hpow0_sum :
          2 ^ (lowWidth k w idx - 1) + (2 ^ (lowWidth k w idx - 1) - 1) =
            2 ^ lowWidth k w idx - 1 := by
        have hpos : 1 ≤ 2 ^ (lowWidth k w idx - 1) := Nat.one_le_two_pow
        have hpow : 2 ^ lowWidth k w idx = 2 * 2 ^ (lowWidth k w idx - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel hk0_pos]
          rw [Nat.pow_succ']
        omega
      have hfit_mask0 : Fits w (2 ^ lowWidth k w idx - 1) := by
        change 2 ^ lowWidth k w idx - 1 < 2 ^ w
        have hle : 2 ^ lowWidth k w idx ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hk0_le_w
        have hpos : 1 ≤ 2 ^ lowWidth k w idx := Nat.one_le_two_pow
        omega
      set m1 := s21.set 7 (lowWidth k w idx - 1)
      have em1 : Exec w (.op (.exactBin .sub 7 6 9) : Code .exact 10) s21 m1 1 :=
        exec_exactBin (by simp [BinOp.evalExact, hs21_6, hs21_9, hk0_pos]) hfit_sub1
      set m2 := m1.set 7 (2 ^ (lowWidth k w idx - 1))
      have em2 : Exec w (.op (.exactBin .shiftLeft 7 9 7) : Code .exact 10) m1 m2 1 :=
        exec_exactBin (by simp +decide [m1, hs21_9, Nat.shiftLeft_eq]) hfit_pow0
      set m3 := m2.set 9 (2 ^ (lowWidth k w idx - 1) - 1)
      have em3 : Exec w (.op (.exactBin .sub 9 7 9) : Code .exact 10) m2 m3 1 :=
        exec_exactBin (by simp [BinOp.evalExact, m2, m1, hs21_9, Nat.one_le_two_pow]) hfit_sub_pow0
      set m4 := m3.set 7 (2 ^ lowWidth k w idx - 1)
      have em4 : Exec w (.op (.exactBin .add 7 7 9) : Code .exact 10) m3 m4 1 :=
        exec_exactBin (by simp [BinOp.evalExact, m3, m2, hpow0_sum]) hfit_mask0
      refine ⟨m4, ⟨4 + 2, by omega,
        Exec.branch_neg hc (em1.seq (em2.seq (em3.seq em4)))⟩, rfl, ?_⟩
      simp +decide [m4, m3, m2, m1]
  obtain ⟨x₁, hex_mask, hmem, hr0, hr1', hr2, hr3, hr4, hr5, hr6, hr7, hr8'⟩ := e_mask
  obtain ⟨t_m, ht_m, he_m⟩ := hex_mask
  obtain ⟨t16, ht16, he16⟩ := e16
  have he_mask_all : Exec w maskSetupCode s14 x₁ (1 + (t16 + (1 + (1 + (1 + (1 + (1 + t_m))))))) :=
    e15.seq (he16.seq (e17.seq (e18.seq (e19.seq (e20.seq (e21.seq he_m))))))
  refine ⟨x₁, ⟨10 + (1 + (t16 + (1 + (1 + (1 + (1 + (1 + t_m))))))), by omega,
    he_off.seq he_mask_all⟩,
    hmem.trans hs21_mem,
    hr0.trans hs21_0, hr1'.trans hs21_1, hr2.trans hs21_2, hr3.trans hs21_3,
    hr4.trans hs21_4, hr5.trans hs21_5, hr6.trans hs21_6, hr7, hr8'.trans hs21_8⟩

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
  have hm1_fit : Fits w (x.mem addr₁) := hx.2 addr₁
  have hshr0_fit : Fits w (x.mem addr₀ >>> bOff) :=
    hm0_fit.of_le (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _)
  have hlow_lt : (x.mem addr₀ >>> bOff) &&& (2 ^ k₀ - 1) < 2 ^ k₀ := by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hk0_le_w : k₀ ≤ w := (Nat.min_le_left _ _).trans hkw
  have hlow_fit : Fits w ((x.mem addr₀ >>> bOff) &&& (2 ^ k₀ - 1)) :=
    hlow_lt.trans_le (Nat.pow_le_pow_right (by decide) hk0_le_w)
  have hzero_fit : Fits w 0 := Nat.two_pow_pos w
  have hshr1_fit : Fits w (x.mem addr₁ >>> 0) := hm1_fit
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
  have hread_fit : Fits w (readPacked (base + offset) k w x.mem idx) :=
    (readPacked_lt (base + offset) k w x.mem idx).trans_le
      (Nat.pow_le_pow_right (by decide) hkw)
  set r1 := x₁.set 9 (x.mem addr₀)
  have er1 : Exec w (.op (.load 9 3) : Code .exact 10) x₁ r1 1 := by
    simpa [r1, hr3, hmem₁] using (Exec.load (B := .exact) (w := w) (d := 9) (a := 3) (x := x₁))
  set r2 := r1.set 9 (x.mem addr₀ >>> bOff)
  have er2 : Exec w (.op (.exactBin .shiftRight 9 9 5) : Code .exact 10) r1 r2 1 :=
    exec_exactBin (by simp +decide [r1, hr5]) hshr0_fit
  set r3 := r2.set 9 ((x.mem addr₀ >>> bOff) &&& (2 ^ k₀ - 1))
  have er3 : Exec w (.op (.exactBin .and 9 9 7) : Code .exact 10) r2 r3 1 :=
    exec_exactBin (by simp +decide [r2, r1, hr7]) hlow_fit
  set r4 := r3.set 2 (x.mem addr₁)
  have hr4_r3 : r3.regs 4 = addr₁ := by simp +decide [r3, r2, r1, hr4]
  have hmem_r3 : r3.mem = x.mem := hmem₁
  have er4 : Exec w (.op (.load 2 4) : Code .exact 10) r3 r4 1 := by
    simpa [r4, hr4_r3, hmem_r3] using
      (Exec.load (B := .exact) (w := w) (d := 2) (a := 4) (x := r3))
  set r5 := r4.set 7 0
  have er5 : Exec w (.op (.const 7 0) : Code .exact 10) r4 r5 1 := Exec.const hzero_fit
  set r6 := r5.set 2 (x.mem addr₁ >>> 0)
  have er6 : Exec w (.op (.exactBin .shiftRight 2 2 7) : Code .exact 10) r5 r6 1 :=
    exec_exactBin (by simp +decide [r5, r4]) hshr1_fit
  set r7 := r6.set 2 ((x.mem addr₁ >>> 0) &&& (2 ^ k₁ - 1))
  have er7 : Exec w (.op (.exactBin .and 2 2 8) : Code .exact 10) r6 r7 1 :=
    exec_exactBin (by simp +decide [r6, r5, r4, r3, r2, r1, hr8']) hhigh_fit
  set r8 := r7.set 2 (((x.mem addr₁ >>> 0) &&& (2 ^ k₁ - 1)) <<< k₀)
  have er8 : Exec w (.op (.exactBin .shiftLeft 2 2 6) : Code .exact 10) r7 r8 1 :=
    exec_exactBin (by simp +decide [r7, r6, r5, r4, r3, r2, r1, hr6]) hshl_fit
  set r9 := r8.set 2 (readPacked (base + offset) k w x.mem idx)
  have er9 : Exec w (.op (.exactBin .xor 2 9 2) : Code .exact 10) r8 r9 1 :=
    exec_exactBin (by simp +decide [r8, r7, r6, r5, r4, r3, readPacked, addr₀, addr₁, wOff, bOff,
      k₀, k₁]) hread_fit
  obtain ⟨t₁, ht₁, he₁⟩ := hex₁
  have he_fin : Exec w readPackedFinishCode x₁ r9 9 :=
    er1.seq (er2.seq (er3.seq (er4.seq (er5.seq (er6.seq (er7.seq (er8.seq er9)))))))
  refine ⟨r9, ⟨t₁ + 9, by omega, he₁.seq he_fin⟩, hmem₁, ?_⟩
  simp +decide [r9, r8, r7, r6, r5, r4, r3, r2, r1, hr0, hr1']

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
  set old₀ := (x.mem addr₀ >>> bOff) &&& (2 ^ k₀ - 1)
  set val₀ := val &&& (2 ^ k₀ - 1)
  set mem₁ := Function.update x.mem addr₀ (x.mem addr₀ ^^^ ((old₀ ^^^ val₀) <<< bOff))
  set old₁ := (mem₁ addr₁ >>> 0) &&& (2 ^ k₁ - 1)
  set val₁ := (val >>> k₀) &&& (2 ^ k₁ - 1)
  have hm0_fit : Fits w (x.mem addr₀) := hx.2 addr₀
  have hshr0_fit : Fits w (x.mem addr₀ >>> bOff) :=
    hm0_fit.of_le (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _)
  have hold0_lt : old₀ < 2 ^ k₀ := by
    dsimp only [old₀]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hval0_lt : val₀ < 2 ^ k₀ := by
    dsimp only [val₀]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hk0_le_w : k₀ ≤ w := (Nat.min_le_left _ _).trans hkw
  have hold0_fit : Fits w old₀ := hold0_lt.trans_le (Nat.pow_le_pow_right (by decide) hk0_le_w)
  have hval0_fit : Fits w val₀ := hval0_lt.trans_le (Nat.pow_le_pow_right (by decide) hk0_le_w)
  have hδ0_lt : old₀ ^^^ val₀ < 2 ^ k₀ := Nat.xor_lt_two_pow hold0_lt hval0_lt
  have hδ0_fit : Fits w (old₀ ^^^ val₀) :=
    hδ0_lt.trans_le (Nat.pow_le_pow_right (by decide) hk0_le_w)
  have hsh0_lt : (old₀ ^^^ val₀) <<< bOff < 2 ^ w := by
    refine shiftLeft_lt_two_pow_of_lt hδ0_lt ?_
    have := bitOffset_add_lowWidth_le (k := k) (idx := idx) hw
    omega
  have hsh0_fit : Fits w ((old₀ ^^^ val₀) <<< bOff) := hsh0_lt
  have hnew0_fit : Fits w (x.mem addr₀ ^^^ ((old₀ ^^^ val₀) <<< bOff)) :=
    Nat.xor_lt_two_pow hm0_fit hsh0_lt
  have hm1_fit : Fits w (mem₁ addr₁) := by
    dsimp only [mem₁]
    rw [Function.update_of_ne (by omega)]
    exact hx.2 addr₁
  have hzero_fit : Fits w 0 := Nat.two_pow_pos w
  have hshr1_fit : Fits w (mem₁ addr₁ >>> 0) := hm1_fit
  have hold1_lt : old₁ < 2 ^ k₁ := by
    dsimp only [old₁]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hval1_lt : val₁ < 2 ^ k₁ := by
    dsimp only [val₁]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hk1_le_w : k₁ ≤ w := by
    have := lowWidth_add_highWidth k w idx
    omega
  have hold1_fit : Fits w old₁ := hold1_lt.trans_le (Nat.pow_le_pow_right (by decide) hk1_le_w)
  have hval_shr_fit : Fits w (val >>> k₀) :=
    hfit_val.of_le (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _)
  have hval1_fit : Fits w val₁ := hval1_lt.trans_le (Nat.pow_le_pow_right (by decide) hk1_le_w)
  have hδ1_lt : old₁ ^^^ val₁ < 2 ^ k₁ := Nat.xor_lt_two_pow hold1_lt hval1_lt
  have hδ1_fit : Fits w (old₁ ^^^ val₁) :=
    hδ1_lt.trans_le (Nat.pow_le_pow_right (by decide) hk1_le_w)
  have hsh1_lt : (old₁ ^^^ val₁) <<< 0 < 2 ^ w := hδ1_fit
  have hsh1_fit : Fits w ((old₁ ^^^ val₁) <<< 0) := hsh1_lt
  have hnew1_fit : Fits w (mem₁ addr₁ ^^^ ((old₁ ^^^ val₁) <<< 0)) :=
    Nat.xor_lt_two_pow hm1_fit hsh1_lt
  set w1 := x₁.set 9 (x.mem addr₀)
  have ew1 : Exec w (.op (.load 9 3) : Code .exact 10) x₁ w1 1 := by
    simpa [w1, hr3, hmem₁, addr₀] using
      (Exec.load (B := .exact) (w := w) (d := 9) (a := 3) (x := x₁))
  set w2 := w1.set 9 (x.mem addr₀ >>> bOff)
  have ew2 : Exec w (.op (.exactBin .shiftRight 9 9 5) : Code .exact 10) w1 w2 1 :=
    exec_exactBin (by simp +decide [w1, hr5]) hshr0_fit
  set w3 := w2.set 9 old₀
  have ew3 : Exec w (.op (.exactBin .and 9 9 7) : Code .exact 10) w2 w3 1 :=
    exec_exactBin (by simp +decide [w2, w1, hr7, old₀]) hold0_fit
  set w4 := w3.set 7 val₀
  have ew4 : Exec w (.op (.exactBin .and 7 2 7) : Code .exact 10) w3 w4 1 :=
    exec_exactBin (by simp +decide [w3, w2, w1, hr2', hr7, val₀]) hval0_fit
  set w5 := w4.set 9 (old₀ ^^^ val₀)
  have ew5 : Exec w (.op (.exactBin .xor 9 9 7) : Code .exact 10) w4 w5 1 :=
    exec_exactBin (by simp +decide [w4, w3]) hδ0_fit
  set w6 := w5.set 9 ((old₀ ^^^ val₀) <<< bOff)
  have ew6 : Exec w (.op (.exactBin .shiftLeft 9 9 5) : Code .exact 10) w5 w6 1 :=
    exec_exactBin (by simp +decide [w5, w4, w3, w2, w1, hr5]) hsh0_fit
  set w7 := w6.set 7 (x.mem addr₀)
  have hr3_w6 : w6.regs 3 = addr₀ := by simp +decide [w6, w5, w4, w3, w2, w1, hr3, addr₀]
  have hmem_w6 : w6.mem = x.mem := hmem₁
  have ew7 : Exec w (.op (.load 7 3) : Code .exact 10) w6 w7 1 := by
    simpa [w7, hr3_w6, hmem_w6] using
      (Exec.load (B := .exact) (w := w) (d := 7) (a := 3) (x := w6))
  set w8 := w7.set 9 (x.mem addr₀ ^^^ ((old₀ ^^^ val₀) <<< bOff))
  have ew8 : Exec w (.op (.exactBin .xor 9 7 9) : Code .exact 10) w7 w8 1 :=
    exec_exactBin (by simp +decide [w7, w6]) hnew0_fit
  set w9 := w8.write addr₀ (x.mem addr₀ ^^^ ((old₀ ^^^ val₀) <<< bOff))
  have hr3_w8 : w8.regs 3 = addr₀ := by simp +decide [w8, w7, hr3_w6]
  have hr9_w8 : w8.regs 9 = x.mem addr₀ ^^^ ((old₀ ^^^ val₀) <<< bOff) := by simp +decide [w8]
  have ew9 : Exec w (.op (.store 3 9) : Code .exact 10) w8 w9 1 := by
    simpa [w9, hr3_w8, hr9_w8] using
      (Exec.store (B := .exact) (w := w) (a := 3) (s := 9) (x := w8))
  have hw9_mem : w9.mem = mem₁ := by
    change Function.update w8.mem addr₀ (x.mem addr₀ ^^^ ((old₀ ^^^ val₀) <<< bOff)) = mem₁
    have hw8_mem : w8.mem = x.mem := hmem₁
    rw [hw8_mem]
  have hw9_0 : w9.regs 0 = base + offset := by
    simp +decide [w9, Data.write, w8, w7, w6, w5, w4, w3, w2, w1, hr0]
  have hw9_1 : w9.regs 1 = idx := by
    simp +decide [w9, Data.write, w8, w7, w6, w5, w4, w3, w2, w1, hr1']
  have hw9_2 : w9.regs 2 = val := by
    simp +decide [w9, Data.write, w8, w7, w6, w5, w4, w3, w2, w1, hr2']
  have hw9_4 : w9.regs 4 = addr₁ := by
    simp +decide [w9, Data.write, w8, w7, w6, w5, w4, w3, w2, w1, hr4, addr₁]
  have hw9_6 : w9.regs 6 = k₀ := by
    simp +decide [w9, Data.write, w8, w7, w6, w5, w4, w3, w2, w1, hr6]
  have hw9_8 : w9.regs 8 = 2 ^ k₁ - 1 := by
    simp +decide [w9, Data.write, w8, w7, w6, w5, w4, w3, w2, w1, hr8']
  set w10 := w9.set 5 0
  have ew10 : Exec w (.op (.const 5 0) : Code .exact 10) w9 w10 1 := Exec.const hzero_fit
  set w11 := w10.set 9 (mem₁ addr₁)
  have hr4_w10 : w10.regs 4 = addr₁ := by simp +decide [w10, hw9_4]
  have hmem_w10 : w10.mem = mem₁ := hw9_mem
  have ew11 : Exec w (.op (.load 9 4) : Code .exact 10) w10 w11 1 := by
    simpa [w11, hr4_w10, hmem_w10] using
      (Exec.load (B := .exact) (w := w) (d := 9) (a := 4) (x := w10))
  set w12 := w11.set 9 (mem₁ addr₁ >>> 0)
  have ew12 : Exec w (.op (.exactBin .shiftRight 9 9 5) : Code .exact 10) w11 w12 1 :=
    exec_exactBin (by simp +decide [w11, w10]) hshr1_fit
  set w13 := w12.set 9 old₁
  have ew13 : Exec w (.op (.exactBin .and 9 9 8) : Code .exact 10) w12 w13 1 :=
    exec_exactBin (by simp +decide [w12, w11, w10, hw9_8, old₁]) hold1_fit
  set w14 := w13.set 7 (val >>> k₀)
  have ew14 : Exec w (.op (.exactBin .shiftRight 7 2 6) : Code .exact 10) w13 w14 1 :=
    exec_exactBin (by simp +decide [w13, w12, w11, w10, hw9_2, hw9_6]) hval_shr_fit
  set w15 := w14.set 7 val₁
  have ew15 : Exec w (.op (.exactBin .and 7 7 8) : Code .exact 10) w14 w15 1 :=
    exec_exactBin (by simp +decide [w14, w13, w12, w11, w10, hw9_8, val₁]) hval1_fit
  set w16 := w15.set 9 (old₁ ^^^ val₁)
  have ew16 : Exec w (.op (.exactBin .xor 9 9 7) : Code .exact 10) w15 w16 1 :=
    exec_exactBin (by simp +decide [w15, w14, w13]) hδ1_fit
  set w17 := w16.set 9 ((old₁ ^^^ val₁) <<< 0)
  have ew17 : Exec w (.op (.exactBin .shiftLeft 9 9 5) : Code .exact 10) w16 w17 1 :=
    exec_exactBin (by simp +decide [w16, w15, w14, w13, w12, w11, w10]) hsh1_fit
  set w18 := w17.set 7 (mem₁ addr₁)
  have hr4_w17 : w17.regs 4 = addr₁ := by
    simp +decide [w17, w16, w15, w14, w13, w12, w11, w10, hw9_4]
  have hmem_w17 : w17.mem = mem₁ := hw9_mem
  have ew18 : Exec w (.op (.load 7 4) : Code .exact 10) w17 w18 1 := by
    simpa [w18, hr4_w17, hmem_w17] using
      (Exec.load (B := .exact) (w := w) (d := 7) (a := 4) (x := w17))
  set w19 := w18.set 9 (mem₁ addr₁ ^^^ ((old₁ ^^^ val₁) <<< 0))
  have ew19 : Exec w (.op (.exactBin .xor 9 7 9) : Code .exact 10) w18 w19 1 :=
    exec_exactBin (by simp +decide [w18, w17]) hnew1_fit
  set w20 := w19.write addr₁ (mem₁ addr₁ ^^^ ((old₁ ^^^ val₁) <<< 0))
  have hr4_w19 : w19.regs 4 = addr₁ := by simp +decide [w19, w18, hr4_w17]
  have hr9_w19 : w19.regs 9 = mem₁ addr₁ ^^^ ((old₁ ^^^ val₁) <<< 0) := by simp +decide [w19]
  have ew20 : Exec w (.op (.store 4 9) : Code .exact 10) w19 w20 1 := by
    simpa [w20, hr4_w19, hr9_w19] using
      (Exec.store (B := .exact) (w := w) (a := 4) (s := 9) (x := w19))
  obtain ⟨t₁, ht₁, he₁⟩ := hex₁
  have he_fin : Exec w writePackedFinishCode x₁ w20 20 :=
    ew1.seq (ew2.seq (ew3.seq (ew4.seq (ew5.seq (ew6.seq (ew7.seq (ew8.seq (ew9.seq (ew10.seq
      (ew11.seq (ew12.seq (ew13.seq (ew14.seq (ew15.seq (ew16.seq (ew17.seq (ew18.seq
        (ew19.seq ew20))))))))))))))))))
  refine ⟨w20, ⟨t₁ + 20, by omega, he₁.seq he_fin⟩, ?_, ?_⟩
  · change Function.update w19.mem addr₁ (mem₁ addr₁ ^^^ ((old₁ ^^^ val₁) <<< 0)) =
      writePacked (base + offset) k w x.mem idx val
    have hw19_mem : w19.mem = mem₁ := hw9_mem
    rw [hw19_mem]
    rfl
  · simp +decide [w20, Data.write, w19, w18, w17, w16, w15, w14, w13, w12, w11, w10,
      hw9_0, hw9_1, hw9_2]

end Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
