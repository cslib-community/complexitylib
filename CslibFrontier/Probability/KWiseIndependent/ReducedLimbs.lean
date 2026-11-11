/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.KWiseIndependent.Reduced

/-!
# Limb-Aligned Arithmetic and Bit-Packed Table Bounds for Reduced `k`-Wise Hashing

This module develops the pure arithmetic and polynomial-limb identities underlying the Word-RAM
implementation of the two-stage universe-reduced `k`-wise independent hash family
(`Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise`):

1. **Overflow-free full-word multiply-shift (`halfMulMod`, `oddMulModWord`)**: computes
   `(2 * α + 1) * x % 2 ^ w₀ / 2 ^ (w₀ - R)` for any `0 < w₀ ≤ w` using only `< 2 ^ w₀`
   intermediate products and sums, avoiding any `2 * w₀ ≤ w` restriction.
2. **Exact limb factorization of `2 * 3 ^ t` (`reducedChunkBits`, `reducedHalfLimbs`,
   `reducedLimbCount`)**: decomposes any `2 * 3 ^ t`-bit element of `TrinomialField t` into
   `reducedLimbCount t = 2 * 3 ^ min t 3 ≤ 54` limbs of `reducedChunkBits t = 3 ^ (t - 3)` bits
   each, with `2 * reducedChunkBits t ≤ w` unconditionally whenever `w₀ ≤ w`, `b' ≤ w`, and
   `2 ≤ w`, and bit-packed Four-Russians table size
   `reducedTableBits t ≤ max 8 (2 ^ (b / 2)) = o(2 ^ b)` bits
   (`reducedTableWords t w ≤ 2 * reducedTableBits t / w + 1` words) whenever `b' ≤ 3 * b`.
3. **Bit-packed word slices (`getLimb`) and limb-level polynomial multiplication / 4-block
   trinomial reduction (`packLimbs`, `truncLimbs`)**: proves that limb-by-limb carryless
   multiplication followed by limb-aligned 4-block XOR reduction computes exact multiplication and
   addition in `TrinomialField t`.

## Main definitions

* `Cslib.Probability.halfMulMod`, `Cslib.Probability.oddMulModWord`: overflow-free full-word
  odd-multiplier modular product `(2 * α + 1) * x % 2 ^ w₀`.
* `Cslib.Probability.reducedChunkBits`, `Cslib.Probability.reducedHalfLimbs`,
  `Cslib.Probability.reducedLimbCount`: limb bit-width `3 ^ (t - 3)` and limb counts
  `3 ^ min t 3 ≤ 27`, `2 * 3 ^ min t 3 ≤ 54`.
* `Cslib.Probability.reducedTableBits`, `Cslib.Probability.reducedPackShift`,
  `Cslib.Probability.reducedTableWords`: bit-packed Four-Russians table size in bits and words.
* `Cslib.Probability.getLimb`, `Cslib.Probability.packLimbs`,
  `Cslib.Probability.truncLimbs`: conversion between natural numbers `< 2 ^ (L * c)` and `L` limbs
  of `c` bits.

## Main results

* `Cslib.Probability.oddMulModWord_shiftRight_eq_multiplyShiftReduced`: `oddMulModWord` shifted
  right by `w₀ - R` equals `multiplyShiftReduced`.
* `Cslib.Probability.two_mul_reducedChunkBits_le`: `2 * reducedChunkBits t ≤ w` whenever `w₀ ≤ w`,
  `b' ≤ w`, and `2 ≤ w`.
* `Cslib.Probability.reducedTableBits_le`: `reducedTableBits t ≤ max 8 (2 ^ (b / 2))` whenever
  `b' ≤ 3 * b`.
* `Cslib.Probability.reducedTableWords_le`:
  `reducedTableWords t w ≤ 2 * reducedTableBits t / w + 1`.
-/

public section

namespace Cslib.Probability

open Finset Polynomial

/-! ## Section 1: Overflow-free full-word `multiplyShiftReduced` arithmetic -/

/-- Computes `(α * (x' % 2 ^ m)) % 2 ^ m` using only intermediate products and sums `< 2 ^ (m + 1)`
by splitting `m` at `h = m / 2`. -/
@[expose] def halfMulMod (m α x' : ℕ) : ℕ :=
  let h := m / 2
  let α₀ := α &&& (2 ^ h - 1)
  let α₁ := α >>> h
  let x₀ := x' &&& (2 ^ h - 1)
  let x₁ := x' >>> h
  let p₀ := (α₀ * x₀) &&& (2 ^ m - 1)
  let p₁ := ((α₀ * x₁) &&& (2 ^ (m - h) - 1)) <<< h
  let p₂ := ((α₁ * x₀) &&& (2 ^ (m - h) - 1)) <<< h
  let p₃ := ((α₁ &&& (2 ^ (m - 2 * h) - 1)) * (x₁ &&& (2 ^ (m - 2 * h) - 1))) <<< (2 * h)
  (((((p₀ + p₁) &&& (2 ^ m - 1)) + p₂) &&& (2 ^ m - 1)) + p₃) &&& (2 ^ m - 1)

/-- Computes `(2 * α + 1) * x % 2 ^ w₀` using `halfMulMod (w₀ - 1)` so that every intermediate
quantity is strictly less than `2 ^ w₀` whenever `α < 2 ^ (w₀ - 1)` and `x < 2 ^ w₀`. -/
@[expose] def oddMulModWord (w₀ α x : ℕ) : ℕ :=
  let m := w₀ - 1
  let x' := x &&& (2 ^ m - 1)
  let p := halfMulMod m α x'
  (x &&& 1) + ((((x >>> 1) + p) &&& (2 ^ m - 1)) <<< 1)

theorem halfMulMod_lt (m α x' : ℕ) : halfMulMod m α x' < 2 ^ m := by
  dsimp only [halfMulMod]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by positivity)

theorem oddMulModWord_lt {w₀ : ℕ} (hw₀ : 0 < w₀) (α x : ℕ) :
    oddMulModWord w₀ α x < 2 ^ w₀ := by
  dsimp only [oddMulModWord]
  have hbit : x &&& 1 < 2 := by
    rw [Nat.and_two_pow_sub_one_eq_mod x 1]
    exact Nat.mod_lt x two_pos
  have hhigh : (((x >>> 1) + halfMulMod (w₀ - 1) α (x &&& (2 ^ (w₀ - 1) - 1))) &&&
      (2 ^ (w₀ - 1) - 1)) < 2 ^ (w₀ - 1) := by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hpow : 2 ^ w₀ = 2 * 2 ^ (w₀ - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hw₀, pow_succ']
  rw [Nat.shiftLeft_eq, pow_one, hpow]
  omega

/-- Exact modular correctness of `halfMulMod`: for all `m α x' : ℕ`, `halfMulMod m α x'` equals
`(α * x') % 2 ^ m`. -/
theorem halfMulMod_eq (m α x' : ℕ) :
    halfMulMod m α x' = (α * x') % 2 ^ m := by
  dsimp only [halfMulMod]
  set h := m / 2
  have h_le : h ≤ m := Nat.div_le_self m 2
  have h2_le : 2 * h ≤ m := Nat.mul_div_le m 2
  have hd_le : m - 2 * h ≤ 1 := by omega
  simp only [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  set α₀ := α % 2 ^ h
  set α₁ := α / 2 ^ h
  set x₀ := x' % 2 ^ h
  set x₁ := x' / 2 ^ h
  have hα : α = 2 ^ h * α₁ + α₀ := (Nat.div_add_mod α (2 ^ h)).symm
  have hx : x' = 2 ^ h * x₁ + x₀ := (Nat.div_add_mod x' (2 ^ h)).symm
  have hm1 : 2 ^ m = 2 ^ h * 2 ^ (m - h) := by rw [← pow_add, Nat.add_sub_of_le h_le]
  have hm2 : 2 ^ m = 2 ^ (2 * h) * 2 ^ (m - 2 * h) := by rw [← pow_add, Nat.add_sub_of_le h2_le]
  have hp1 : ((α₀ * x₁) % 2 ^ (m - h) * 2 ^ h) % 2 ^ m = (2 ^ h * (α₀ * x₁)) % 2 ^ m := by
    rw [mul_comm _ (2 ^ h), hm1, ← Nat.mul_mod_mul_left, Nat.mod_mod]
  have hp2 : ((α₁ * x₀) % 2 ^ (m - h) * 2 ^ h) % 2 ^ m = (2 ^ h * (α₁ * x₀)) % 2 ^ m := by
    rw [mul_comm _ (2 ^ h), hm1, ← Nat.mul_mod_mul_left, Nat.mod_mod]
  have hp3_mod : (α₁ % 2 ^ (m - 2 * h)) * (x₁ % 2 ^ (m - 2 * h)) =
      (α₁ * x₁) % 2 ^ (m - 2 * h) := by
    have hlt1 : α₁ % 2 ^ (m - 2 * h) < 2 ^ (m - 2 * h) := Nat.mod_lt _ (by positivity)
    have hlt2 : x₁ % 2 ^ (m - 2 * h) < 2 ^ (m - 2 * h) := Nat.mod_lt _ (by positivity)
    have hprod_lt : (α₁ % 2 ^ (m - 2 * h)) * (x₁ % 2 ^ (m - 2 * h)) < 2 ^ (m - 2 * h) := by
      rcases (by omega : m - 2 * h = 0 ∨ m - 2 * h = 1) with hd0 | hd1
      · rw [hd0, pow_zero] at hlt1 hlt2 ⊢
        have : α₁ % 1 = 0 := by omega
        rw [this, zero_mul]
        exact zero_lt_one
      · rw [hd1, pow_one] at hlt1 hlt2 ⊢
        rcases (by omega : α₁ % 2 = 0 ∨ α₁ % 2 = 1) with h0 | h1
        · rw [h0, zero_mul]; exact two_pos
        · rw [h1, one_mul]; exact hlt2
    rw [Nat.mul_mod, Nat.mod_eq_of_lt hprod_lt]
  have hp3 : ((α₁ % 2 ^ (m - 2 * h)) * (x₁ % 2 ^ (m - 2 * h)) * 2 ^ (2 * h)) % 2 ^ m =
      (2 ^ (2 * h) * (α₁ * x₁)) % 2 ^ m := by
    rw [hp3_mod, mul_comm _ (2 ^ (2 * h)), hm2, ← Nat.mul_mod_mul_left, Nat.mod_mod]
  have hs1 : (α₀ * x₀ % 2 ^ m + (α₀ * x₁ % 2 ^ (m - h) * 2 ^ h)) % 2 ^ m =
      (α₀ * x₀ + 2 ^ h * (α₀ * x₁)) % 2 ^ m := by
    rw [Nat.add_mod, Nat.mod_mod, hp1, ← Nat.add_mod]
  have hs2 : ((α₀ * x₀ + 2 ^ h * (α₀ * x₁)) % 2 ^ m + (α₁ * x₀ % 2 ^ (m - h) * 2 ^ h)) % 2 ^ m =
      (α₀ * x₀ + 2 ^ h * (α₀ * x₁) + 2 ^ h * (α₁ * x₀)) % 2 ^ m := by
    rw [Nat.add_mod, Nat.mod_mod, hp2, ← Nat.add_mod]
  have hs3 : ((α₀ * x₀ + 2 ^ h * (α₀ * x₁) + 2 ^ h * (α₁ * x₀)) % 2 ^ m +
      (α₁ % 2 ^ (m - 2 * h) * (x₁ % 2 ^ (m - 2 * h)) * 2 ^ (2 * h))) % 2 ^ m =
      (α₀ * x₀ + 2 ^ h * (α₀ * x₁) + 2 ^ h * (α₁ * x₀) + 2 ^ (2 * h) * (α₁ * x₁)) % 2 ^ m := by
    rw [Nat.add_mod, Nat.mod_mod, hp3, ← Nat.add_mod]
  rw [hs1, hs2, hs3]
  congr 1
  conv_rhs => rw [hα, hx]
  rw [two_mul, pow_add]
  ring

/-- Exact modular correctness of `oddMulModWord`: for all `0 < w₀`,
`oddMulModWord w₀ α x = (2 * α + 1) * x % 2 ^ w₀`. -/
theorem oddMulModWord_eq {w₀ : ℕ} (hw₀ : 0 < w₀) (α x : ℕ) :
    oddMulModWord w₀ α x = (2 * α + 1) * x % 2 ^ w₀ := by
  dsimp only [oddMulModWord]
  set m := w₀ - 1
  have hm : w₀ = m + 1 := (Nat.sub_add_cancel hw₀).symm
  have hmul_mod : α * (x % 2 ^ m) % 2 ^ m = (α * x) % 2 ^ m := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  rw [halfMulMod_eq, Nat.and_two_pow_sub_one_eq_mod x m, hmul_mod,
    Nat.and_two_pow_sub_one_eq_mod x 1, pow_one,
    Nat.and_two_pow_sub_one_eq_mod _ m, Nat.shiftRight_eq_div_pow x 1, pow_one,
    Nat.shiftLeft_eq, pow_one, Nat.add_mod_mod]
  have hx : x = x % 2 + 2 * (x / 2) := by
    have := Nat.div_add_mod x 2
    omega
  have hprod : (2 * α + 1) * x = x % 2 + 2 * (x / 2 + α * x) := by
    calc (2 * α + 1) * x = x + 2 * (α * x) := by ring
      _ = (x % 2 + 2 * (x / 2)) + 2 * (α * x) := by rw [← hx]
      _ = x % 2 + 2 * (x / 2 + α * x) := by ring
  have hpow : 2 ^ w₀ = 2 * 2 ^ m := by rw [hm, pow_succ']
  rw [hprod, hpow]
  have hdiv_mod := Nat.div_add_mod (x / 2 + α * x) (2 ^ m)
  have hrem_lt : x % 2 + ((x / 2 + α * x) % 2 ^ m) * 2 < 2 * 2 ^ m := by
    have h1 : x % 2 < 2 := Nat.mod_lt x two_pos
    have h2 : (x / 2 + α * x) % 2 ^ m < 2 ^ m := Nat.mod_lt _ (by positivity)
    omega
  have heq : x % 2 + 2 * (x / 2 + α * x) =
      (x % 2 + ((x / 2 + α * x) % 2 ^ m) * 2) + (2 * 2 ^ m) * ((x / 2 + α * x) / 2 ^ m) := by
    linarith
  rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem_lt]

/-- Shifting `oddMulModWord w₀ α.val u.val` right by `w₀ - R` computes
`(multiplyShiftReduced U w₀ R α u).val`. -/
theorem oddMulModWord_shiftRight_eq_multiplyShiftReduced {U w₀ R : ℕ} (hw₀ : 0 < w₀)
    (α : Fin (2 ^ (w₀ - 1))) (u : Fin U) :
    oddMulModWord w₀ α.val u.val >>> (w₀ - R) = (multiplyShiftReduced U w₀ R α u).val := by
  rw [oddMulModWord_eq hw₀, Nat.shiftRight_eq_div_pow, val_multiplyShiftReduced]

/-! ## Section 2: Limb parameters and bit-packed Four-Russians table bounds -/

/-- Limb bit-width `c = 3 ^ (t - 3)` for trinomial parameter `t`. -/
@[expose] def reducedChunkBits (t : ℕ) : ℕ :=
  3 ^ (t - 3)

/-- Half-field limb count `L₀ = 3 ^ min t 3 ≤ 27`, so `L₀ * c = 3 ^ t`. -/
@[expose] def reducedHalfLimbs (t : ℕ) : ℕ :=
  3 ^ min t 3

/-- Full-field limb count `L = 2 * L₀ = 2 * 3 ^ min t 3 ≤ 54`, so `L * c = 2 * 3 ^ t`. -/
@[expose] def reducedLimbCount (t : ℕ) : ℕ :=
  2 * reducedHalfLimbs t

theorem reducedChunkBits_pos (t : ℕ) : 0 < reducedChunkBits t := by
  dsimp only [reducedChunkBits]; positivity

theorem reducedHalfLimbs_pos (t : ℕ) : 0 < reducedHalfLimbs t := by
  dsimp only [reducedHalfLimbs]; positivity

theorem reducedLimbCount_pos (t : ℕ) : 0 < reducedLimbCount t := by
  dsimp only [reducedLimbCount, reducedHalfLimbs]; positivity

theorem reducedHalfLimbs_mul_chunkBits (t : ℕ) :
    reducedHalfLimbs t * reducedChunkBits t = 3 ^ t := by
  dsimp only [reducedHalfLimbs, reducedChunkBits]
  rw [← pow_add, show min t 3 + (t - 3) = t by omega]

theorem reducedLimbCount_mul_chunkBits (t : ℕ) :
    reducedLimbCount t * reducedChunkBits t = 2 * 3 ^ t := by
  dsimp only [reducedLimbCount]
  rw [Nat.mul_assoc, reducedHalfLimbs_mul_chunkBits]

theorem reducedHalfLimbs_le (t : ℕ) : reducedHalfLimbs t ≤ 27 := by
  dsimp only [reducedHalfLimbs]
  calc 3 ^ min t 3 ≤ 3 ^ 3 := Nat.pow_le_pow_right (by decide) (Nat.min_le_right t 3)
    _ = 27 := by decide

theorem reducedLimbCount_le (t : ℕ) : reducedLimbCount t ≤ 54 := by
  have := reducedHalfLimbs_le t
  dsimp only [reducedLimbCount]
  omega

/-- Whenever `w₀ ≤ w`, `b' ≤ w`, and `2 ≤ w`, `2 * reducedChunkBits (reducedTrinomialStep w₀ b b')`
fits in a single `w`-bit word (`≤ w`) unconditionally for all `b : ℕ`. -/
theorem two_mul_reducedChunkBits_le {w₀ b b' w : ℕ} (hw₀ : w₀ ≤ w) (hb' : b' ≤ w) (hw : 2 ≤ w) :
    2 * reducedChunkBits (reducedTrinomialStep w₀ b b') ≤ w := by
  set B := reducedTargetBits w₀ b b'
  set t := reducedTrinomialStep w₀ b b'
  have hB_le : B ≤ w := by
    dsimp only [B, reducedTargetBits]
    omega
  by_cases ht : t ≤ 3
  · have hc1 : reducedChunkBits t = 1 := by
      dsimp only [reducedChunkBits]
      rw [Nat.sub_eq_zero_of_le ht, pow_zero]
    omega
  · have hB2 : 2 < B := by
      by_contra hle
      push Not at hle
      have ht0 : t = 0 := by
        dsimp only [t, reducedTrinomialStep]
        rw [trinomialStepAux, ite_eq_left hle]
      omega
    obtain ⟨_, hlt⟩ := two_mul_three_pow_pred_lt_of_two_lt hB2
    have hpow : 3 ^ (t - 3) ≤ 3 ^ (t - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    dsimp only [reducedChunkBits]
    change 2 * 3 ^ (t - 1) < B at hlt
    omega

/-- Total number of bits `(2 * c) * 2 ^ (2 * c)` in the Four-Russians carryless multiplication
table for trinomial step `t`. -/
@[expose] def reducedTableBits (t : ℕ) : ℕ :=
  (2 * reducedChunkBits t) * 2 ^ (2 * reducedChunkBits t)

private theorem two_mul_le_two_pow (c : ℕ) : 2 * c ≤ 2 ^ c := by
  induction c with
  | zero => decide
  | succ c ih =>
    rcases eq_or_ne c 0 with rfl | hc
    · decide
    · rw [pow_succ']
      have : 2 ≤ 2 ^ c := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ c := Nat.pow_le_pow_right two_pos (Nat.one_le_iff_ne_zero.mpr hc)
      omega

/-- Whenever `b' ≤ 3 * b`, the Four-Russians table bit count satisfies
`reducedTableBits (reducedTrinomialStep w₀ b b') ≤ max 8 (2 ^ (b / 2)) = o(2 ^ b)`. -/
theorem reducedTableBits_le {w₀ b b' : ℕ} (hb' : b' ≤ 3 * b) :
    reducedTableBits (reducedTrinomialStep w₀ b b') ≤ max 8 (2 ^ (b / 2)) := by
  set B := reducedTargetBits w₀ b b'
  set t := reducedTrinomialStep w₀ b b'
  by_cases ht : t ≤ 3
  · have hc1 : reducedChunkBits t = 1 := by
      dsimp only [reducedChunkBits]
      rw [Nat.sub_eq_zero_of_le ht, pow_zero]
    dsimp only [reducedTableBits]
    rw [hc1]
    exact le_max_left 8 _
  · have hB2 : 2 < B := by
      by_contra hle
      push Not at hle
      have ht0 : t = 0 := by
        dsimp only [t, reducedTrinomialStep]
        rw [trinomialStepAux, ite_eq_left hle]
      omega
    obtain ⟨_, hlt⟩ := two_mul_three_pow_pred_lt_of_two_lt hB2
    change 2 * 3 ^ (t - 1) < B at hlt
    have hpow9 : 3 ^ (t - 1) = 9 * reducedChunkBits t := by
      dsimp only [reducedChunkBits]
      rw [show t - 1 = (t - 3) + 2 by omega, pow_add]
      ring
    have h18 : 18 * reducedChunkBits t < B := by linarith
    have hB_le : B ≤ max (3 * b) 1 := by
      dsimp only [B, reducedTargetBits]
      omega
    have hc_pos := reducedChunkBits_pos t
    have h3c : 3 * reducedChunkBits t ≤ b / 2 := by omega
    have htb : reducedTableBits t ≤ 2 ^ (3 * reducedChunkBits t) := by
      dsimp only [reducedTableBits]
      calc (2 * reducedChunkBits t) * 2 ^ (2 * reducedChunkBits t)
          ≤ 2 ^ reducedChunkBits t * 2 ^ (2 * reducedChunkBits t) :=
            Nat.mul_le_mul_right _ (two_mul_le_two_pow (reducedChunkBits t))
        _ = 2 ^ (3 * reducedChunkBits t) := by
            rw [← pow_add, show reducedChunkBits t + 2 * reducedChunkBits t =
              3 * reducedChunkBits t by ring]
    exact (htb.trans (Nat.pow_le_pow_right two_pos h3c)).trans (le_max_right 8 _)

/-- Log₂ of the number of `2 * c`-bit entries packed into each `w`-bit word:
`p = min (2 * c) ⌊log₂ (w / (2 * c))⌋`. -/
@[expose] def reducedPackShift (t w : ℕ) : ℕ :=
  min (2 * reducedChunkBits t) (Nat.log 2 (w / (2 * reducedChunkBits t)))

/-- Number of `w`-bit words `2 ^ (2 * c - p)` occupied by the bit-packed Four-Russians table. -/
@[expose] def reducedTableWords (t w : ℕ) : ℕ :=
  2 ^ (2 * reducedChunkBits t - reducedPackShift t w)

theorem reducedPackShift_le (t w : ℕ) :
    reducedPackShift t w ≤ 2 * reducedChunkBits t :=
  Nat.min_le_left _ _

theorem two_pow_reducedPackShift_mul_le {t w : ℕ} (hc : 2 * reducedChunkBits t ≤ w) :
    2 ^ reducedPackShift t w * (2 * reducedChunkBits t) ≤ w := by
  have hc_pos : 0 < 2 * reducedChunkBits t := by
    have := reducedChunkBits_pos t; omega
  have hdiv_pos : 0 < w / (2 * reducedChunkBits t) := Nat.div_pos hc hc_pos
  have hp_le : reducedPackShift t w ≤ Nat.log 2 (w / (2 * reducedChunkBits t)) :=
    Nat.min_le_right _ _
  calc 2 ^ reducedPackShift t w * (2 * reducedChunkBits t)
      ≤ 2 ^ Nat.log 2 (w / (2 * reducedChunkBits t)) * (2 * reducedChunkBits t) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos hp_le)
    _ ≤ (w / (2 * reducedChunkBits t)) * (2 * reducedChunkBits t) :=
        Nat.mul_le_mul_right _ (Nat.pow_log_le_self 2 (by omega))
    _ ≤ w := Nat.div_mul_le_self w _

/-- The bit-packed Four-Russians table uses at most `2 * reducedTableBits t / w + 1` words. -/
theorem reducedTableWords_le {t w : ℕ} (hc : 2 * reducedChunkBits t ≤ w) :
    reducedTableWords t w ≤ 2 * reducedTableBits t / w + 1 := by
  set c2 := 2 * reducedChunkBits t
  have hc2_pos : 0 < c2 := by have := reducedChunkBits_pos t; omega
  have hw_pos : 0 < w := lt_of_lt_of_le hc2_pos hc
  by_cases hle : c2 ≤ Nat.log 2 (w / c2)
  · have hp : reducedPackShift t w = c2 := Nat.min_eq_left hle
    dsimp only [reducedTableWords]
    rw [hp, Nat.sub_self, pow_zero]
    exact Nat.le_add_left 1 _
  · push Not at hle
    have hp : reducedPackShift t w = Nat.log 2 (w / c2) := Nat.min_eq_right (le_of_lt hle)
    have hp_le_c2 : reducedPackShift t w ≤ c2 := reducedPackShift_le t w
    have hlt_pow : w / c2 < 2 ^ (reducedPackShift t w + 1) := by
      rw [hp]
      exact Nat.lt_pow_succ_log_self one_lt_two (w / c2)
    have hw_lt : w ≤ 2 * c2 * 2 ^ reducedPackShift t w := by
      have h1 : w < (w / c2 + 1) * c2 := by
        have := Nat.div_add_mod w c2
        have := Nat.mod_lt w hc2_pos
        linarith
      have h2 : w / c2 + 1 ≤ 2 * 2 ^ reducedPackShift t w := by
        rw [pow_succ'] at hlt_pow
        omega
      calc w ≤ (w / c2 + 1) * c2 := le_of_lt h1
        _ ≤ (2 * 2 ^ reducedPackShift t w) * c2 := Nat.mul_le_mul_right c2 h2
        _ = 2 * c2 * 2 ^ reducedPackShift t w := by ring
    have hmul : w * reducedTableWords t w ≤ 2 * reducedTableBits t := by
      dsimp only [reducedTableWords, reducedTableBits]
      calc w * 2 ^ (c2 - reducedPackShift t w)
          ≤ (2 * c2 * 2 ^ reducedPackShift t w) * 2 ^ (c2 - reducedPackShift t w) :=
            Nat.mul_le_mul_right _ hw_lt
        _ = 2 * (c2 * (2 ^ reducedPackShift t w * 2 ^ (c2 - reducedPackShift t w))) := by ring
        _ = 2 * (c2 * 2 ^ c2) := by
            rw [← pow_add, Nat.add_sub_of_le hp_le_c2]
    have hdiv : reducedTableWords t w ≤ 2 * reducedTableBits t / w :=
      Nat.le_div_iff_mul_le hw_pos |>.mpr (by linarith)
    exact hdiv.trans (Nat.le_succ _)


/-! ## Section 3: Limb extraction, packing, and 4-block trinomial reduction on limbs -/

/-- Extract the `m`-th `c`-bit limb `(a >>> (m * c)) &&& (2 ^ c - 1)` of a natural number `a`. -/
@[expose] def getLimb (c a m : ℕ) : ℕ :=
  (a >>> (m * c)) &&& (2 ^ c - 1)

theorem getLimb_lt (c a m : ℕ) : getLimb c a m < 2 ^ c := by
  dsimp only [getLimb]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos c)

theorem getLimb_zero (c m : ℕ) : getLimb c 0 m = 0 := by
  simp [getLimb]

theorem testBit_getLimb (c a m k : ℕ) :
    (getLimb c a m).testBit k = (decide (k < c) && a.testBit (m * c + k)) := by
  dsimp only [getLimb]
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight, Bool.and_comm]

theorem getLimb_xor (c a b m : ℕ) :
    getLimb c (a ^^^ b) m = getLimb c a m ^^^ getLimb c b m := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_xor, testBit_getLimb, testBit_getLimb, testBit_getLimb, Nat.testBit_xor]
  cases decide (k < c) <;> simp

theorem getLimb_and_low {c a m s : ℕ} (hm : m < s) :
    getLimb c (a &&& (2 ^ (s * c) - 1)) m = getLimb c a m := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_getLimb, testBit_getLimb, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hk : k < c
  · have hlt : m * c + k < s * c := by
      calc m * c + k < m * c + c := Nat.add_lt_add_left hk _
        _ = (m + 1) * c := by ring
        _ ≤ s * c := Nat.mul_le_mul_right c hm
    simp [hk, hlt]
  · simp [hk]

theorem getLimb_and_high (c a : ℕ) {s m : ℕ} (hm : s ≤ m) :
    getLimb c (a &&& (2 ^ (s * c) - 1)) m = 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_getLimb, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.zero_testBit]
  have hle : s * c ≤ m * c := Nat.mul_le_mul_right c hm
  have hnot : ¬ (m * c + k < s * c) := by omega
  simp [hnot]

theorem getLimb_and_self (c a s : ℕ) :
    getLimb c (a &&& (2 ^ (s * c) - 1)) s = 0 :=
  getLimb_and_high c a le_rfl

theorem getLimb_shiftRight_mul (c a s m : ℕ) :
    getLimb c (a >>> (s * c)) m = getLimb c a (s + m) := by
  dsimp only [getLimb]
  rw [← Nat.shiftRight_add, ← Nat.add_mul]

theorem getLimb_shiftLeft_mul_low (c a : ℕ) {s m : ℕ} (hm : m < s) :
    getLimb c (a <<< (s * c)) m = 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_getLimb, Nat.testBit_shiftLeft, Nat.zero_testBit]
  by_cases hk : k < c
  · have hlt : m * c + k < s * c := by
      calc m * c + k < m * c + c := Nat.add_lt_add_left hk _
        _ = (m + 1) * c := by ring
        _ ≤ s * c := Nat.mul_le_mul_right c hm
    have hnot : ¬ (m * c + k ≥ s * c) := not_le.mpr hlt
    simp [hk, hnot]
  · simp [hk]

theorem getLimb_shiftLeft_mul_add (c a s m : ℕ) :
    getLimb c (a <<< (s * c)) (s + m) = getLimb c a m := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_getLimb, testBit_getLimb, Nat.testBit_shiftLeft]
  have hge : (s + m) * c + k ≥ s * c := by rw [Nat.add_mul]; omega
  have hsub : (s + m) * c + k - s * c = m * c + k := by rw [Nat.add_mul]; omega
  simp [hge, hsub]

theorem getLimb_xor_shiftLeft_self {c a val s : ℕ}
    (ha : a < 2 ^ (s * c)) (hval : val < 2 ^ c) :
    getLimb c (a ^^^ (val <<< (s * c))) s = val := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_getLimb, Nat.testBit_xor, Nat.testBit_shiftLeft]
  by_cases hk : k < c
  · have ha_false : a.testBit (s * c + k) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right two_pos (by omega)))
    have hge : s * c + k ≥ s * c := Nat.le_add_right _ _
    have hsub : s * c + k - s * c = k := Nat.add_sub_cancel_left _ _
    simp [hk, ha_false, hge, hsub]
  · have hval_false : val.testBit k = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hval (Nat.pow_le_pow_right two_pos (by omega)))
    simp [hk, hval_false]

theorem getLimb_xor_shiftLeft_of_ne {c a val s m : ℕ}
    (hval : val < 2 ^ c) (hne : m ≠ s) :
    getLimb c (a ^^^ (val <<< (s * c))) m = getLimb c a m := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_getLimb, testBit_getLimb, Nat.testBit_xor, Nat.testBit_shiftLeft]
  by_cases hk : k < c
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hlt_sc : m * c + k < s * c := by
        calc m * c + k < m * c + c := Nat.add_lt_add_left hk _
          _ = (m + 1) * c := by ring
          _ ≤ s * c := Nat.mul_le_mul_right c hlt
      have hnot_ge : ¬ (m * c + k ≥ s * c) := not_le.mpr hlt_sc
      simp [hk, hnot_ge]
    · have hge_sc : m * c + k ≥ s * c := by
        have : s * c ≤ m * c := Nat.mul_le_mul_right c (le_of_lt hgt)
        omega
      have hsub_ge : c ≤ m * c + k - s * c := by
        have : (s + 1) * c ≤ m * c := Nat.mul_le_mul_right c hgt
        have : s * c + c ≤ m * c := by linarith
        omega
      have hval_false : val.testBit (m * c + k - s * c) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hval (Nat.pow_le_pow_right two_pos hsub_ge))
      simp [hk, hge_sc, hval_false]
  · simp [hk]

/-- Bitwise decomposition of `idx < 2 ^ (2 * c)` into word index `idx >>> p < 2 ^ (2 * c - p)` and
within-word entry index `idx &&& (2 ^ p - 1) < 2 ^ p` for `p = reducedPackShift t w`. -/
theorem reducedPackIndex_props {t w idx : ℕ} (hidx : idx < 2 ^ (2 * reducedChunkBits t)) :
    let p := reducedPackShift t w
    idx >>> p < reducedTableWords t w ∧
    idx &&& (2 ^ p - 1) < 2 ^ p := by
  intro p
  have hp_le : p ≤ 2 * reducedChunkBits t := reducedPackShift_le t w
  refine ⟨?_, ?_⟩
  · dsimp only [reducedTableWords]
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    rwa [← pow_add, Nat.add_sub_of_le hp_le]
  · rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt idx (Nat.two_pow_pos p)

/-- Pack `n` limbs `f 0, …, f (n - 1)` of `c` bits each into a single natural number
`< 2 ^ (n * c)`. -/
@[expose] def packLimbs (c : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => packLimbs c n f ^^^ ((f n &&& (2 ^ c - 1)) <<< (n * c))

theorem packLimbs_congr {c n : ℕ} {f g : ℕ → ℕ} (h : ∀ i < n, f i = g i) :
    packLimbs c n f = packLimbs c n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [packLimbs]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem packLimbs_lt (c n : ℕ) (f : ℕ → ℕ) :
    packLimbs c n f < 2 ^ (n * c) := by
  induction n with
  | zero => simp [packLimbs]
  | succ n ih =>
    dsimp only [packLimbs]
    have h1 : packLimbs c n f < 2 ^ ((n + 1) * c) :=
      lt_of_lt_of_le ih (Nat.pow_le_pow_right two_pos (by rw [Nat.succ_mul]; omega))
    have h2 : (f n &&& (2 ^ c - 1)) <<< (n * c) < 2 ^ ((n + 1) * c) := by
      have hand : f n &&& (2 ^ c - 1) < 2 ^ c := by
        rw [Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (Nat.two_pow_pos c)
      rw [Nat.shiftLeft_eq, Nat.succ_mul, Nat.add_comm (n * c) c, pow_add]
      exact Nat.mul_lt_mul_of_pos_right hand (Nat.two_pow_pos (n * c))
    exact Nat.xor_lt_two_pow h1 h2

theorem getLimb_packLimbs (c : ℕ) {n m : ℕ} (f : ℕ → ℕ) (hm : m < n) :
    getLimb c (packLimbs c n f) m = f m &&& (2 ^ c - 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    dsimp only [packLimbs]
    have hand_lt : f n &&& (2 ^ c - 1) < 2 ^ c := by
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos c)
    rcases eq_or_ne m n with rfl | hne
    · exact getLimb_xor_shiftLeft_self (packLimbs_lt c m f) hand_lt
    · rw [getLimb_xor_shiftLeft_of_ne hand_lt hne]
      exact ih (by omega)

theorem getLimb_packLimbs_of_lt (c : ℕ) {n m : ℕ} {f : ℕ → ℕ}
    (hm : m < n) (hf : f m < 2 ^ c) :
    getLimb c (packLimbs c n f) m = f m := by
  rw [getLimb_packLimbs c f hm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hf]

theorem getLimb_packLimbs_of_ge (c : ℕ) {n m : ℕ} (f : ℕ → ℕ) (hm : n ≤ m) :
    getLimb c (packLimbs c n f) m = 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_getLimb, Nat.zero_testBit]
  have hlt : packLimbs c n f < 2 ^ (m * c + k) :=
    lt_of_lt_of_le (packLimbs_lt c n f) (Nat.pow_le_pow_right two_pos (by
      have : n * c ≤ m * c := Nat.mul_le_mul_right c hm
      omega))
  rw [Nat.testBit_lt_two_pow hlt, Bool.and_false]

theorem eq_of_getLimb_eq {c : ℕ} (hc : 0 < c) {a b : ℕ}
    (h : ∀ m, getLimb c a m = getLimb c b m) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro idx
  have hm := congrArg (fun x => x.testBit (idx % c)) (h (idx / c))
  have hmod : idx % c < c := Nat.mod_lt idx hc
  have hdiv : (idx / c) * c + idx % c = idx := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod idx c
  simpa only [testBit_getLimb, hmod, decide_true, Bool.true_and, hdiv] using hm

theorem packLimbs_getLimb {c : ℕ} (hc : 0 < c) (n : ℕ) {a : ℕ} (ha : a < 2 ^ (n * c)) :
    packLimbs c n (getLimb c a) = a := by
  apply eq_of_getLimb_eq hc
  intro m
  by_cases hm : m < n
  · exact getLimb_packLimbs_of_lt c hm (getLimb_lt c a m)
  · push Not at hm
    rw [getLimb_packLimbs_of_ge c _ hm]
    apply (Nat.eq_of_testBit_eq fun k => ?_).symm
    rw [testBit_getLimb, Nat.zero_testBit]
    have hlt : a < 2 ^ (m * c + k) :=
      lt_of_lt_of_le ha (Nat.pow_le_pow_right two_pos (by
        have : n * c ≤ m * c := Nat.mul_le_mul_right c hm
        omega))
    rw [Nat.testBit_lt_two_pow hlt, Bool.and_false]

theorem packLimbs_xor {c : ℕ} (hc : 0 < c) (n : ℕ) (f g : ℕ → ℕ) :
    packLimbs c n (fun i => f i ^^^ g i) = packLimbs c n f ^^^ packLimbs c n g := by
  apply eq_of_getLimb_eq hc
  intro m
  rw [getLimb_xor]
  by_cases hm : m < n
  · rw [getLimb_packLimbs c _ hm, getLimb_packLimbs c f hm, getLimb_packLimbs c g hm]
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and]
    cases (2 ^ c - 1).testBit k <;> simp
  · push Not at hm
    rw [getLimb_packLimbs_of_ge c _ hm, getLimb_packLimbs_of_ge c f hm,
      getLimb_packLimbs_of_ge c g hm, Nat.xor_zero]

theorem getLimb_zero_of_lt {c val : ℕ} (hval : val < 2 ^ c) :
    getLimb c val 0 = val := by
  dsimp only [getLimb]
  rw [Nat.zero_mul, Nat.shiftRight_zero, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hval]

theorem packLimbs_update_xor {c : ℕ} (hc : 0 < c) {n i v : ℕ} (f : ℕ → ℕ)
    (hi : i < n) (hv : v < 2 ^ c) :
    packLimbs c n (Function.update f i (f i ^^^ v)) =
      packLimbs c n f ^^^ (v <<< (i * c)) := by
  apply eq_of_getLimb_eq hc
  intro m
  by_cases hm : m < n
  · rw [getLimb_packLimbs c _ hm]
    rcases eq_or_ne m i with rfl | hne
    · rw [Function.update_self, getLimb_xor, getLimb_packLimbs c f hm]
      have hsh : getLimb c (v <<< (m * c)) m = v := by
        simpa only [Nat.add_zero] using
          (getLimb_shiftLeft_mul_add c v m 0).trans (getLimb_zero_of_lt hv)
      rw [hsh]
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_and,
        Nat.testBit_two_pow_sub_one]
      by_cases hk : k < c
      · simp [hk]
      · have hv_false : v.testBit k = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right two_pos (by omega)))
        simp [hk, hv_false]
    · rw [Function.update_of_ne hne, getLimb_xor_shiftLeft_of_ne hv hne,
        getLimb_packLimbs c f hm]
  · push Not at hm
    have hne : m ≠ i := by omega
    rw [getLimb_packLimbs_of_ge c _ hm, getLimb_xor_shiftLeft_of_ne hv hne,
      getLimb_packLimbs_of_ge c f hm]

/-- Updating two consecutive limbs `i` and `i + 1` of `f` by XORing `v &&& (2 ^ c - 1)` and
`v >>> c` (where `v < 2 ^ (2 * c)`) XORs `packLimbs c n f` with `v <<< (i * c)`. -/
theorem packLimbs_update_pair {c : ℕ} (hc : 0 < c) {n i v : ℕ} (f : ℕ → ℕ)
    (hi : i + 1 < n) (hv : v < 2 ^ (2 * c)) :
    packLimbs c n
      (Function.update (Function.update f i (f i ^^^ (v &&& (2 ^ c - 1))))
        (i + 1) (f (i + 1) ^^^ (v >>> c))) =
      packLimbs c n f ^^^ (v <<< (i * c)) := by
  have hv_lo : v &&& (2 ^ c - 1) < 2 ^ c := by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (Nat.two_pow_pos c)
  have hv_hi : v >>> c < 2 ^ c := by
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    rwa [← pow_add, ← two_mul]
  let g := Function.update f i (f i ^^^ (v &&& (2 ^ c - 1)))
  have hg : f (i + 1) = g (i + 1) :=
    (Function.update_of_ne (by omega : i + 1 ≠ i) _ f).symm
  have hupd : Function.update g (i + 1) (f (i + 1) ^^^ (v >>> c)) =
      Function.update g (i + 1) (g (i + 1) ^^^ (v >>> c)) := by
    rw [hg]
  rw [show Function.update (Function.update f i (f i ^^^ (v &&& (2 ^ c - 1))))
      (i + 1) (f (i + 1) ^^^ (v >>> c)) =
      Function.update g (i + 1) (g (i + 1) ^^^ (v >>> c)) from hupd,
    packLimbs_update_xor hc g hi hv_hi,
    packLimbs_update_xor hc f (Nat.lt_of_succ_lt hi) hv_lo, Nat.xor_assoc]
  congr 1
  rw [Nat.succ_mul, Nat.add_comm (i * c) c, Nat.shiftLeft_add _ c (i * c),
    ← Nat.shiftLeft_xor_distrib, and_xor_shiftRight_shiftLeft]

/-- Low-half limb formula (`m < L₀`) for `reduceTrinomialCode t P`. -/
theorem getLimb_reduceTrinomialCode_low (t P : ℕ) {m : ℕ} (hm : m < reducedHalfLimbs t) :
    let c := reducedChunkBits t
    let L₀ := reducedHalfLimbs t
    getLimb c (reduceTrinomialCode t P) m =
      (getLimb c P m ^^^ getLimb c P (3 * L₀ + m)) ^^^ getLimb c P (2 * L₀ + m) := by
  intro c L₀
  have h1 : 3 ^ t = L₀ * c := (reducedHalfLimbs_mul_chunkBits t).symm
  have h2 : 2 * 3 ^ t = (2 * L₀) * c := by rw [h1]; ring
  have h3 : 3 * 3 ^ t = (3 * L₀) * c := by rw [h1]; ring
  dsimp only [reduceTrinomialCode]
  rw [h3, h2, h1, getLimb_xor, getLimb_xor, getLimb_xor,
    getLimb_and_low (by omega : m < 2 * L₀),
    getLimb_shiftRight_mul,
    getLimb_and_low hm,
    getLimb_shiftRight_mul,
    getLimb_shiftLeft_mul_low c _ hm, Nat.xor_zero]

/-- High-half limb formula (`m < L₀`, limb index `L₀ + m`) for `reduceTrinomialCode t P`. -/
theorem getLimb_reduceTrinomialCode_high (t P : ℕ) {m : ℕ} (hm : m < reducedHalfLimbs t) :
    let c := reducedChunkBits t
    let L₀ := reducedHalfLimbs t
    getLimb c (reduceTrinomialCode t P) (L₀ + m) =
      (getLimb c P (L₀ + m) ^^^ getLimb c P (4 * L₀ + m)) ^^^ getLimb c P (2 * L₀ + m) := by
  intro c L₀
  have h1 : 3 ^ t = L₀ * c := (reducedHalfLimbs_mul_chunkBits t).symm
  have h2 : 2 * 3 ^ t = (2 * L₀) * c := by rw [h1]; ring
  have h3 : 3 * 3 ^ t = (3 * L₀) * c := by rw [h1]; ring
  dsimp only [reduceTrinomialCode]
  rw [h3, h2, h1, getLimb_xor, getLimb_xor, getLimb_xor,
    getLimb_and_low (by omega : L₀ + m < 2 * L₀),
    getLimb_shiftRight_mul,
    getLimb_and_high c _ (Nat.le_add_right L₀ m), Nat.xor_zero,
    getLimb_shiftLeft_mul_add,
    getLimb_and_low hm,
    getLimb_shiftRight_mul,
    show 3 * L₀ + (L₀ + m) = 4 * L₀ + m by ring]

/-- Equivalence between `L`-tuples of `c`-bit limbs `Fin L → Fin (2 ^ c)` and
`Fin (2 ^ (L * c))`. -/
@[expose] def limbsEquivFin (c L : ℕ) (hc : 0 < c) :
    (Fin L → Fin (2 ^ c)) ≃ Fin (2 ^ (L * c)) where
  toFun f :=
    ⟨packLimbs c L (fun i => if h : i < L then (f ⟨i, h⟩).val else 0), packLimbs_lt c L _⟩
  invFun a i :=
    ⟨getLimb c a.val i.val, getLimb_lt c a.val i.val⟩
  left_inv f := by
    funext i
    ext
    dsimp only
    rw [getLimb_packLimbs_of_lt c i.isLt (by simp [i.isLt, (f i).isLt])]
    simp [i.isLt]
  right_inv a := by
    ext
    dsimp only
    have hcongr : packLimbs c L (fun i => if h : i < L then getLimb c a.val i else 0) =
        packLimbs c L (getLimb c a.val) :=
      packLimbs_congr fun i hi => dite_eq_left hi
    rw [hcongr, packLimbs_getLimb hc L a.isLt]

/-- Low `n` limbs `a &&& (2 ^ (n * c) - 1)` of a natural number `a`. -/
@[expose] def truncLimbs (c n a : ℕ) : ℕ :=
  a &&& (2 ^ (n * c) - 1)

@[simp]
theorem truncLimbs_zero (c a : ℕ) : truncLimbs c 0 a = 0 := by
  simp [truncLimbs]

theorem truncLimbs_of_lt {c n a : ℕ} (ha : a < 2 ^ (n * c)) :
    truncLimbs c n a = a := by
  dsimp only [truncLimbs]
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt ha]

theorem truncLimbs_succ (c n a : ℕ) :
    truncLimbs c (n + 1) a = truncLimbs c n a ^^^ (getLimb c a n <<< (n * c)) := by
  apply Nat.eq_of_testBit_eq
  intro idx
  dsimp only [truncLimbs, getLimb]
  rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_sub_one,
    Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftLeft,
    Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight]
  by_cases h1 : idx < n * c
  · have h2 : idx < (n + 1) * c := by rw [Nat.succ_mul]; omega
    have hnot : ¬ (idx ≥ n * c) := not_le.mpr h1
    simp [h1, h2, hnot]
  · have hge : idx ≥ n * c := le_of_not_gt h1
    by_cases h2 : idx < (n + 1) * c
    · have hsub : idx - n * c < c := by rw [Nat.succ_mul] at h2; omega
      have hadd : n * c + (idx - n * c) = idx := Nat.add_sub_of_le hge
      simp [h1, h2, hge, hsub, hadd]
    · have hsub : ¬ (idx - n * c < c) := by rw [Nat.succ_mul] at h2; omega
      simp [h1, h2, hge, hsub]

theorem clmul_truncLimbs_right_succ (c i m xc x : ℕ) :
    clmul xc (truncLimbs c (m + 1) x) <<< (i * c) =
      (clmul xc (truncLimbs c m x) <<< (i * c)) ^^^
        (clmul xc (getLimb c x m) <<< ((i + m) * c)) := by
  rw [truncLimbs_succ, clmul_xor_right, clmul_shiftLeft_right, Nat.shiftLeft_xor_distrib]
  congr 1
  rw [Nat.add_mul, Nat.add_comm (i * c) (m * c), Nat.shiftLeft_add]

theorem clmul_truncLimbs_left_succ (c i a x : ℕ) :
    clmul (truncLimbs c (i + 1) a) x =
      clmul (truncLimbs c i a) x ^^^ (clmul (getLimb c a i) x <<< (i * c)) := by
  rw [truncLimbs_succ, clmul_xor_left, clmul_shiftLeft_left]

/-- Mask `2 ^ min c (b' - m * c) - 1` for extracting the `< b'` bits of limb `m`. -/
@[expose] def reducedOutMask (c b' m : ℕ) : ℕ :=
  2 ^ min c (b' - m * c) - 1

/-- Shift `if m * c < b' then m * c else 0` for placing limb `m` into the `< b'` output word. -/
@[expose] def reducedOutShift (c b' m : ℕ) : ℕ :=
  if m * c < b' then m * c else 0

theorem reducedOutMask_lt (c b' m : ℕ) : reducedOutMask c b' m < 2 ^ c := by
  dsimp only [reducedOutMask]
  have hle : 2 ^ min c (b' - m * c) ≤ 2 ^ c :=
    Nat.pow_le_pow_right two_pos (Nat.min_le_left _ _)
  have hpos : 0 < 2 ^ min c (b' - m * c) := Nat.two_pow_pos _
  omega

theorem reducedOutShift_le (c b' m : ℕ) : reducedOutShift c b' m ≤ b' := by
  dsimp only [reducedOutShift]
  split_ifs with h
  · exact le_of_lt h
  · exact Nat.zero_le b'

theorem and_reducedOutMask_shiftLeft_lt (c b' m v : ℕ) :
    (v &&& reducedOutMask c b' m) <<< reducedOutShift c b' m < 2 ^ max b' 1 := by
  dsimp only [reducedOutMask, reducedOutShift]
  split_ifs with h
  · have hand : v &&& (2 ^ min c (b' - m * c) - 1) < 2 ^ (b' - m * c) := by
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le
        (Nat.pow_le_pow_right two_pos (Nat.min_le_right _ _))
    rw [Nat.shiftLeft_eq]
    calc (v &&& (2 ^ min c (b' - m * c) - 1)) * 2 ^ (m * c)
        < 2 ^ (b' - m * c) * 2 ^ (m * c) :=
          Nat.mul_lt_mul_of_pos_right hand (Nat.two_pow_pos _)
      _ = 2 ^ b' := by rw [← pow_add, Nat.sub_add_cancel (le_of_lt h)]
      _ ≤ 2 ^ max b' 1 := Nat.pow_le_pow_right two_pos (le_max_left b' 1)
  · have hmin : min c (b' - m * c) = 0 := by omega
    rw [hmin]
    simp

theorem packLimbs_and_mask_succ (c b' n : ℕ) (f : ℕ → ℕ) :
    (packLimbs c (n + 1) f) &&& (2 ^ b' - 1) =
      ((packLimbs c n f) &&& (2 ^ b' - 1)) ^^^
        ((f n &&& reducedOutMask c b' n) <<< reducedOutShift c b' n) := by
  dsimp only [packLimbs, reducedOutMask, reducedOutShift]
  apply Nat.eq_of_testBit_eq
  intro idx
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_xor,
    Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_sub_one,
    Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_two_pow_sub_one,
    Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  split_ifs with hlt
  · by_cases hge : idx ≥ n * c
    · by_cases hb : idx < b'
      · have hmin : (idx - n * c < min c (b' - n * c)) ↔ (idx - n * c < c) := by omega
        simp [hge, hb, hmin]
      · have hnot : ¬ (idx - n * c < min c (b' - n * c)) := by omega
        simp [hge, hb, hnot]
    · simp [hge]
  · have hmin0 : min c (b' - n * c) = 0 := by omega
    by_cases hb : idx < b'
    · have hnot_ge : ¬ (idx ≥ n * c) := by omega
      simp [hb, hnot_ge, hmin0]
    · simp [hb, hmin0]

theorem shiftRight_lt_reducedTableWords {t w idx : ℕ}
    (hidx : idx < 2 ^ (2 * reducedChunkBits t)) :
    idx >>> reducedPackShift t w < reducedTableWords t w := by
  dsimp only [reducedTableWords]
  rw [Nat.shiftRight_eq_div_pow]
  apply Nat.div_lt_of_lt_mul
  rw [← pow_add, Nat.add_sub_of_le (reducedPackShift_le t w)]
  exact hidx

theorem shiftRight_add_one_le (idx p : ℕ) :
    (idx + 1) >>> p ≤ (idx >>> p) + 1 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have h1 : idx + 1 ≤ idx + 2 ^ p := Nat.add_le_add_left Nat.one_le_two_pow idx
  calc (idx + 1) / 2 ^ p ≤ (idx + 2 ^ p) / 2 ^ p := Nat.div_le_div_right h1
    _ = idx / 2 ^ p + 1 := Nat.add_div_right idx (Nat.two_pow_pos p)

theorem and_lt_of_lt_of_shiftRight_eq {i idx p : ℕ}
    (hlt : i < idx) (heq : i >>> p = idx >>> p) :
    i &&& (2 ^ p - 1) < idx &&& (2 ^ p - 1) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at heq
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
  have hi := Nat.div_add_mod i (2 ^ p)
  have hidx := Nat.div_add_mod idx (2 ^ p)
  rw [heq] at hi
  omega

theorem two_pow_two_mul_chunkBits_shiftRight (t w : ℕ) :
    2 ^ (2 * reducedChunkBits t) >>> reducedPackShift t w = reducedTableWords t w := by
  dsimp only [reducedTableWords]
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.pow_div (reducedPackShift_le t w) two_pos

theorem xor_shiftLeft_lt_two_pow {c s a v : ℕ}
    (ha : a < 2 ^ (s * c)) (hv : v < 2 ^ c) :
    a ^^^ (v <<< (s * c)) < 2 ^ ((s + 1) * c) := by
  have ha' : a < 2 ^ ((s + 1) * c) :=
    ha.trans_le (Nat.pow_le_pow_right two_pos (by rw [Nat.succ_mul]; omega))
  have hv' : v <<< (s * c) < 2 ^ ((s + 1) * c) := by
    rw [Nat.shiftLeft_eq, Nat.succ_mul, pow_add, mul_comm]
    exact Nat.mul_lt_mul_of_pos_left hv (Nat.two_pow_pos _)
  exact Nat.xor_lt_two_pow ha' hv'

/-- Ascending Horner prefix over `TrinomialField t`, processing coefficients from `k - 1` down to
`k - n` as `n` goes from `0` to `k`. -/
@[expose] noncomputable def hornerPrefix (t k : ℕ)
    (c_field : Fin k → TrinomialField t) (x_field : TrinomialField t) : ℕ → TrinomialField t
  | 0 => 0
  | n + 1 =>
    if h : n < k then
      hornerPrefix t k c_field x_field n * x_field + c_field ⟨k - 1 - n, by omega⟩
    else
      hornerPrefix t k c_field x_field n

theorem hornerPrefix_succ_of_lt {t k n : ℕ} (hn : n < k)
    (c_field : Fin k → TrinomialField t) (x_field : TrinomialField t) :
    hornerPrefix t k c_field x_field (n + 1) =
      hornerPrefix t k c_field x_field n * x_field + c_field ⟨k - 1 - n, by omega⟩ := by
  simp [hornerPrefix, hn]

theorem hornerPrefix_eq_sum {t k : ℕ}
    (c_field : Fin k → TrinomialField t) (x_field : TrinomialField t) :
    ∀ (n : ℕ) (hn : n ≤ k),
      hornerPrefix t k c_field x_field n =
        ∑ i : Fin n,
          c_field ⟨k - 1 - i.val, by have := i.isLt; omega⟩ * x_field ^ (n - 1 - i.val) := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [hornerPrefix]
  | succ n ih =>
    intro hn
    have hlt : n < k := Nat.lt_of_succ_le hn
    rw [hornerPrefix_succ_of_lt hlt, ih (le_of_lt hlt), Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    congr 1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hexp : n - i.val = (n - 1 - i.val) + 1 := by have := i.isLt; omega
    rw [hexp, pow_succ, mul_assoc]

theorem hornerPrefix_self_eq_polynomialHash {t k : ℕ}
    (c_field : Fin k → TrinomialField t) (x_field : TrinomialField t) :
    hornerPrefix t k c_field x_field k = polynomialHash c_field x_field := by
  rw [hornerPrefix_eq_sum c_field x_field k le_rfl]
  dsimp only [polynomialHash]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  have hrev : k - 1 - i.val = (Fin.revPerm i).val := by
    change k - 1 - i.val = (Fin.rev i).val
    rw [Fin.val_rev]
    omega
  have hfin : (⟨k - 1 - i.val, by have := i.isLt; omega⟩ : Fin k) = Fin.revPerm i :=
    Fin.ext hrev
  rw [hfin, hrev]

end Cslib.Probability
