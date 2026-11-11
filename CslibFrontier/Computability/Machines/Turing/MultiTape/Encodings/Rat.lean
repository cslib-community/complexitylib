/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Mathlib.Data.Rat.Init
import CslibFrontier.Foundations.Data.Nat.BinarySize
import CslibFrontier.Foundations.Data.Rat.Basic
import Mathlib.Data.Rat.Lemmas

/-!
# Binary encoding of rational numbers

`Turing.MultiTapeTM.encRat` encodes a rational number `q : ℚ` as its framed pair
`(q.num, q.den) : ℤ × ℕ` using `Turing.MultiTapeTM.encIntBin` and `Turing.MultiTapeTM.encNat`.

## Main definitions

* `Turing.MultiTapeTM.encRatData`: framed pair encoding of `(ℤ × ℕ)` used for rationals.
* `Turing.MultiTapeTM.encRat`: binary encoding of `ℚ` via `(q.num, q.den)`.

## Main results

* `Turing.MultiTapeTM.encRat_apply`: unfolding of `encRat q`.
* `Turing.MultiTapeTM.length_encRat`, `Turing.MultiTapeTM.length_encRat_le`: exact encoded bit
  length of `encRat q` and upper bound from numerator/denominator sizes.
* `Turing.MultiTapeTM.length_encRat_num_le`: `(encIntBin q.num).length ≤ (encRat q).length`.
* `Turing.MultiTapeTM.length_encRat_den_le`: `(encNat q.den).length ≤ (encRat q).length`.
* `Turing.MultiTapeTM.natAbs_num_lt_two_pow_length_encRat`,
  `Turing.MultiTapeTM.den_lt_two_pow_length_encRat`: numerator/denominator magnitude bounds.
* `Turing.MultiTapeTM.length_encRat_divInt_le`, `Turing.MultiTapeTM.length_encRat_neg`,
  `Turing.MultiTapeTM.length_encRat_inv_le`, `Turing.MultiTapeTM.length_encRat_mul_le`,
  `Turing.MultiTapeTM.length_encRat_add_le`, `Turing.MultiTapeTM.length_encRat_sub_le`,
  `Turing.MultiTapeTM.length_encRat_div_le`: encoded length bounds for rational arithmetic.
-/

public section

namespace Turing.MultiTapeTM

/-- Binary encoding of rational numerator-denominator pairs `(q.num, q.den)`. -/
abbrev encRatData : ℤ × ℕ ↪ List Bool :=
  encPair encIntBin encNat

/-- Binary encoding of rational numbers `ℚ` as `(q.num, q.den)`. -/
@[expose] def encRat : ℚ ↪ List Bool where
  toFun q := encRatData (q.num, q.den)
  inj' _ _ h :=
    Rat.ext (congrArg Prod.fst (encRatData.injective h))
      (congrArg Prod.snd (encRatData.injective h))

@[simp]
theorem encRat_apply (q : ℚ) : encRat q = encRatData (q.num, q.den) := rfl

/-- Exact encoded bit length of `encRat q`. -/
theorem length_encRat (q : ℚ) :
    (encRat q).length = 2 * q.num.natAbs.size + q.den.size + 3 := by
  rw [encRat_apply, encRatData, length_encPair, length_encIntBin, encNat_apply,
    Nat.size_eq_bits_len]
  dsimp only
  omega

/-- Every encoded rational uses at least `4` bits. -/
theorem four_le_length_encRat (q : ℚ) : 4 ≤ (encRat q).length := by
  rw [length_encRat]
  have hden : 1 ≤ q.den.size := Nat.size_pos.mpr q.pos
  omega

theorem length_encRat_num_le (q : ℚ) : (encIntBin q.num).length ≤ (encRat q).length :=
  length_le_encPair_left encIntBin encNat (q.num, q.den)

theorem length_encRat_den_le (q : ℚ) : (encNat q.den).length ≤ (encRat q).length :=
  length_le_encPair_right encIntBin encNat (q.num, q.den)

/-- Upper bound on `(encRat q).length` in terms of `|q.num|` and `q.den` binary sizes. -/
theorem length_encRat_le (q : ℚ) {A B : ℕ} (hnum : q.num.natAbs ≤ A) (hden : q.den ≤ B) :
    (encRat q).length ≤ 2 * A.size + B.size + 3 := by
  rw [length_encRat]
  have hn : q.num.natAbs.size ≤ A.size := Nat.size_le_size hnum
  have hd : q.den.size ≤ B.size := Nat.size_le_size hden
  omega

/-- The numerator magnitude of `q` is strictly below `2 ^ (encRat q).length`. -/
theorem natAbs_num_lt_two_pow_length_encRat (q : ℚ) :
    q.num.natAbs < 2 ^ (encRat q).length := by
  refine (Nat.lt_size_self q.num.natAbs).trans_le ?_
  refine Nat.pow_le_pow_right (by omega) ?_
  have hnum := length_encRat_num_le q
  rw [length_encIntBin] at hnum
  omega

/-- The denominator of `q` is strictly below `2 ^ (encRat q).length`. -/
theorem den_lt_two_pow_length_encRat (q : ℚ) : q.den < 2 ^ (encRat q).length := by
  refine (Nat.lt_size_self q.den).trans_le ?_
  refine Nat.pow_le_pow_right (by omega) ?_
  have hden := length_encRat_den_le q
  rw [encNat_apply, Nat.size_eq_bits_len] at hden
  exact hden

/-- Encoded length of `Rat.divInt a b` in terms of the binary lengths of `a` and `b`. -/
theorem length_encRat_divInt_le (a b : ℤ) :
    (encRat (Rat.divInt a b)).length ≤ 2 * (encIntBin a).length + (encIntBin b).length + 1 := by
  rw [length_encRat, length_encIntBin, length_encIntBin]
  by_cases hb : b = 0
  · subst hb
    simp [Nat.size_zero]
  · have hnum : (Rat.divInt a b).num.natAbs.size ≤ a.natAbs.size :=
      Nat.size_le_size (Rat.natAbs_num_divInt_le a b hb)
    have hden : (Rat.divInt a b).den.size ≤ b.natAbs.size :=
      Nat.size_le_size (Rat.den_divInt_le a b hb)
    omega

/-- Negation preserves the encoded length of a rational number. -/
theorem length_encRat_neg (q : ℚ) : (encRat (-q)).length = (encRat q).length := by
  simp only [length_encRat, Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den, Int.natAbs_neg]

/-- Encoded length of `q⁻¹` is at most twice that of `q`. -/
theorem length_encRat_inv_le (q : ℚ) : (encRat q⁻¹).length ≤ 2 * (encRat q).length := by
  rw [length_encRat, length_encRat]
  have hnum : q⁻¹.num.natAbs.size ≤ q.den.size := Nat.size_le_size (Rat.natAbs_num_inv_le q)
  have hden : q⁻¹.den.size ≤ max q.num.natAbs.size 1 := by
    refine (Nat.size_le_size (Rat.den_inv_le q)).trans ?_
    by_cases h0 : q.num.natAbs = 0
    · simp [h0]
    · simp [Nat.max_eq_left (Nat.pos_of_ne_zero h0)]
  omega

/-- Encoded length of `a * b` is at most `(encRat a).length + (encRat b).length`. -/
theorem length_encRat_mul_le (a b : ℚ) :
    (encRat (a * b)).length ≤ (encRat a).length + (encRat b).length := by
  rw [length_encRat, length_encRat, length_encRat]
  have hnum : (a * b).num.natAbs.size ≤ a.num.natAbs.size + b.num.natAbs.size :=
    (Nat.size_le_size (Rat.natAbs_num_mul_le a b)).trans (Nat.size_mul_le _ _)
  have hden : (a * b).den.size ≤ a.den.size + b.den.size :=
    (Nat.size_le_size (Rat.den_mul_le a b)).trans (Nat.size_mul_le _ _)
  omega

/-- Encoded length of `a + b` is at most `3 * ((encRat a).length + (encRat b).length)`. -/
theorem length_encRat_add_le (a b : ℚ) :
    (encRat (a + b)).length ≤ 3 * ((encRat a).length + (encRat b).length) := by
  rw [length_encRat, length_encRat, length_encRat]
  have hnum :
      (a + b).num.natAbs.size ≤
        a.num.natAbs.size + b.den.size + (b.num.natAbs.size + a.den.size) + 1 := by
    refine (Nat.size_le_size (Rat.natAbs_num_add_le a b)).trans ?_
    refine (Nat.size_add_le _ _).trans ?_
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.size_mul_le _ _) (Nat.size_mul_le _ _)) 1
  have hden : (a + b).den.size ≤ a.den.size + b.den.size :=
    (Nat.size_le_size (Rat.den_add_le a b)).trans (Nat.size_mul_le _ _)
  omega

/-- Encoded length of `a - b` is at most `3 * ((encRat a).length + (encRat b).length)`. -/
theorem length_encRat_sub_le (a b : ℚ) :
    (encRat (a - b)).length ≤ 3 * ((encRat a).length + (encRat b).length) := by
  rw [sub_eq_add_neg]
  simpa only [length_encRat_neg] using length_encRat_add_le a (-b)

/-- Encoded length of `a / b` is at most `(encRat a).length + 2 * (encRat b).length`. -/
theorem length_encRat_div_le (a b : ℚ) :
    (encRat (a / b)).length ≤ (encRat a).length + 2 * (encRat b).length := by
  rw [div_eq_mul_inv]
  exact (length_encRat_mul_le a b⁻¹).trans (Nat.add_le_add_left (length_encRat_inv_le b) _)

end Turing.MultiTapeTM
