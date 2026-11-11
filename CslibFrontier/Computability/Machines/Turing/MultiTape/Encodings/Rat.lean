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
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Data.Nat.Size

/-!
# Binary encoding of rational numbers

`Turing.MultiTapeTM.encRat` encodes a rational number `q : ℚ` as its framed pair
`(q.num, q.den) : ℤ × ℕ` using `Turing.MultiTapeTM.encIntBin` and `Turing.MultiTapeTM.encNat`.

## Main definitions

* `Turing.MultiTapeTM.encRatData`: framed pair encoding of `(ℤ × ℕ)` used for rationals.
* `Turing.MultiTapeTM.encRat`: binary encoding of `ℚ` via `(q.num, q.den)`.

## Main results

* `Turing.MultiTapeTM.encRat_apply`: unfolding of `encRat q`.
* `Turing.MultiTapeTM.length_encRat_num_le`: `(encIntBin q.num).length ≤ (encRat q).length`.
* `Turing.MultiTapeTM.length_encRat_den_le`: `(encNat q.den).length ≤ (encRat q).length`.
* `Turing.MultiTapeTM.length_encRat`, `Turing.MultiTapeTM.length_encRat_le`: exact bit length
  of `encRat q` and upper bound from numerator/denominator sizes.
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

theorem length_encRat_num_le (q : ℚ) : (encIntBin q.num).length ≤ (encRat q).length :=
  length_le_encPair_left encIntBin encNat (q.num, q.den)

theorem length_encRat_den_le (q : ℚ) : (encNat q.den).length ≤ (encRat q).length :=
  length_le_encPair_right encIntBin encNat (q.num, q.den)

/-- Exact encoded bit length of a rational under `Turing.MultiTapeTM.encRat`. -/
theorem length_encRat (q : ℚ) :
    (encRat q).length = 2 * (q.num.natAbs.size + 1) + 1 + q.den.size := by
  rw [encRat_apply, length_encPair, length_encIntBin, encNat_apply, Nat.size_eq_bits_len]

/-- Upper bound on `(encRat q).length` in terms of `|q.num|` and `q.den` binary sizes. -/
theorem length_encRat_le (q : ℚ) {A B : ℕ} (hnum : q.num.natAbs ≤ A) (hden : q.den ≤ B) :
    (encRat q).length ≤ 2 * A.size + B.size + 3 := by
  rw [length_encRat]
  have hn : q.num.natAbs.size ≤ A.size := Nat.size_le_size hnum
  have hd : q.den.size ≤ B.size := Nat.size_le_size hden
  omega

end Turing.MultiTapeTM
