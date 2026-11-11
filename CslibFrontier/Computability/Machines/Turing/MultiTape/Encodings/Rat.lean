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

end Turing.MultiTapeTM
