/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
public import CslibFrontier.Foundations.Data.BitString.Binary
public import CslibFrontier.Foundations.Data.BitString.List

/-!
# Reading words as numbers through `lsbValue`

`Turing.MultiTapeTM.ofBits` and `Cslib.BitString.lsbValue` both read a word as a number, least
significant bit first. This module identifies them and transfers the facts that
`Cslib.BitString` already proves about `lsbValue` to `ofBits`.

The module is kept apart from `Encodings.Nat.Words`, which many modules import, so that only its
clients depend on it.

## Main results

* `Turing.MultiTapeTM.ofBits_eq_lsbValue`: `ofBits` is `Cslib.BitString.lsbValue`.
* `Turing.MultiTapeTM.ofBits_ofFn`: reading a finite bit string gives its index under
  `Cslib.BitString.equivFin`.
* `Turing.MultiTapeTM.ofBits_replicate_false`: an all-`false` word reads as zero.
* `Turing.MultiTapeTM.ofBits_lt_two_pow`, `Turing.MultiTapeTM.ofBits_injective_of_length_eq`: a
  word of length `m` reads below `2 ^ m`, and words of one length are determined by their values.
* `Turing.MultiTapeTM.ofBits_append`: reading a concatenation shifts the second word past the first.
* `Turing.MultiTapeTM.ofBits_lowBits`: the `W` low-order digits (`Cslib.BitString.lowBits`) of
  `x < 2 ^ W` read as `x`.
* `Turing.MultiTapeTM.ofBits_ofFn_ofList`: padding a word with `false` to a fixed width
  (`Cslib.BitString.ofList`) does not change its value.
-/

public section

namespace Turing.MultiTapeTM

/-- `ofBits` and `Cslib.BitString.lsbValue` read words the same way. -/
theorem ofBits_eq_lsbValue (w : List Bool) : ofBits w = Cslib.BitString.lsbValue w :=
  (Cslib.BitString.lsbValue_eq_foldr_bit w).symm

/-- Reading a finite bit string gives its index under `Cslib.BitString.equivFin`. -/
theorem ofBits_ofFn {n : ℕ} (bits : Cslib.BitString n) :
    ofBits (List.ofFn bits) = (Cslib.BitString.equivFin n bits).val := by
  rw [ofBits_eq_lsbValue, Cslib.BitString.lsbValue_ofFn]

/-- An all-`false` word reads as zero. -/
theorem ofBits_replicate_false (n : ℕ) : ofBits (List.replicate n false) = 0 := by
  rw [ofBits_eq_lsbValue, Cslib.BitString.lsbValue_replicate_false]

/-- A word of length `m` reads as a number below `2 ^ m`. -/
theorem ofBits_lt_two_pow (w : List Bool) : ofBits w < 2 ^ w.length := by
  rw [ofBits_eq_lsbValue]
  exact Cslib.BitString.lsbValue_lt w

/-- Words of the same length that read as the same number are equal. -/
theorem ofBits_injective_of_length_eq {u v : List Bool} (hlen : u.length = v.length)
    (heq : ofBits u = ofBits v) : u = v := by
  rw [ofBits_eq_lsbValue, ofBits_eq_lsbValue] at heq
  exact Cslib.BitString.lsbValue_injective hlen heq

/-- Reading a concatenation shifts the second word past the first. -/
theorem ofBits_append (u v : List Bool) :
    ofBits (u ++ v) = ofBits u + 2 ^ u.length * ofBits v := by
  simp only [ofBits_eq_lsbValue, Cslib.BitString.lsbValue_append]

/-- The `W` low-order digits of `x < 2 ^ W` read as `x`. -/
theorem ofBits_lowBits {W x : ℕ} (hx : x < 2 ^ W) :
    ofBits (Cslib.BitString.lowBits W x) = x := by
  rw [ofBits_eq_lsbValue]
  exact Cslib.BitString.lsbValue_lowBits hx

/-- Padding a word to `n` bits with `false` does not change the number it reads as. -/
theorem ofBits_ofFn_ofList (word : List Bool) (n : ℕ) (h : word.length ≤ n) :
    ofBits (List.ofFn (Cslib.BitString.ofList n word)) = ofBits word := by
  rw [Cslib.BitString.ofFn_ofList_eq_take, List.take_append, List.take_of_length_le h,
    List.take_replicate, ofBits_append, ofBits_replicate_false, mul_zero, add_zero]

end Turing.MultiTapeTM
