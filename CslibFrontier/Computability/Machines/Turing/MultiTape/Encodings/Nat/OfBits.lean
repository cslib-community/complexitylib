/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
public import CslibFrontier.Foundations.Data.BitString.Binary

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

end Turing.MultiTapeTM
