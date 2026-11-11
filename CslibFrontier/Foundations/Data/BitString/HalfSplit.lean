/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate (addition to `Cslib/Foundations/Data/BitString.lean`)

public import Cslib.Foundations.Data.BitString
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Splitting a bit string into two halves

An `n`-bit string splits into its first `n / 2` bits and its remaining `n - n / 2` bits. For odd
`n` the second part is one bit longer than the first, so the split applies to every block length.

## Main definitions

* `Cslib.BitString.halfSplitEquiv`: the equivalence
  `BitString n ≃ BitString (n / 2) × BitString (n - n / 2)`.
-/

@[expose] public section

namespace Cslib.BitString

/-- Split an `n`-bit string into its first `n / 2` bits and its remaining `n - n / 2` bits, for
both even and odd `n`. -/
def halfSplitEquiv (n : ℕ) : BitString n ≃ BitString (n / 2) × BitString (n - n / 2) :=
  (Equiv.arrowCongr (finCongr (Nat.add_sub_of_le (Nat.div_le_self n 2)).symm)
    (Equiv.refl Bool)).trans (Fin.appendEquiv (n / 2) (n - n / 2)).symm

end Cslib.BitString
