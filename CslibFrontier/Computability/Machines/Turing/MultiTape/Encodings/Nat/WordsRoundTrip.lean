/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
import CslibFrontier.Foundations.Data.Nat.Bits

/-!
# Reading back encoded natural numbers

`ofBits` inverts the binary-digit encoding `encNat`. Clients that decode encoded numbers (keys,
exponents, commitments) use these round trips instead of unfolding `ofBits` to reach
`Nat.foldr_bit_bits`. The module is kept separate from `Encodings/Nat/Words`, which has a large
import fan-out.

## Main results

* `Turing.MultiTapeTM.ofBits_bits`: reading back the binary digits of `n` gives `n`.
* `Turing.MultiTapeTM.ofBits_encNat`: the same round trip through `encNat`.
-/

public section

namespace Turing.MultiTapeTM

/-- Reading back the binary digits of a number recovers it. -/
@[simp] theorem ofBits_bits (n : ℕ) : ofBits n.bits = n := Nat.foldr_bit_bits n

/-- Reading back an encoded number recovers it. -/
theorem ofBits_encNat (n : ℕ) : ofBits (encNat n) = n := ofBits_bits n

end Turing.MultiTapeTM
