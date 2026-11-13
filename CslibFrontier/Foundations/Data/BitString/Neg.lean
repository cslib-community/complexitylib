/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Data.BitString
public import Mathlib.Algebra.Ring.BooleanRing

/-!
# Negation and subtraction of bit strings

Bit strings `ι → Bool` add coordinatewise by XOR, so every bit string is its own negative and
subtraction is addition. These are the coordinatewise forms of `BooleanRing.neg_eq` and
`BooleanRing.sub_eq_add`. The module is small, so clients can import it without the rest of the
bit-string API.

## Main results

* `Cslib.BitString.neg_eq_self`: `-x = x`.
* `Cslib.BitString.sub_eq_add`: `x - y = x + y`.
-/

public section

namespace Cslib.BitString

variable {ι : Type*}

/-- Every bit string is its own negative. -/
protected theorem neg_eq_self (x : ι → Bool) : -x = x :=
  funext fun i => BooleanRing.neg_eq (x i)

/-- Subtracting a bit string is adding it. -/
protected theorem sub_eq_add (x y : ι → Bool) : x - y = x + y :=
  funext fun i => BooleanRing.sub_eq_add (x i) (y i)

end Cslib.BitString
