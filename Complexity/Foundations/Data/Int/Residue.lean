/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Order.Ring.Int

/-!
# Integer residues as natural numbers

## Main results

* `Int.natCast_toNat_emod`: the nonnegative integer residue survives a round trip through `Nat`.

Bounds on natural residues use Mathlib's existing `Int.natMod_lt`.

## References

Adapted from [Index.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Util/Index.lean) at
`anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
The existing Exact Triangle hashing client now uses these shared facts.
-/

@[expose] public section

namespace Int

/-- Casting the natural Euclidean residue back to `Int` preserves its value for a positive
modulus. -/
theorem natCast_toNat_emod {p : ℕ} (hp : 0 < p) (u : ℤ) :
    ((u % (p : ℤ)).toNat : ℤ) = u % (p : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

end Int
