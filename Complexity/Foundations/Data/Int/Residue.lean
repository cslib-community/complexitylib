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
* `Int.toNat_emod_lt`: the natural residue is below a positive modulus.

## References

Adapted from [Index.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Util/Index.lean) at
`anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
The existing Exact Triangle hashing client now uses these shared facts.
-/

@[expose] public section

namespace Int

theorem natCast_toNat_emod {p : ℕ} (hp : 0 < p) (u : ℤ) :
    ((u % (p : ℤ)).toNat : ℤ) = u % (p : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

theorem toNat_emod_lt {p : ℕ} (hp : 0 < p) (u : ℤ) : (u % (p : ℤ)).toNat < p := by
  have := Int.emod_nonneg u (by omega : (p : ℤ) ≠ 0)
  have := Int.emod_lt_of_pos u (by omega : (0 : ℤ) < p)
  omega

end Int
