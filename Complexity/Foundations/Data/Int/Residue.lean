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
* `Int.toNat_neg_emod`: compute the natural residue of a negated integer from its residue.

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

/-- Natural residues of negated integers use a zero test followed by natural subtraction. -/
theorem toNat_neg_emod {p : ℕ} (hp : 0 < p) (z : ℤ) :
    ((-z) % (p : ℤ)).toNat =
      if (z % (p : ℤ)).toNat = 0 then 0 else p - (z % (p : ℤ)).toNat := by
  have hnonneg := Int.emod_nonneg z (show (p : ℤ) ≠ 0 by omega)
  have hlt := Int.emod_lt_of_pos z (show (0 : ℤ) < p by omega)
  rw [Int.neg_emod]
  by_cases h : (p : ℤ) ∣ z
  · simp only [h, ite_true, Int.emod_eq_zero_of_dvd h, Int.toNat_zero]
  · have hn : (z % (p : ℤ)).toNat ≠ 0 := by
      intro hz
      have he : z % (p : ℤ) = 0 := by omega
      exact h (Int.dvd_of_emod_eq_zero he)
    simp only [h, ite_false, hn, Int.natAbs_natCast]
    omega

end Int
