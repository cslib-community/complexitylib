/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PolyTime.GaloisRingUnits
import Mathlib.Algebra.Polynomial.SpecificDegree

/-! # Newton inversion of units in a Galois ring

For `f = U ^ 2 + U + 1`, irreducible modulo `2`, Newton inversion inverts every unit of
`(ℤ / 8)[U] / (f)` (`p = 3`, `fl = [1, 1]`) with no hypothesis on the seed. -/

namespace ComplexityTests.GaloisRingUnits

open Cslib.GaloisRingArith Polynomial

/-- `U ^ 2 + U + 1` is irreducible modulo `2`: it has degree two and no root in `𝔽_2`. -/
theorem irreducible_monicOf_one_one :
    Irreducible ((monicOf [1, 1]).map (Int.castRingHom (ZMod 2))) := by
  have hmap : (monicOf [1, 1]).map (Int.castRingHom (ZMod 2)) = X ^ 2 + X + 1 := by
    simp [monicOf, Finset.sum_range_succ]
    ring
  have hmon : ((monicOf [1, 1]).map (Int.castRingHom (ZMod 2))).Monic :=
    (monic_monicOf _).map _
  have hdeg : ((monicOf [1, 1]).map (Int.castRingHom (ZMod 2))).natDegree = 2 := by
    rw [(monic_monicOf _).natDegree_map, natDegree_monicOf]; rfl
  rw [hmon.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
  rw [mem_roots hmon.ne_zero, IsRoot, hmap] at hx
  simp only [eval_add, eval_pow, eval_X, eval_one] at hx
  fin_cases x <;> exact absurd hx (by decide)

/-- **Every unit is inverted**, with no hypothesis on the seed. -/
example (x : List ℕ) (hx : IsUnit (val 3 [1, 1] x)) :
    val 3 [1, 1] x * val 3 [1, 1] (inv 3 [1, 1] x) = 1 :=
  val_mul_inv_of_isUnit irreducible_monicOf_one_one hx

/-- Every element that is nonzero modulo `2` is inverted. -/
example (x : List ℕ) (hx : GaloisRing.residue 2 3 (monicOf [1, 1]) (val 3 [1, 1] x) ≠ 0) :
    val 3 [1, 1] x * val 3 [1, 1] (inv 3 [1, 1] x) = 1 :=
  val_mul_inv_of_residue_ne_zero irreducible_monicOf_one_one hx

/-- The seed inverts every unit modulo `2`: here `e = 2`, so the seed is `x ^ 2`. -/
example (y : Ring 3 [1, 1]) (hy : IsUnit y) : ∃ w, y * y ^ (2 ^ 2 - 2) = 1 + 2 * w :=
  exists_mul_pow_eq_one_add_two_mul irreducible_monicOf_one_one hy

example : (monicOf [1, 1]).natDegree = 2 := natDegree_monicOf _

end ComplexityTests.GaloisRingUnits
