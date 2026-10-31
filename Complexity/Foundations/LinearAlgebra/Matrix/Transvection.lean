/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Transvections in the special linear group acting on vectors

Mathlib's `Matrix.SpecialLinearGroup.transvection` is the transvection `1 + c E_ij`, for `i ≠ j`,
as an element of `SL_n(R)`. This file adds two facts about it: a ring homomorphism maps it to the
transvection with the image parameter, and it acts on a vector by adding `c` times the coordinate
`j` to the coordinate `i`. Mathlib computes the action on standard basis vectors only. For `c = 1`
these are the elementary generators of `SL_n(ℤ)`, which act on vectors over every quotient ring
by the elementary moves.

## Main results

* `Matrix.SpecialLinearGroup.map_transvection`: a ring homomorphism maps transvections to
  transvections.
* `Matrix.SpecialLinearGroup.transvection_mulVec`: a transvection adds `c v j` to `v i`.
-/

public section

namespace Matrix.SpecialLinearGroup

open Function

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- A ring homomorphism maps the transvection `1 + c E_ij` to `1 + f c E_ij`. -/
@[simp]
theorem map_transvection {S : Type*} [CommRing S] (f : R →+* S) {i j : n} (h : i ≠ j) (c : R) :
    map f (transvection h c) = transvection h (f c) := by
  ext k l
  simp only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, transvection_coe,
    Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

/-- The transvection `1 + c E_ij` adds `c v j` to the coordinate `i` of `v`. -/
@[simp]
theorem transvection_mulVec {i j : n} (h : i ≠ j) (c : R) (v : n → R) :
    (transvection h c : Matrix n n R) *ᵥ v = update v i (v i + c * v j) := by
  rw [transvection_coe, add_mulVec, one_mulVec, single_mulVec]
  ext k
  by_cases hk : k = i
  · subst hk
    simp
  · simp [hk]

end Matrix.SpecialLinearGroup
