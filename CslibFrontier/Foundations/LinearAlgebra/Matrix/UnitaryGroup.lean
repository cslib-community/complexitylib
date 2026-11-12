/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/UnitaryGroup.lean`)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Hermitian involutions are unitary

A Hermitian matrix `A` with `A * A = 1` is unitary, since `A * star A = A * A`
(`Matrix.IsHermitian.mem_unitaryGroup_of_mul_self`). In quantum computing these are the `±1`
observables, such as the Pauli matrices and the CNOT gate.

## Main results

* `Matrix.IsHermitian.mem_unitaryGroup_of_mul_self`: a Hermitian involution is unitary.
-/

public section

namespace Matrix

/-- A Hermitian matrix `A` with `A * A = 1` (a `±1` observable) is unitary. -/
theorem IsHermitian.mem_unitaryGroup_of_mul_self {n α : Type*} [Fintype n] [DecidableEq n]
    [CommRing α] [StarRing α] {A : Matrix n n α} (hA : A.IsHermitian) (hA2 : A * A = 1) :
    A ∈ unitaryGroup n α := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, hA.eq, hA2]

end Matrix
