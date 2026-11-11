/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The Pauli matrices `X` and `Z`

The single-qubit Pauli matrices `X = [[0, 1], [1, 0]]` (the bit flip, `Cslib.Quantum.pauliX`) and
`Z = [[1, 0], [0, -1]]` (the phase flip, `Cslib.Quantum.pauliZ`), indexed by one bit `Bool` as the
Hadamard matrix `Cslib.Quantum.Gate.hadamardMatrix` is, [de Wolf][deWolf2019], Appendix A.9. They
are Hermitian, square to the identity and anticommute, so they are unitary; their action on a
vector is `(X v)_b = v_{¬b}` and `(Z v)_b = (-1)^b v_b`.

Teleportation and superdense coding apply them as Bob's correction and as Alice's encoding
(`Complexity/Computability/Circuit/Quantum/Teleportation.lean`,
`Complexity/Computability/Circuit/Quantum/SuperdenseCoding.lean`).

## Main definitions

* `Cslib.Quantum.pauliX`: the Pauli matrix `X`.
* `Cslib.Quantum.pauliZ`: the Pauli matrix `Z`.

## Main results

* `Cslib.Quantum.pauliX_mem_unitaryGroup`, `Cslib.Quantum.pauliZ_mem_unitaryGroup`: they are
  unitary.
* `Cslib.Quantum.pauliX_mul_self`, `Cslib.Quantum.pauliZ_mul_self`: they square to the identity.
* `Cslib.Quantum.pauliZ_mul_pauliX`: they anticommute, `ZX = -XZ`.
* `Cslib.Quantum.pauliX_mulVec`, `Cslib.Quantum.pauliZ_mulVec`: their action on a vector.

## References

* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019]
-/

public section

namespace Cslib.Quantum

open Matrix

/-- The **Pauli matrix** `X = [[0, 1], [1, 0]]`, the bit flip `|b⟩ ↦ |¬b⟩`. -/
noncomputable def pauliX : Matrix Bool Bool ℂ := fun b c => if b = !c then 1 else 0

/-- The **Pauli matrix** `Z = [[1, 0], [0, -1]]`, the phase flip `|b⟩ ↦ (-1)^b |b⟩`. -/
noncomputable def pauliZ : Matrix Bool Bool ℂ := Matrix.diagonal fun b => if b then -1 else 1

@[simp] theorem pauliX_apply (b c : Bool) : pauliX b c = if b = !c then 1 else 0 := by
  rfl

@[simp] theorem pauliZ_apply (b c : Bool) :
    pauliZ b c = if b = c then (if b then -1 else 1) else 0 := by
  simp [pauliZ, Matrix.diagonal_apply]

theorem pauliX_isHermitian : Matrix.IsHermitian pauliX := by
  ext b c; cases b <;> cases c <;> simp [Matrix.conjTranspose_apply]

theorem pauliZ_isHermitian : Matrix.IsHermitian pauliZ := by
  ext b c; cases b <;> cases c <;> simp [Matrix.conjTranspose_apply]

theorem pauliX_mul_self : pauliX * pauliX = 1 := by
  ext b c; cases b <;> cases c <;> simp [Matrix.mul_apply]

theorem pauliZ_mul_self : pauliZ * pauliZ = 1 := by
  ext b c; cases b <;> cases c <;> simp [Matrix.mul_apply]

/-- The Pauli matrices `X` and `Z` anticommute. -/
theorem pauliZ_mul_pauliX : pauliZ * pauliX = -(pauliX * pauliZ) := by
  ext b c; cases b <;> cases c <;> simp [Matrix.mul_apply]

theorem pauliX_mem_unitaryGroup : pauliX ∈ unitaryGroup Bool ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, pauliX_isHermitian.eq, pauliX_mul_self]

theorem pauliZ_mem_unitaryGroup : pauliZ ∈ unitaryGroup Bool ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, pauliZ_isHermitian.eq, pauliZ_mul_self]

@[simp] theorem pauliX_mulVec (v : Bool → ℂ) (b : Bool) : (pauliX *ᵥ v) b = v (!b) := by
  cases b <;> simp [mulVec, dotProduct]

@[simp] theorem pauliZ_mulVec (v : Bool → ℂ) (b : Bool) :
    (pauliZ *ᵥ v) b = (if b then -1 else 1) * v b := by
  cases b <;> simp [mulVec, dotProduct]

end Cslib.Quantum
