/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Quantum.Basic
public import Complexity.Foundations.Quantum.Pauli

/-!
# Bit-indexed matrices of the NOT, Hadamard and CNOT gates

The register gates of `Complexity/Computability/Circuit/Quantum/Basic.lean` are indexed by bit
strings `Fin k → Bool`. Small protocols are easier to state with one basis index per qubit, as
`Bool` for one qubit and `Bool × Bool` for two. This file provides the `Bool × Bool`-indexed
**CNOT** matrix `|a, b⟩ ↦ |a, b ⊕ a⟩` (`Cslib.Quantum.Gate.cnotMatrix`), the action of the
Hadamard matrix `Cslib.Quantum.Gate.hadamardMatrix` on vectors, and the identifications of the
register gates `Cslib.Quantum.Gate.cnot` and `Cslib.Quantum.Gate.not` with `cnotMatrix` and the
Pauli matrix `X` (`Cslib.Quantum.pauliX`) under the reindexings `Fin 2 → Bool ≃ Bool × Bool` and
`Fin 1 → Bool ≃ Bool`, [de Wolf][deWolf2019], Section 1.4.

## Main definitions

* `Cslib.Quantum.Gate.cnotMatrix`: the CNOT matrix on `Bool × Bool`, first qubit the control.

## Main results

* `Cslib.Quantum.Gate.cnotMatrix_mem_unitaryGroup`: the CNOT matrix is unitary.
* `Cslib.Quantum.Gate.cnotMatrix_mulVec`, `Cslib.Quantum.Gate.hadamardMatrix_mulVec`: the action
  of the CNOT and Hadamard matrices on vectors.
* `Cslib.Quantum.Gate.cnot_eq_submatrix_cnotMatrix`: the register gate `cnot` is `cnotMatrix`.
* `Cslib.Quantum.Gate.not_eq_submatrix_pauliX`: the register gate `not` is the Pauli matrix `X`.

## References

* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019]
-/

public section

namespace Cslib.Quantum

namespace Gate

open Matrix

/-- The Hadamard matrix maps `v` to `((v₀ + (-1)^b v₁)/√2)_b`. -/
theorem hadamardMatrix_mulVec (v : Bool → ℂ) (b : Bool) :
    (hadamardMatrix *ᵥ v) b =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (v false + (if b then -1 else 1) * v true) := by
  cases b <;> simp [mulVec, dotProduct, hadamardMatrix] <;> ring

/-- The **CNOT** matrix `|a, b⟩ ↦ |a, b ⊕ a⟩` on two qubits indexed by `Bool × Bool`, the first
qubit being the control. -/
noncomputable def cnotMatrix : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun p q => if p.1 = q.1 ∧ p.2 = (q.2 ^^ q.1) then 1 else 0

theorem cnotMatrix_apply (p q : Bool × Bool) :
    cnotMatrix p q = if p.1 = q.1 ∧ p.2 = (q.2 ^^ q.1) then 1 else 0 := by
  rfl

@[simp] theorem cnotMatrix_mulVec (v : Bool × Bool → ℂ) (a b : Bool) :
    (cnotMatrix *ᵥ v) (a, b) = v (a, b ^^ a) := by
  cases a <;> cases b <;> simp [mulVec, dotProduct, cnotMatrix_apply, Fintype.sum_prod_type]

theorem cnotMatrix_isHermitian : Matrix.IsHermitian cnotMatrix := by
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> simp [conjTranspose_apply, cnotMatrix_apply]

theorem cnotMatrix_mul_self : cnotMatrix * cnotMatrix = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [Matrix.mul_apply, cnotMatrix_apply, Fintype.sum_prod_type]

theorem cnotMatrix_mem_unitaryGroup : cnotMatrix ∈ unitaryGroup (Bool × Bool) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, cnotMatrix_isHermitian.eq,
    cnotMatrix_mul_self]

theorem cnot_apply (y x : Fin 2 → Bool) :
    (cnot : Matrix (Fin 2 → Bool) (Fin 2 → Bool) ℂ) y x =
      if y = Function.update x 1 (x 1 ^^ x 0) then 1 else 0 :=
  ofPerm_apply _ y x

theorem not_apply (y x : Fin 1 → Bool) :
    (Gate.not : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) y x =
      if y = (fun _ => !x 0) then 1 else 0 :=
  ofPerm_apply _ y x

/-- The register gate `cnot` is the CNOT matrix, reindexed by `Fin 2 → Bool ≃ Bool × Bool`. -/
theorem cnot_eq_submatrix_cnotMatrix :
    (cnot : Matrix (Fin 2 → Bool) (Fin 2 → Bool) ℂ) =
      cnotMatrix.submatrix (finTwoArrowEquiv Bool) (finTwoArrowEquiv Bool) := by
  ext x y
  rw [cnot_apply]
  change _ = cnotMatrix (x 0, x 1) (y 0, y 1)
  rw [cnotMatrix_apply]
  congr 1
  refine propext ⟨fun h => ?_, fun ⟨h0, h1⟩ => ?_⟩
  · rw [h]; simp
  · funext i; fin_cases i
    · exact h0
    · simpa using h1

/-- The register gate `not` is the Pauli matrix `X`, reindexed by `Fin 1 → Bool ≃ Bool`. -/
theorem not_eq_submatrix_pauliX :
    (Gate.not : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) =
      pauliX.submatrix (Equiv.funUnique (Fin 1) Bool) (Equiv.funUnique (Fin 1) Bool) := by
  ext x y
  rw [not_apply]
  change _ = pauliX (x 0) (y 0)
  rw [pauliX_apply]
  congr 1
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · rw [h]
  · funext i; fin_cases i; exact h

end Gate

end Cslib.Quantum
