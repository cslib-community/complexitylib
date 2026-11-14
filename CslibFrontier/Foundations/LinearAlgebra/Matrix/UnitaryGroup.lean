/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/UnitaryGroup.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Unitary group characterizations and Hermitian involutions

For a square matrix `U : Matrix n n 𝕜` over `[RCLike 𝕜]`, we prove the four-way equivalence
(`Matrix.unitaryGroup_tfae`, [Arora and Barak, Claim 20.11][AroraBarak07]):

1. `U ∈ unitaryGroup n 𝕜` (`U * star U = 1` and `star U * U = 1`);
2. `∀ v : EuclideanSpace 𝕜 n, ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) U v‖ = ‖v‖` (Euclidean norm
   preservation);
3. `Orthonormal 𝕜 (fun j : n => WithLp.toLp 2 (fun i => U i j))` (orthonormal columns);
4. `Orthonormal 𝕜 (fun i : n => WithLp.toLp 2 (U i))` (orthonormal rows).

A Hermitian matrix `A` with `A * A = 1` is unitary, since `A * star A = A * A`
(`Matrix.IsHermitian.mem_unitaryGroup_of_mul_self`). In quantum computing these are the `±1`
observables, such as the Pauli matrices and the CNOT gate.

## Main results

* `Matrix.IsHermitian.mem_unitaryGroup_of_mul_self`: a Hermitian involution is unitary.
* `Matrix.mem_unitaryGroup_iff_forall_norm_toEuclideanCLM`: a matrix is unitary iff its action on
  `EuclideanSpace 𝕜 n` preserves the Euclidean norm of every vector.
* `Matrix.mem_unitaryGroup_iff_orthonormal_cols`,
  `Matrix.mem_unitaryGroup_iff_orthonormal_rows`: a matrix is unitary iff its columns (or rows) are
  orthonormal in `EuclideanSpace 𝕜 n`.
* `Matrix.unitaryGroup_tfae`: the four-way `List.TFAE` equivalence.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak07]
-/

public section

namespace Matrix

/-- A Hermitian matrix `A` with `A * A = 1` (a `±1` observable) is unitary. -/
theorem IsHermitian.mem_unitaryGroup_of_mul_self {n α : Type*} [Fintype n] [DecidableEq n]
    [CommRing α] [StarRing α] {A : Matrix n n α} (hA : A.IsHermitian) (hA2 : A * A = 1) :
    A ∈ unitaryGroup n α := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, hA.eq, hA2]

section RCLike

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- A square matrix over `𝕜` is unitary if and only if its action on `EuclideanSpace 𝕜 n` preserves
the Euclidean norm of every vector [Arora and Barak, Claim 20.11][AroraBarak07]. -/
theorem mem_unitaryGroup_iff_forall_norm_toEuclideanCLM (U : Matrix n n 𝕜) :
    U ∈ unitaryGroup n 𝕜 ↔
      ∀ v : EuclideanSpace 𝕜 n, ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) U v‖ = ‖v‖ := by
  rw [(toEuclideanCLM (n := n) (𝕜 := 𝕜) U).norm_map_iff_adjoint_comp_self,
    ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_def, ← map_star, ← map_mul,
    ← map_one (toEuclideanCLM (n := n) (𝕜 := 𝕜)),
    EmbeddingLike.apply_eq_iff_eq, mem_unitaryGroup_iff']

/-- A square matrix over `𝕜` is unitary if and only if its columns form an orthonormal family in
`EuclideanSpace 𝕜 n` [Arora and Barak, Claim 20.11][AroraBarak07]. -/
theorem mem_unitaryGroup_iff_orthonormal_cols (U : Matrix n n 𝕜) :
    U ∈ unitaryGroup n 𝕜 ↔ Orthonormal 𝕜 (fun j : n => WithLp.toLp 2 (fun i => U i j)) := by
  rw [mem_unitaryGroup_iff', orthonormal_iff_ite, ← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  simp [Matrix.mul_apply, Matrix.one_apply, PiLp.inner_apply, star_eq_conjTranspose, mul_comm]

/-- A square matrix over `𝕜` is unitary if and only if its rows form an orthonormal family in
`EuclideanSpace 𝕜 n` [Arora and Barak, Claim 20.11][AroraBarak07]. -/
theorem mem_unitaryGroup_iff_orthonormal_rows (U : Matrix n n 𝕜) :
    U ∈ unitaryGroup n 𝕜 ↔ Orthonormal 𝕜 (fun i : n => WithLp.toLp 2 (U i)) := by
  rw [← Matrix.transpose_mem_unitaryGroup_iff, mem_unitaryGroup_iff_orthonormal_cols]
  rfl

/-- **Four equivalent characterizations of a unitary matrix**
([Arora and Barak, Claim 20.11 and Chapter 20, Exercise 1][AroraBarak07]):
`U ∈ unitaryGroup n 𝕜`, norm preservation on `EuclideanSpace 𝕜 n`, orthonormal columns, and
orthonormal rows. -/
theorem unitaryGroup_tfae (U : Matrix n n 𝕜) :
    List.TFAE
      [U ∈ unitaryGroup n 𝕜,
        ∀ v : EuclideanSpace 𝕜 n, ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) U v‖ = ‖v‖,
        Orthonormal 𝕜 (fun j : n => WithLp.toLp 2 (fun i => U i j)),
        Orthonormal 𝕜 (fun i : n => WithLp.toLp 2 (U i))] := by
  tfae_have 1 ↔ 2 := mem_unitaryGroup_iff_forall_norm_toEuclideanCLM U
  tfae_have 1 ↔ 3 := mem_unitaryGroup_iff_orthonormal_cols U
  tfae_have 1 ↔ 4 := mem_unitaryGroup_iff_orthonormal_rows U
  tfae_finish

end RCLike

end Matrix
