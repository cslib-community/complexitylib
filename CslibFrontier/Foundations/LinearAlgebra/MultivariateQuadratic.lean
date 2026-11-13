/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Vector-valued multivariate quadratic maps

This file packages a family of quadratic forms as a vector-valued quadratic map.  It uses
Mathlib's `QuadraticMap` throughout, including in characteristic two: no division by two and no
choice of a symmetric matrix representative is required.

The API isolates the algebra shared by multivariate post-quantum signature proposals.  In the Oil
and Vinegar construction a central quadratic map vanishes on the oil subspace.  Its value at
`v + o`, for an oil vector `o`, is therefore its value at `v` plus the polar form at `(v, o)`, which
is linear in `o`.  A linear change of variables hides the central map while transporting the
vanishing subspace by `Submodule.comap`.

## Main definitions

* `Cslib.MultivariateQuadraticMap`: a quadratic map `R ^ I → R ^ O`.
* `Cslib.MultivariateQuadraticMap.ofCoordinates`: assemble scalar quadratic forms into a
  vector-valued map.
* `Cslib.MultivariateQuadraticMap.ofMatrices`: construct a map from one coefficient matrix per
  output coordinate.
* `Cslib.MultivariateQuadraticMap.VanishesOn`: a quadratic map vanishes on a submodule.
* `Cslib.MultivariateQuadraticMap.linearization`: the polar form with its first argument fixed.

## Main results

* `Cslib.MultivariateQuadraticMap.map_add_of_mem`: the Oil and Vinegar linearization identity.
* `Cslib.MultivariateQuadraticMap.VanishesOn.comp_comap`: a linear change of variables transports
  a vanishing subspace.
* `Cslib.MultivariateQuadraticMap.ofMatrices_apply` and
  `Cslib.MultivariateQuadraticMap.polar_ofMatrices_apply`: matrix evaluation and polarization.

## References

* MAYO Round-3 specification, Chapter 1, pp. 1–2, and §5.1, pp. 26–27.
* UOV specification v3.0, §2.3, pp. 8–10, and §3.2, pp. 13–19.
* MQOM specification v3.0, §2.1.1, pp. 4–5.
* QR-UOV Round-3 specification, §3.1, pp. 12–13.
* SNOVA specification v3.0, §§1.2.2–1.2.4, pp. 5–8.
-/

public section

open Matrix

namespace Cslib

/-- A vector-valued multivariate quadratic map with input coordinates `I` and output coordinates
`O` over `R`.  This is only a scheme-facing name for Mathlib's `QuadraticMap`. -/
abbrev MultivariateQuadraticMap (R I O : Type*) [CommRing R] :=
  QuadraticMap R (I → R) (O → R)

namespace MultivariateQuadraticMap

variable {R I O M N : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Assemble one scalar quadratic form per output coordinate into a vector-valued quadratic map. -/
@[expose] def ofCoordinates (Q : O → QuadraticForm R M) : QuadraticMap R M (O → R) :=
  QuadraticMap.ofPolar (fun x o ↦ Q o x)
    (fun a x ↦ funext fun o ↦ (Q o).map_smul a x)
    (fun x x' y ↦ funext fun o ↦ (Q o).polar_add_left x x' y)
    (fun a x y ↦ funext fun o ↦ (Q o).polar_smul_left a x y)

@[simp]
theorem ofCoordinates_apply (Q : O → QuadraticForm R M) (x : M) (o : O) :
    ofCoordinates Q x o = Q o x :=
  rfl

@[simp]
theorem polar_ofCoordinates_apply (Q : O → QuadraticForm R M) (x y : M) (o : O) :
    QuadraticMap.polar (ofCoordinates Q) x y o = QuadraticMap.polar (Q o) x y := by
  rfl

/-- The scalar quadratic form at one output coordinate. -/
@[expose] def coordinate (P : QuadraticMap R M (O → R)) (o : O) : QuadraticForm R M :=
  (LinearMap.proj o).compQuadraticMap P

@[simp]
theorem coordinate_apply (P : QuadraticMap R M (O → R)) (o : O) (x : M) :
    coordinate P o x = P x o :=
  rfl

@[simp]
theorem coordinate_ofCoordinates (Q : O → QuadraticForm R M) (o : O) :
    coordinate (ofCoordinates Q) o = Q o := by
  ext x
  rfl

/-- Vector-valued quadratic maps are equal when all scalar coordinates agree. -/
@[ext]
theorem ext {P Q : QuadraticMap R M (O → R)} (h : ∀ o x, P x o = Q x o) : P = Q := by
  apply QuadraticMap.ext
  intro x
  exact funext fun o ↦ h o x

section Matrices

variable [Fintype I] [DecidableEq I]

/-- Construct a multivariate quadratic map from one coefficient matrix per output coordinate.
The matrices need not be symmetric, which is important in characteristic two. -/
@[expose] def ofMatrices (A : O → Matrix I I R) : MultivariateQuadraticMap R I O :=
  ofCoordinates fun o ↦ (A o).toQuadraticForm'

@[simp]
theorem ofMatrices_apply (A : O → Matrix I I R) (x : I → R) (o : O) :
    ofMatrices A x o = x ⬝ᵥ (A o *ᵥ x) := by
  simp only [ofMatrices, ofCoordinates_apply, Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']

/-- The polar form of a matrix presentation is the sum of its two cross terms.  This formula is
valid in every characteristic. -/
@[simp]
theorem polar_ofMatrices_apply (A : O → Matrix I I R) (x y : I → R) (o : O) :
    QuadraticMap.polar (ofMatrices A) x y o =
      x ⬝ᵥ (A o *ᵥ y) + y ⬝ᵥ (A o *ᵥ x) := by
  change QuadraticMap.polar ((A o).toQuadraticForm') x y = _
  rw [Matrix.toQuadraticForm', LinearMap.BilinMap.polar_toQuadraticMap]
  simp only [Matrix.toLinearMap₂'_apply']

end Matrices

/-- A quadratic map vanishes on a submodule.  Oil spaces in UOV-type constructions satisfy this
property. -/
@[expose] def VanishesOn (P : QuadraticMap R M N) (S : Submodule R M) : Prop :=
  ∀ x ∈ S, P x = 0

theorem VanishesOn.mono {P : QuadraticMap R M N} {S T : Submodule R M}
    (hP : VanishesOn P S) (hTS : T ≤ S) : VanishesOn P T :=
  fun x hx ↦ hP x (hTS hx)

theorem vanishesOn_zero (S : Submodule R M) : VanishesOn (0 : QuadraticMap R M N) S := by
  intro x hx
  rfl

/-- Fixing the first argument of the polar form gives the linear system solved for the oil
variables in UOV-type signing. -/
@[expose] def linearization (P : QuadraticMap R M N) (v : M) : M →ₗ[R] N :=
  P.polarBilin v

@[simp]
theorem linearization_apply (P : QuadraticMap R M N) (v o : M) :
    linearization P v o = QuadraticMap.polar P v o :=
  rfl

/-- If `P` vanishes on `S`, evaluating at a public part plus a vector in `S` reduces to a value
independent of that vector plus a linear function of it. -/
theorem map_add_of_mem {P : QuadraticMap R M N} {S : Submodule R M}
    (hP : VanishesOn P S) (v : M) {o : M} (ho : o ∈ S) :
    P (v + o) = P v + linearization P v o := by
  rw [QuadraticMap.map_add P v o, hP o ho, add_zero]
  rfl

/-- A linear change of input variables transports a vanishing subspace by preimage. -/
theorem VanishesOn.comp_comap {P : QuadraticMap R M N} {S : Submodule R M}
    (hP : VanishesOn P S) {M' : Type*} [AddCommGroup M'] [Module R M']
    (T : M' →ₗ[R] M) : VanishesOn (P.comp T) (S.comap T) := by
  intro x hx
  exact hP (T x) hx

end MultivariateQuadraticMap

end Cslib
