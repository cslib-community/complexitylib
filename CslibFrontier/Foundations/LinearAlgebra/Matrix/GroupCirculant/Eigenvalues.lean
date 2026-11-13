/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.Tactic.Abel

/-!
# Character eigenvalues of group-circulant matrices

The character eigenvalues of a circulant matrix multiply under convolution. This elementary
API is shared by the spectral results in `GroupCirculant` and binary syndrome parity. Its
declarations are extracted unchanged from `GroupCirculant`; no splitting-field or spectral-rank
assumption is needed.

## Main definitions

* `Matrix.circulantEigenvalue`: the eigenvalue at an additive character.

## Main results

* `Matrix.circulant_mulVec_addChar`: characters are eigenvectors.
* `Matrix.circulantEigenvalue_mulVec`: convolution multiplies character eigenvalues.
* `Matrix.circulantEigenvalue_trivial`: the trivial character gives the sum of entries.
-/

public section

namespace Matrix

open Finset
open scoped BigOperators

/-! ### Group-circulant eigenvectors and character eigenvalues -/

section Eigenvalues

variable {G R : Type*} [AddCommGroup G] [Fintype G]

/-- The character eigenvalue associated to `w : G → R` at `ψ : AddChar G R`, given by
`∑ g : G, w g * ψ (-g)`. -/
@[expose] def circulantEigenvalue [CommSemiring R] (w : G → R) (ψ : AddChar G R) : R :=
  ∑ g : G, w g * ψ (-g)

/-- Every additive character `ψ : AddChar G R` is an eigenvector of `Matrix.circulant w` with
eigenvalue `circulantEigenvalue w ψ`. -/
theorem circulant_mulVec_addChar [CommSemiring R] (w : G → R) (ψ : AddChar G R) :
    circulant w *ᵥ (⇑ψ) = circulantEigenvalue w ψ • (⇑ψ) := by
  funext x
  simp only [mulVec, dotProduct, circulant_apply, Pi.smul_apply, smul_eq_mul,
    circulantEigenvalue, sum_mul]
  refine Fintype.sum_equiv (Equiv.subLeft x) _ _ fun y => ?_
  have hy : y = x + -(x - y) := by abel
  have hψ : ψ y = ψ x * ψ (-(x - y)) := by
    conv_lhs => rw [hy]
    exact ψ.map_add_eq_mul _ _
  rw [Equiv.subLeft_apply, hψ, mul_comm (ψ x), ← mul_assoc]

@[simp]
theorem circulantEigenvalue_zero [CommSemiring R] (ψ : AddChar G R) :
    circulantEigenvalue (0 : G → R) ψ = 0 := by
  simp [circulantEigenvalue]

theorem circulantEigenvalue_add [CommSemiring R] (u v : G → R) (ψ : AddChar G R) :
    circulantEigenvalue (u + v) ψ = circulantEigenvalue u ψ + circulantEigenvalue v ψ := by
  simp only [circulantEigenvalue, Pi.add_apply, add_mul, sum_add_distrib]

theorem circulantEigenvalue_smul [CommSemiring R] (c : R) (w : G → R) (ψ : AddChar G R) :
    circulantEigenvalue (c • w) ψ = c * circulantEigenvalue w ψ := by
  simp only [circulantEigenvalue, Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum]

@[simp]
theorem circulantEigenvalue_single_zero [CommSemiring R] [DecidableEq G] (a : R)
    (ψ : AddChar G R) :
    circulantEigenvalue (Pi.single 0 a : G → R) ψ = a := by
  rw [circulantEigenvalue, Fintype.sum_eq_single 0 fun g hg => by simp [hg]]
  simp

@[simp]
theorem circulantEigenvalue_trivial [CommSemiring R] (w : G → R) :
    circulantEigenvalue w (0 : AddChar G R) = ∑ g : G, w g := by
  simp [circulantEigenvalue]

/-- When `w` is negation-symmetric (`w (-g) = w g`, e.g. undirected Cayley graphs or `𝔽₂^n`),
`circulantEigenvalue w ψ` equals `∑ g, w g * ψ g`. -/
theorem circulantEigenvalue_of_symm [CommSemiring R] {w : G → R} (hw : ∀ g, w (-g) = w g)
    (ψ : AddChar G R) :
    circulantEigenvalue w ψ = ∑ g : G, w g * ψ g := by
  unfold circulantEigenvalue
  refine Fintype.sum_equiv (Equiv.neg G) _ _ fun g => ?_
  simp [hw g]

/-- **Convolution multiplicativity**: the character eigenvalue of the convolution vector
`circulant u *ᵥ v` (which generates `circulant u * circulant v` via `Matrix.circulant_mul`) is the
product of the character eigenvalues of `u` and `v`. -/
theorem circulantEigenvalue_mulVec [CommSemiring R] (u v : G → R) (ψ : AddChar G R) :
    circulantEigenvalue (circulant u *ᵥ v) ψ =
      circulantEigenvalue u ψ * circulantEigenvalue v ψ := by
  have h1 := congrFun (circulant_mulVec_addChar (circulant u *ᵥ v) ψ) 0
  have h2 : (circulant (circulant u *ᵥ v) *ᵥ (⇑ψ)) 0 =
      (circulantEigenvalue u ψ * circulantEigenvalue v ψ) * ψ 0 := by
    rw [← circulant_mul, ← mulVec_mulVec, circulant_mulVec_addChar, mulVec_smul,
      circulant_mulVec_addChar, smul_smul]
    simp [mul_comm]
  simpa using h1.symm.trans h2

/-- Scalar homomorphisms commute with `circulantEigenvalue`. -/
theorem map_circulantEigenvalue {S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (w : G → R) (ψ : AddChar G R) :
    f (circulantEigenvalue w ψ) =
      circulantEigenvalue (f ∘ w) (f.toMonoidHom.compAddChar ψ) := by
  simp [circulantEigenvalue, map_sum, map_mul]

end Eigenvalues

end Matrix
