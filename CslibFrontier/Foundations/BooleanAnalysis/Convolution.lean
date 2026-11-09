/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Tactic.Ring

/-!
# Convolution on the Boolean cube

Bit strings add coordinatewise modulo two, `(x + y) i = (x i ^^ y i)`, through Mathlib's Boolean
ring structure on `Bool`. Adding a fixed string permutes the cube, so the uniform expectation is
translation invariant (`Fintype.expect_add_left`), and the characters turn sums into products
(`BitString.chi_add`). The *convolution* of two real functions on the cube averages
`f y * g (x + y)` over `y` (`BitString.convolution`); it is commutative
(`BitString.convolution_comm`), and its Fourier coefficients are the products of the coefficients
of the factors (`BitString.fourierCoeff_convolution`) [O'Donnell, Section 1.5][ODonnell2014].

## Main definitions

* `Cslib.BitString.convolution`: the convolution of two real functions on the cube.

## Main results

* `Cslib.BitString.convolution_comm`: convolution is commutative.
* `Cslib.BitString.fourierCoeff_convolution`: the convolution theorem.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The convolution of two real functions on the cube: `(f ∗ g) x = 𝔼_y f y * g (x + y)`
[O'Donnell, Definition 1.24][ODonnell2014]. -/
noncomputable def convolution (f g : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  𝔼 y, f y * g (x + y)

/-- Convolution is commutative. -/
theorem convolution_comm (f g : (ι → Bool) → ℝ) : convolution f g = convolution g f := by
  funext x
  rw [convolution, ← Fintype.expect_add_left _ x]
  simp only [BitString.add_cancel_left]
  exact expect_congr rfl fun y _ => mul_comm _ _

/-- **The convolution theorem**: the Fourier coefficients of a convolution are the products of
the Fourier coefficients of the factors [O'Donnell, Theorem 1.27][ODonnell2014]. -/
theorem fourierCoeff_convolution (f g : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (convolution f g) S = fourierCoeff f S * fourierCoeff g S := by
  have h (y : ι → Bool) : 𝔼 x, g (x + y) * chi ℝ S x = chi ℝ S y * fourierCoeff g S := by
    rw [← Fintype.expect_add_left _ y, fourierCoeff, mul_expect]
    simp only [add_comm y, BitString.add_cancel_right, chi_add]
    exact expect_congr rfl fun x _ => by ring
  rw [fourierCoeff, fourierCoeff]
  simp only [convolution, expect_mul, mul_assoc]
  rw [expect_comm]
  simp only [← mul_expect, h]

end Cslib.BitString
