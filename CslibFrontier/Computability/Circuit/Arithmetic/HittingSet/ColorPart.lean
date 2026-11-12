/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The part of a polynomial that uses every colour once

A colouring `c : σ → Fin r` of the variables gives every monomial a colour degree: the vector
of its degrees in the variables of each colour. This is the weighted degree for the weight
`colorWeight c`, with values in `Fin r →₀ ℕ`. The *colour part* `colorPart c f` of a polynomial
is its component of colour degree `(1, …, 1)`: the sum of its monomials that contain exactly one
variable of each colour, to the first power. It is the polynomial `g_{a,h}` of
[Shpilka2026, eq. (3)–(4)], defined there as the coefficient of `y₁ ⋯ yᵣ` after multiplying
every variable of colour `i` by a new variable `yᵢ`.

## Main definitions

* `colorWeight`: the weight whose weighted degree is the colour degree.
* `colorPart`: the component of colour degree `(1, …, 1)`.

## References

* [A. Shpilka, *Polynomial-size hitting sets for multilinear any-order read-once algebraic
  branching programs and for set-multilinear depth-3 circuits with constant-size variable
  sets*][Shpilka2026], §3 (unrefereed preprint)
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial

variable {σ F : Type*} [CommSemiring F] {r : ℕ}

/-- The weight of a variable: one in the coordinate of its colour. -/
noncomputable def colorWeight (c : σ → Fin r) (v : σ) : Fin r →₀ ℕ := Finsupp.single (c v) 1

variable (r) in
/-- The colour degree `(1, …, 1)`. -/
noncomputable def colorOnes : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1

/-- The sum of the monomials of a polynomial that contain exactly one variable of each colour,
to the first power. -/
noncomputable def colorPart (c : σ → Fin r) : MvPolynomial σ F →ₗ[F] MvPolynomial σ F :=
  weightedHomogeneousComponent (colorWeight c) (colorOnes r)

end Cslib.Circuits.Arithmetic
