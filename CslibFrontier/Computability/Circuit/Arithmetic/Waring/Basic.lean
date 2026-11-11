/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Waring terms

A term is a scaled `d`-th power of a homogeneous linear form in `d` variables. Its coefficients
can be interpreted in another semiring, including the formal polynomial semiring. This module
is shared by the arithmetic compiler and the term-count lower bounds.

## Main definitions

* `Cslib.Circuits.Waring.Term`: a scale and a finite family of coefficient symbols.
* `Cslib.Circuits.Waring.Term.eval`: interpret the symbols and evaluate at an input.
* `Cslib.Circuits.Waring.Term.polynomial`: the represented formal polynomial.

## References

* Adapted from LowerBound/Fusion/SumOfTerms/Waring.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

@[expose] public section

namespace Cslib.Circuits.Waring

open MvPolynomial

/-- A scalar multiple of a `d`-th power of a homogeneous linear form in `d` variables. -/
structure Term (K : Type*) (d : ℕ) where
  /-- The scalar multiplying the power. -/
  scale : K
  /-- Coefficients of the homogeneous linear form. -/
  coefficients : Fin d → K

/-- Interpret the coefficient symbols and evaluate the scaled power. -/
def Term.eval {C R : Type*} [Semiring R] {d : ℕ} (t : Term C d)
    (constant : C → R) (x : Fin d → R) : R :=
  constant t.scale * (∑ i, constant (t.coefficients i) * x i) ^ d

/-- The polynomial represented by a Waring dictionary term. -/
noncomputable def Term.polynomial {K : Type*} [CommSemiring K] {d : ℕ}
    (t : Term K d) : MvPolynomial (Fin d) K :=
  C t.scale * (∑ i, t.coefficients i • X i) ^ d

end Cslib.Circuits.Waring
