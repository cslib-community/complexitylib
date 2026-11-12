/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Hitting sets

A finite set `H` of points is a *hitting set* for a class `𝒞` of polynomials if every nonzero
polynomial of `𝒞` is nonzero at some point of `H`. A hitting set for `𝒞` gives a deterministic
black-box identity test for `𝒞`: evaluate at the points of `H`. The definition concerns formal
polynomials and points of the coefficient ring; it does not model the cost of evaluation or the
bit length of the points.

## Main definitions

* `Cslib.Circuits.Arithmetic.IsHittingSet`: `H` hits every nonzero polynomial of `𝒞`.

## Main results

* `IsHittingSet.mono`: a larger set hits a smaller class.
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

variable {F σ : Type*} [CommSemiring F]

/-- A finite set of points is a hitting set for a class of polynomials if every nonzero
polynomial of the class is nonzero at one of the points. -/
def IsHittingSet (H : Finset (σ → F)) (𝒞 : Set (MvPolynomial σ F)) : Prop :=
  ∀ f ∈ 𝒞, f ≠ 0 → ∃ a ∈ H, MvPolynomial.eval a f ≠ 0

/-- A larger set of points hits a smaller class. -/
theorem IsHittingSet.mono {H H' : Finset (σ → F)} {𝒞 𝒞' : Set (MvPolynomial σ F)}
    (h : IsHittingSet H 𝒞) (hH : H ⊆ H') (h𝒞 : 𝒞' ⊆ 𝒞) : IsHittingSet H' 𝒞' :=
  fun f hf hf0 => (h f (h𝒞 hf) hf0).imp fun _ ha => ⟨hH ha.1, ha.2⟩

end Cslib.Circuits.Arithmetic
