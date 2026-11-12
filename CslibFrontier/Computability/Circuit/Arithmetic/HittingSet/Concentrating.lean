/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.MvPolynomial.SplitRank

/-!
# Concentrating points

A point `γ` with coordinates in an algebra `R` over a field `F` is *concentrating* for the
parameters `k`, `w`, `δ` (`IsConcentrating F γ k w δ`) if no nonzero `R`-combination of `w`
shifted polynomials in a set `Y` of `k` variables, of individual degree at most `δ`, has all
its monomials divisible by every variable of `Y`. This is the property of a shift used to
concentrate a polynomial of small split rank on monomials with few variables: it isolates the
part of the argument about `k` variables from the reduction to it.

## Main definitions

* `IsConcentrating`: the property of a point.
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial

variable {σ R : Type*} (F : Type*) [Field F] [CommRing R] [Algebra F R]

/-- For every set `Y` of `k` variables and polynomials `p i` in the variables of `Y`, a nonzero
combination `∑ i, ρ i • (p i) (X + γ)` of individual degree at most `δ` has a monomial that
misses a variable of `Y`. -/
def IsConcentrating (γ : σ → R) (k w δ : ℕ) : Prop :=
  ∀ Y : Finset σ, Y.card = k → ∀ p : Fin w → MvPolynomial σ F,
    (∀ i, p i ∈ supported F (Y : Set σ)) → ∀ ρ : Fin w → R,
      ∑ i, C (ρ i) * shift γ (p i) ≠ 0 →
        (∀ j, (∑ i, C (ρ i) * shift γ (p i)).degreeOf j ≤ δ) →
          ∃ m ∈ (∑ i, C (ρ i) * shift γ (p i)).support, ∃ j ∈ Y, m j = 0

end Cslib.Circuits.Arithmetic
