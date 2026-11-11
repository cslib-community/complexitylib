/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import Mathlib.Algebra.MvPolynomial.Supported

/-!
# The rank of a polynomial across a split of its variables

For a set `U` of variables, a polynomial `f` has *split rank at most `w` across `U`*
(`MvPolynomial.SplitRankLE U w f`) if it is a sum of `w` products `p * q` with `p` a polynomial in
the variables of `U` and `q` a polynomial in the other variables. Over a field this says that the
matrix of coefficients of `f`, with rows indexed by the monomials in `U` and columns by the
monomials in the complement, has rank at most `w`; by Nisan's characterisation a
polynomial computed by a read-once oblivious branching program of width `w` in an order that reads
`U` first has this property. The decomposition form is the one used here: it is preserved by every
substitution that keeps the two sets of variables apart, with no matrix in sight.

## Main definitions

* `MvPolynomial.SplitRankLE`: a decomposition into `w` products across a split of the variables.
-/

@[expose] public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- `f` is a sum of `w` products of a polynomial in the variables of `U` and a polynomial in the
other variables. -/
def SplitRankLE (U : Set σ) (w : ℕ) (f : MvPolynomial σ R) : Prop :=
  ∃ p q : Fin w → MvPolynomial σ R,
    (∀ i, p i ∈ supported R U) ∧ (∀ i, q i ∈ supported R Uᶜ) ∧ f = ∑ i, p i * q i

end MvPolynomial
