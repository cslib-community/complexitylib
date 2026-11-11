/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Words as sign vectors

A word `f : X → Bool` over a finite set of positions is read as the vector of signs
`signWord f = (signVal (f x))_x` in `EuclideanSpace ℝ X`. The inner product of two such vectors is
the sign correlation `∑ x, signVal (f x) * signVal (g x)` (`BitString.inner_signWord`), and each
has squared norm `|X|` (`BitString.norm_signWord_sq`). This lets inequalities for vectors in a
real inner product space, such as the Cauchy–Schwarz inequality, apply to Boolean words.

## Main definitions

* `Cslib.BitString.signWord`: the sign vector of a word.

## Main results

* `Cslib.BitString.inner_signWord`: inner products of sign vectors are sign correlations.
* `Cslib.BitString.norm_signWord_sq`: a sign vector has squared norm `|X|`.
-/

public section

namespace Cslib.BitString

open scoped RealInnerProductSpace

variable {X : Type*} [Fintype X]

/-- The `±1` word of a Boolean function, as a vector of `EuclideanSpace ℝ X`. -/
noncomputable def signWord (f : X → Bool) : EuclideanSpace ℝ X :=
  WithLp.toLp 2 fun x => signVal (f x)

/-- The inner product of two sign vectors is the sign correlation of the words. -/
theorem inner_signWord (f g : X → Bool) :
    ⟪signWord f, signWord g⟫ = ∑ x, signVal (f x) * signVal (g x) := by
  simp [signWord, PiLp.inner_apply, mul_comm]

/-- A sign vector has squared norm `|X|`. -/
theorem norm_signWord_sq (f : X → Bool) : ‖signWord f‖ ^ 2 = Fintype.card X := by
  rw [← real_inner_self_eq_norm_sq, inner_signWord]
  simp [signVal_mul_self]

end Cslib.BitString
