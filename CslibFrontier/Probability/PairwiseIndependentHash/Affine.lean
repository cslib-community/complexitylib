/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PairwiseIndependentHash
import CslibFrontier.Probability.PairwiseIndependentHash.Shift
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# The affine hash family

For a finite field `F` and finite types `m` and `n`, the affine maps `x ↦ A x + b` from `n → F`
to `m → F`, with seed a matrix `A` and a vector `b` (`Cslib.Probability.affineHash`), form a
pairwise independent hash family (`Cslib.Probability.isPairwiseIndependentHash_affineHash`):
the map `A ↦ A x₁ - A x₂` is onto for `x₁ ≠ x₂`, so the shift criterion
`Cslib.Probability.isPairwiseIndependentHash_add_of_surjective` applies. Over `F = ZMod 2` these
are the affine maps of bit vectors used for the set lower bound protocol and in the lemma of
Valiant and Vazirani; the linear maps `x ↦ A x` over `ZMod 2` form one of the universal classes of
Carter and Wegman [CarterWegman1979].

## Main definitions

* `Cslib.Probability.affineHash`: the affine map `x ↦ A x + b` with seed `(A, b)`.

## Main results

* `Cslib.Probability.isPairwiseIndependentHash_affineHash`: the affine maps over a finite field
  form a pairwise independent hash family.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 8.2][AroraBarak09]
* [J. L. Carter, M. N. Wegman, *Universal classes of hash functions*][CarterWegman1979]
-/

@[expose] public section

namespace Cslib.Probability

open Finset
open scoped Matrix

section Def

variable {F m n : Type*} [NonUnitalNonAssocSemiring F] [Fintype n]

/-- The affine map `x ↦ A x + b` from `n → F` to `m → F`, with seed `(A, b)`. -/
def affineHash (p : Matrix m n F × (m → F)) (x : n → F) : m → F :=
  p.1 *ᵥ x + p.2

/-- The affine map with seed `(A, b)` sends `x` to `A x + b`. -/
@[simp]
theorem affineHash_apply (A : Matrix m n F) (b : m → F) (x : n → F) :
    affineHash (A, b) x = A *ᵥ x + b :=
  rfl

end Def

variable {F m n : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype m] [DecidableEq m]
  [Fintype n] [DecidableEq n]

/-- **The affine hash family is pairwise independent**: over a finite field `F`, the affine maps
`x ↦ A x + b` from `n → F` to `m → F`, for a uniformly random matrix `A` and vector `b`, form a
pairwise independent hash family. By the shift criterion it suffices that for `x₁ ≠ x₂` the
matrices `A` reach every difference `A x₁ - A x₂`. -/
theorem isPairwiseIndependentHash_affineHash :
    IsPairwiseIndependentHash (affineHash : Matrix m n F × (m → F) → (n → F) → m → F) :=
  isPairwiseIndependentHash_add_of_surjective
    (AddMonoidHom.pi Matrix.mulVec.addMonoidHomLeft) fun (x₁ x₂ : n → F) hx c => by
      obtain ⟨k, hk⟩ := Function.ne_iff.1 hx
      refine ⟨Matrix.of fun r s => if s = k then c r / (x₁ k - x₂ k) else 0, funext fun r => ?_⟩
      change (_ *ᵥ x₁) r - (_ *ᵥ x₂) r = c r
      rw [← Pi.sub_apply, ← Matrix.mulVec_sub]
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.sub_apply, ite_mul, zero_mul,
        sum_ite_eq', mem_univ, ite_true]
      exact div_mul_cancel₀ _ (sub_ne_zero.2 hk)

end Cslib.Probability
