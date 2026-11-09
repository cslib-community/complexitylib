/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.HashFamily
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fintype.Pi
import Complexity.Probability.LinearCombination

/-!
# Uniform finite-field matrix hashing

A uniform matrix over a finite field maps every nonzero vector to a uniform vector. Consequently,
ordinary matrix-vector multiplication satisfies the existing `IsDeltaUniversalHash` predicate.
These are finite probability laws, with no claim about sampling the matrix with bounded fair coins.

## Main results

* `uniformOfFintype_map_mulVec`: uniform output at each fixed nonzero input.
* `isDeltaUniversalHash_mulVec`: distinct inputs have uniformly distributed hash differences.

The proofs reuse surjectivity of scalar linear combinations and uniformity under surjective
additive homomorphisms. These elementary API lemmas are original; the universality predicate is
the existing one from `Probability.HashFamily`.
-/

public section

namespace Cslib.Probability

open scoped Matrix ENNReal

variable {ι κ F : Type} [Fintype ι] [Fintype κ] [Field F] [Fintype F]
  [DecidableEq ι] [DecidableEq κ]

/-- A uniform finite-field matrix sends a fixed nonzero vector to a uniform vector. -/
theorem uniformOfFintype_map_mulVec (x : κ → F) (hx : x ≠ 0) :
    (PMF.uniformOfFintype (Matrix ι κ F)).map (fun A => A *ᵥ x) =
      PMF.uniformOfFintype (ι → F) := by
  classical
  let transform : Matrix ι κ F →+ (ι → F) := {
    toFun := fun A => A *ᵥ x
    map_zero' := Matrix.zero_mulVec x
    map_add' := fun A B => Matrix.add_mulVec A B x }
  apply PMF.uniformOfFintype_map_addHom transform
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  intro y
  choose row hrow using fun i => linearCombAddHom_surjective hj (y i)
  refine ⟨Matrix.of row, ?_⟩
  funext i
  change (Matrix.of row *ᵥ x) i = y i
  simpa only [Matrix.mulVec, dotProduct, Matrix.of_apply, linearCombAddHom_apply] using hrow i

/-- Finite-field matrices are delta-universal under their uniform law: the difference at any
two distinct inputs hits each output with probability exactly the reciprocal output cardinality.
The predicate records the resulting upper bound. -/
theorem isDeltaUniversalHash_mulVec :
    IsDeltaUniversalHash (PMF.uniformOfFintype (Matrix ι κ F)) (fun A x => A *ᵥ x)
      (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ := by
  apply IsDeltaUniversalHash.of_map_sub_eq_uniform
  intro x y hxy
  simp only [← Matrix.mulVec_sub]
  exact uniformOfFintype_map_mulVec (x - y) (sub_ne_zero.mpr hxy)

end Cslib.Probability
