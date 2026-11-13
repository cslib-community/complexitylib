/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.IsolatedBasis
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Weights isolating a spanning set: concrete checks

For the constant family `1` of rational numbers indexed by `{0, 1, 2}` and the identity weight,
the set `{0}` is isolated: the vectors at `1` and `2` are multiples of the vector at `0`, which
has smaller weight. The general construction gives a set with at most one element, also for a
product of two such families.
-/

public section

namespace CslibFrontierTests.IsolatedBasis

open scoped Pointwise

open Cslib

/-- The identity weight isolates `{0}` inside `{0, 1, 2}` for the constant family `1`. -/
theorem isolates_const : Isolates ℚ id (fun _ : ℕ => (1 : ℚ)) {0, 1, 2} {0} := by
  refine ⟨by simp, by simp, fun m hm hm0 => Submodule.subset_span ⟨0, ⟨by simp, ?_⟩, rfl⟩⟩
  exact Nat.pos_of_ne_zero (by simpa using hm0)

/-- The set `{0, 1}` is not isolated inside itself by a constant weight: the weight is not
injective on it. -/
theorem not_isolates_const_weight :
    ¬ Isolates ℚ (fun _ => 0) (fun _ : ℕ => (1 : ℚ)) {0, 1} {0, 1} := fun h =>
  absurd (h.2.1 (by simp) (by simp) rfl : (0 : ℕ) = 1) (by decide)

/-- An injective weight isolates a set with at most one element in a one-dimensional space. -/
theorem exists_isolates_const :
    ∃ S, S.card ≤ 1 ∧ Isolates ℚ id (fun _ : ℕ => (1 : ℚ)) {0, 1, 2} S := by
  simpa using exists_isolates_of_injOn (F := ℚ) (D := fun _ : ℕ => (1 : ℚ)) (T := {0, 1, 2})
    (Set.injOn_id _)

/-- Isolation for the product of two constant families. -/
theorem exists_isolates_const_add :
    ∃ S ⊆ ({0} + {0} : Finset ℕ), S.card ≤ 1 ∧
      Isolates ℚ (AddMonoidHom.id ℕ) (fun _ : ℕ => (1 : ℚ)) ({0, 1, 2} + {0}) S := by
  simpa using exists_isolates_add (wt := AddMonoidHom.id ℕ) isolates_const
    (⟨subset_rfl, by simp, by simp⟩ : Isolates ℚ id (fun _ : ℕ => (1 : ℚ)) {0} {0})
    (D := fun _ => 1) (by simp) (by simp)

end CslibFrontierTests.IsolatedBasis
