/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ExactTriangle.Defs
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Integer triangle sums and magnitude bounds

## Main definitions

* `weightSum`: the sum of the three supplied integer edge weights.
* `WeightsBoundedBy`: a shared real bound on their absolute values.

## Main results

* `abs_weightSum_le`: a triangle's magnitude is at most three times the edge bound.

## References

Adapted from the weight sum and bound definitions in [Anthropic's
PaperStatements.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/PaperStatements.lean#L893-L914)
and the triangle inequality in its
[Hashing.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec3/Theorem17/Hashing.lean#L246-L255).
The existing `HasZeroTriangle` remains the decision predicate.
-/

@[expose] public section

namespace Cslib.Algorithms.ExactTriangle

variable {n : ℕ} (wAB wBC wAC : Fin n → Fin n → ℤ)

/-- Sum of the A–B, B–C and A–C weights at a triangle. -/
def weightSum (a b c : Fin n) : ℤ := wAB a b + wBC b c + wAC a c

/-- Every supplied edge weight has absolute value at most `U`. -/
def WeightsBoundedBy (U : ℝ) : Prop :=
  (∀ a b, ((|wAB a b| : ℤ) : ℝ) ≤ U) ∧
  (∀ b c, ((|wBC b c| : ℤ) : ℝ) ≤ U) ∧ ∀ a c, ((|wAC a c| : ℤ) : ℝ) ≤ U

/-- The three edge bounds imply a threefold bound on every triangle sum. -/
theorem abs_weightSum_le {U : ℝ} (h : WeightsBoundedBy wAB wBC wAC U) (a b c : Fin n) :
    ((|weightSum wAB wBC wAC a b c| : ℤ) : ℝ) ≤ 3 * U := by
  obtain ⟨hAB, hBC, hAC⟩ := h
  have habs : |weightSum wAB wBC wAC a b c| ≤ |wAB a b| + |wBC b c| + |wAC a c| :=
    abs_add_three _ _ _
  have hcast : ((|weightSum wAB wBC wAC a b c| : ℤ) : ℝ) ≤
      ((|wAB a b| : ℤ) : ℝ) + ((|wBC b c| : ℤ) : ℝ) + ((|wAC a c| : ℤ) : ℝ) := by
    exact_mod_cast habs
  linarith [hAB a b, hBC b c, hAC a c]

end Cslib.Algorithms.ExactTriangle
