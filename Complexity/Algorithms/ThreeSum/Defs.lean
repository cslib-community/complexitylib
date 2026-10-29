/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Int.Notation

/-!
# The distinct-position 3SUM problem

This is the input predicate of Anthropic's [pinned end statement](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/EndStatement.lean#L89),
without its source machine or running-time convention. Equal values at different positions are
allowed. In particular, three occurrences of zero are a solution, whereas one occurrence is not.

## Main definitions

* `HasSolution`: three distinct input positions whose integer values sum to zero.
-/

@[expose] public section

namespace Cslib.Algorithms.ThreeSum

/-- 3SUM on an integer array, requiring three different positions. Values may repeat. -/
def HasSolution {n : ℕ} (x : Fin n → ℤ) : Prop :=
  ∃ i j k, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ x i + x j + x k = 0

end Cslib.Algorithms.ThreeSum
