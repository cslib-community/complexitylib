/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract tests)

import CslibFrontierAbstracts.CommunicationAbstract

/-! # Concrete clients of the communication abstract

Check that its cost/error conditions admit actual protocols and that its finite disjointness
bound excludes a small communication budget.
-/

namespace CslibFrontierTests.Abstracts.CommunicationTests

open CslibFrontierAbstracts.CommunicationAbstract

/-- Alice sends her bit, and Bob sends the equality verdict. -/
def oneBitEquality : Protocol 1 :=
  .alice (fun x => x 0)
    (.bob (fun y => !y 0) (.output false) (.output true))
    (.bob (fun y => y 0) (.output false) (.output true))

example : cost oneBitEquality = 2 := rfl

example : ∀ x y, answer oneBitEquality x y = decide (x = y) := by decide

example : (∃ p : Protocol 1,
    (∀ x y, answer p x y = decide (x = y)) ∧ cost p ≤ 1) ↔ False := by
  rw [equality (by decide)]
  decide

-- On zero positions, disjointness is true and the inner product is false.
example (x y : Input 0) : disjoint x y = true ∧ innerProduct x y = false := by
  simp [disjoint, innerProduct, Bool.zero_eq_false]

/-- A point mass on an explicit correct tree meets both public conditions. -/
example : CostAtMost (PMF.pure oneBitEquality) 2 ∧
    ErrorAtMost (PMF.pure oneBitEquality) (fun x y => decide (x = y)) 0 := by
  constructor
  · intro p hp
    rw [(PMF.mem_support_pure_iff _ _).mp hp]
    exact le_rfl
  · intro x y
    have h : answer oneBitEquality x y = decide (x = y) := by decide +revert
    simp [PMF.toOuterMeasure_pure_apply, h]

-- This finite consequence is nontrivial despite the large disjointness constants.
example (μ : RandomizedProtocol (2 ^ 20)) (hc : CostAtMost μ 15)
    (he : ErrorAtMost μ disjoint (1 / 3)) : False := by
  have h := disjointness_lower_bound μ hc he
  norm_num at h

end CslibFrontierTests.Abstracts.CommunicationTests
