/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.QueryComplexity.AndOrTree.Randomized

/-! Clients and axiom guards for the evasiveness of the AND–OR tree, dual decision trees and the
zero-error directional algorithm. -/

namespace ComplexityTests.AndOrTree

open Cslib Cslib.QueryComplexity Cslib.QueryComplexity.NandTree Cslib.RandomizedDecisionTree

/-! ### The two orientations -/

/-- The input whose leaf is `true` exactly in the right half. -/
def rightHalf : (Fin 2 → Bool) → Bool := fun p => p 0

/-- `T_{2,1}` puts AND at the root: `(0 ∨ 0) ∧ (1 ∨ 1) = 0`. -/
example : andOrTree 1 rightHalf = false := by decide

/-- The OR–AND tree puts OR at the root: `(0 ∧ 0) ∨ (1 ∧ 1) = 1`. -/
example : orAndTree 1 rightHalf = true := by decide

example : orAndTree 1 rightHalf = nandTree 2 rightHalf := by
  rw [orAndTree_eq_nandTree]

example : andOrTree 1 rightHalf = !orAndTree 1 fun p => !rightHalf p :=
  andOrTree_eq_not_orAndTree 1 rightHalf

/-! ### Dual decision trees -/

/-- The conjunction of two bits. -/
def andTree : DecisionTree (Fin 2) Bool :=
  .node 0 (.leaf false) (.node 1 (.leaf false) (.leaf true))

/-- The dual of the AND tree computes OR. -/
example : andTree.dual.Computes fun x => x 0 || x 1 := by
  unfold DecisionTree.Computes
  decide

example : andTree.dual.dual = andTree := DecisionTree.dual_dual andTree

example : DecisionTree.complexity (fun x : Fin 2 → Bool => !(!x 0 && !x 1)) =
    DecisionTree.complexity fun x : Fin 2 → Bool => x 0 && x 1 :=
  DecisionTree.complexity_dual fun x => x 0 && x 1

/-! ### Evasiveness -/

/-- `D(T_{2,1}) = 4`: every leaf must be read. -/
example : DecisionTree.complexity (andOrTree 1) = 4 := complexity_andOrTree 1

example : DecisionTree.complexity (nandTree 3) = 8 := complexity_nandTree 3

example {t : DecisionTree (Fin (2 * 2) → Bool) Bool} (ht : t.Computes (andOrTree 2)) :
    ∃ x, t.queries x = Finset.univ :=
  exists_queries_eq_univ_of_computes_andOrTree ht

/-! ### The directional algorithm -/

/-- The recurrence at depth `1`: on two `false` leaves the first leaf read decides, so one query
is made. -/
example : (directional 1).expectedCost (fun _ => false) = 1 := by
  simp only [expectedCost_directional_succ, expectedCost_directional_zero]
  simp

/-- On two `true` leaves both are read. -/
example : (directional 1).expectedCost (fun _ => true) = 2 := by
  simp only [expectedCost_directional_succ, expectedCost_directional_zero]
  norm_num

/-- On one `false` and one `true` leaf, the second leaf is read only if the `true` leaf comes
first, with probability `1 / 2`. -/
example : (directional 1).expectedCost (fun p => p 0) = 3 / 2 := by
  simp only [expectedCost_directional_succ, expectedCost_directional_zero]
  norm_num

example : (directional 2).Computes 0 (nandTree 2) := directional_computes 2

/-! ### Zero-error complexity -/

/-- `R₀(T_{2,1}) ≤ 3 < 4 = D(T_{2,1})`. -/
example : zeroErrorComplexity (andOrTree 1) ≤ 3 ∧
    zeroErrorComplexity (andOrTree 1) < DecisionTree.complexity (andOrTree 1) := by
  refine ⟨?_, zeroErrorComplexity_andOrTree_lt_complexity one_ne_zero⟩
  simpa using zeroErrorComplexity_andOrTree_le 1

example : 0 ≤ zeroErrorComplexity (andOrTree 2) := zeroErrorComplexity_nonneg

example (k : ℕ) : zeroErrorComplexity (orAndTree k) ≤ 3 ^ k := zeroErrorComplexity_orAndTree_le k

/-- `R₀` never exceeds `D`. -/
example : zeroErrorComplexity (fun x : Fin 2 → Bool => x 0 && x 1) ≤
    DecisionTree.complexity fun x : Fin 2 → Bool => x 0 && x 1 :=
  zeroErrorComplexity_le_complexity _

/-! ### Axiom guards -/

/-- info: 'Cslib.QueryComplexity.complexity_andOrTree' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms complexity_andOrTree

/-- info: 'Cslib.QueryComplexity.zeroErrorComplexity_andOrTree_lt_complexity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zeroErrorComplexity_andOrTree_lt_complexity

/-- info: 'Cslib.QueryComplexity.NandTree.expectedCost_directional_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expectedCost_directional_le

end ComplexityTests.AndOrTree
