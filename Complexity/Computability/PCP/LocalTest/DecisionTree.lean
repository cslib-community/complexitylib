/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Basic
public import Complexity.Computability.PCP.LocalTest.Repetition
public import Mathlib.Data.FinEnum

/-!
# Executing Boolean local tests as decision trees

An explicit enumeration of the query layout turns a Boolean `LocalTest` into a decision tree
for each random string. The tree reads the listed positions and decides the existing acceptance
predicate from their answers. This preserves acceptance and makes at most `|Q|` queries. The
bound counts occurrences, including repeated positions, and certifies query cost; evaluating the
acceptance predicate is free in this decision-tree model.

## Main definitions

* `Cslib.PCP.LocalTest.decisionTree`: execute the queries of a Boolean local test in order.

## Main results

* `Cslib.PCP.LocalTest.eval_decisionTree`: execution decides the local test's acceptance.
* `Cslib.PCP.LocalTest.depth_decisionTree_le`: at most the query-layout cardinality is read.
* `Cslib.PCP.LocalTest.acceptProb_eq_expect_decisionTree`: the execution has the same acceptance
  probability as the local test.
* `Cslib.PCP.LocalTest.depth_decisionTree_repeatAll_le`: `k` trials make at most `k * |Q|` queries.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.PCP.LocalTest

open Finset
open scoped BigOperators

variable {P R Q : Type*} (T : LocalTest P R Q Bool) [FinEnum Q] [DecidableEq P]
variable [∀ r a, Decidable (T.Accepts r a)]

instance (r : R) (π : P → Bool) : Decidable (T.Passes π r) :=
  inferInstanceAs (Decidable (T.Accepts r fun q => π (T.query r q)))

/-- Read the positions in query order, then decide the test's acceptance from their values.
The enumeration and the acceptance decision are supplied explicitly by instances. -/
def decisionTree (r : R) : DecisionTree P Bool :=
  DecisionTree.queryAll (fun π => decide (T.Accepts r fun q => π (T.query r q)))
    ((FinEnum.toList Q).map (T.query r)) fun _ => false

/-- Executing a local test decides exactly its original acceptance predicate. -/
theorem eval_decisionTree (r : R) (π : P → Bool) :
    (T.decisionTree r).eval π = decide (T.Passes π r) := by
  rw [decisionTree, DecisionTree.eval_queryAll]
  have h (q : Q) : T.query r q ∈ (FinEnum.toList Q).map (T.query r) :=
    List.mem_map_of_mem (FinEnum.mem_toList q)
  simp only [ite_eq_left (h _), Passes]
  rfl

/-- Execution reads at most one position for each query-layout occurrence. -/
theorem depth_decisionTree_le (r : R) : (T.decisionTree r).depth ≤ FinEnum.card Q := by
  refine (DecisionTree.depth_queryAll_le _ _ _).trans_eq ?_
  simp only [List.length_map, FinEnum.toList, List.length_finRange]

/-- The distribution of acceptance decisions produced by execution agrees with `acceptProb`. -/
theorem acceptProb_eq_expect_decisionTree [Fintype R] (π : P → Bool) :
    T.acceptProb π = 𝔼 r, if (T.decisionTree r).eval π = true then (1 : ℝ) else 0 := by
  simp only [acceptProb, eval_decisionTree, decide_eq_true_eq]
  refine expect_congr rfl fun r _ => ?_
  split_ifs <;> rfl

/-- Executing `k` independent trials makes at most `k * |Q|` queries on every seed and input. -/
theorem depth_decisionTree_repeatAll_le (k : ℕ) (r : Fin k → R) :
    ((T.repeatAll k).decisionTree r).depth ≤ k * FinEnum.card Q := by
  refine ((T.repeatAll k).depth_decisionTree_le r).trans_eq ?_
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_prod, Fintype.card_fin,
    FinEnum.card_eq_fintypeCard]

end Cslib.PCP.LocalTest
