/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.TreeDecomposition.IndependentSet
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Fin.VecNotation

/-! # Maximum-weight independent sets over tree decompositions on small graphs

Kernel-checked runs of the tree-decomposition dynamic program, with no `native_decide`:

1. the weighted path `0 - 1 - 2 - 3` with weights `3, 5, 4, 1` and a width-one decomposition:
   the value `7` (attained by `{0, 2}`), the exact tick count `156` and the general time bound
   `216`, and the independence number `2` read off the unit-weight run;
2. the five-cycle with a width-two fan decomposition: the independence number `2` and a weighted
   value in which the best set avoids the heaviest vertex's neighbours;
3. a one-node decomposition of the edgeless graph on three vertices, where every vertex is chosen;
4. the star `K_{1,3}` with a root bag `{0}` and three children, which exercises the sum of
   several child messages: the independence number `3` and two weighted values.

The tick counts checked here are the declared cost of `mwisM` (see the module docstring of
`Complexity.Algorithms.Lean.TreeDecomposition.IndependentSet`), not a count of evaluation steps.
-/

public section

namespace Cslib.Tests.TreeDecompositionIndependentSet

open SimpleGraph Cslib.Algorithms.Lean Cslib.Algorithms.Lean.TreeDecomposition

/-! ### 1. A weighted path -/

/-- The path `0 - 1 - 2 - 3` with bags `{0, 1}`, `{1, 2}`, `{2, 3}` along the node path
`0 - 1 - 2`. -/
def pathDecomposition : (pathGraph 4).RootedTreeDecomposition 2 where
  parent := ![0, 0, 1]
  parent_zero := by decide
  parent_lt := by decide
  bag := ![{0, 1}, {1, 2}, {2, 3}]
  exists_mem_bag := by decide
  exists_adj_mem_bag := by decide
  top_unique := by decide

/-- Vertex weights `3, 5, 4, 1`. -/
def pathWeight : Fin 4 → ℕ := ![3, 5, 4, 1]

/-- The program returns `7`, the weight of `{0, 2}`. -/
example : mwisValue pathDecomposition pathWeight = 7 := by decide

example : (mwisM pathDecomposition pathWeight).ret = 7 := by
  rw [ret_mwisM]
  decide

/-- So no independent set of the weighted path weighs more than `7`, and `{0, 2}` attains it. -/
example : IsGreatest {x | ∃ I : Finset (Fin 4), (pathGraph 4).IsIndepSet (↑I : Set (Fin 4)) ∧
    ∑ v ∈ I, pathWeight v = x} 7 := by
  have h := isGreatest_mwisValue pathDecomposition pathWeight
  rwa [show mwisValue pathDecomposition pathWeight = 7 by decide] at h

/-- Two non-root nodes with bags of size two under bags of size two cost `stepCost 2 2 = 60`
each, and the root costs `rootCost 2 = 36`. -/
example : (mwisM pathDecomposition pathWeight).time = 156 := by decide

/-- The general bound for width one: `3 · nodeCost 2 = 216`. -/
example : (mwisM pathDecomposition pathWeight).time ≤ 216 :=
  (time_mwisM_le pathDecomposition pathWeight (k := 1)
    (pathDecomposition.width_le_iff.2 (by decide))).trans_eq (by decide)

/-- The unit-weight run computes the independence number of the path. -/
example : (pathGraph 4).indepNum = 2 := by
  rw [← mwisValue_one_eq_indepNum pathDecomposition]
  decide

/-! ### 2. The five-cycle -/

/-- The five-cycle `0 - 1 - 2 - 3 - 4 - 0`. -/
def cycle5 : SimpleGraph (Fin 5) where
  Adj i j := j.val = (i.val + 1) % 5 ∨ i.val = (j.val + 1) % 5
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun i h => by omega⟩

instance : DecidableRel cycle5.Adj := fun i j =>
  inferInstanceAs (Decidable (j.val = (i.val + 1) % 5 ∨ i.val = (j.val + 1) % 5))

/-- The fan decomposition of the five-cycle: bags `{0, 1, 2}`, `{0, 2, 3}`, `{0, 3, 4}` along
the node path `0 - 1 - 2`. -/
def cycleDecomposition : cycle5.RootedTreeDecomposition 2 where
  parent := ![0, 0, 1]
  parent_zero := by decide
  parent_lt := by decide
  bag := ![{0, 1, 2}, {0, 2, 3}, {0, 3, 4}]
  exists_mem_bag := by decide
  exists_adj_mem_bag := by decide
  top_unique := by decide

/-- The five-cycle has independence number two. -/
example : cycle5.indepNum = 2 := by
  rw [← mwisValue_one_eq_indepNum cycleDecomposition]
  decide

/-- With weights `1, 1, 10, 1, 1` the best independent set is `{0, 2}` or `{2, 4}`, of weight
`11`. -/
example : mwisValue cycleDecomposition ![1, 1, 10, 1, 1] = 11 := by decide

/-! ### 3. An edgeless graph with one bag -/

/-- The edgeless graph on three vertices with a single bag. -/
def bagDecomposition : (⊥ : SimpleGraph (Fin 3)).RootedTreeDecomposition 0 where
  parent := ![0]
  parent_zero := by decide
  parent_lt := by decide
  bag := ![{0, 1, 2}]
  exists_mem_bag := by decide
  exists_adj_mem_bag := by decide
  top_unique := by decide

/-- Every vertex is chosen, and only the root is charged: `rootCost 3 = 120`. -/
example : mwisValue bagDecomposition ![2, 3, 4] = 9 ∧
    (mwisM bagDecomposition ![2, 3, 4]).time = 120 := by
  decide

/-! ### 4. A star with three children -/

/-- The star `K_{1,3}` with centre `0` and leaves `1, 2, 3`. -/
def star : SimpleGraph (Fin 4) where
  Adj i j := i ≠ j ∧ (i = 0 ∨ j = 0)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel star.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ (i = 0 ∨ j = 0)))

/-- The star decomposition: root bag `{0}` and three children with bags `{0, ℓ}`, so the root
table is the sum of three child messages. -/
def starDecomposition : star.RootedTreeDecomposition 3 where
  parent := ![0, 0, 0, 0]
  parent_zero := by decide
  parent_lt := by decide
  bag := ![{0}, {0, 1}, {0, 2}, {0, 3}]
  exists_mem_bag := by decide
  exists_adj_mem_bag := by decide
  top_unique := by decide

/-- The unit-weight run sums the three leaf messages: the independence number is `3`. -/
example : star.indepNum = 3 := by
  rw [← mwisValue_one_eq_indepNum starDecomposition]
  decide

/-- With weights `2, 1, 1, 1` the three leaves (total `3`) beat the centre; with weights
`5, 1, 1, 1` the centre wins. -/
example : mwisValue starDecomposition ![2, 1, 1, 1] = 3 ∧
    mwisValue starDecomposition ![5, 1, 1, 1] = 5 := by
  decide

end Cslib.Tests.TreeDecompositionIndependentSet
