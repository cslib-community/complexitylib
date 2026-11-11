/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.TreeDecomposition.IndependentSetFPT
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Fin.VecNotation
meta import CslibFrontier.Algorithms.Lean.TreeDecomposition.IndependentSetFPT
meta import Mathlib.Combinatorics.SimpleGraph.Hasse
meta import Mathlib.Data.Fin.VecNotation

/-! # Maximum-weight independent sets over tree decompositions on small graphs

Kernel-checked runs of the tree-decomposition dynamic program, with no `native_decide`:

1. the weighted path `0 - 1 - 2 - 3` with weights `3, 5, 4, 1` and a width-one decomposition:
   the value `7` (attained by `{0, 2}`) and the independence number `2` read off the unit-weight
   run;
2. the five-cycle with a width-two fan decomposition: the independence number `2` and a weighted
   value in which the best set avoids the heaviest vertex's neighbours;
3. a one-node decomposition of the edgeless graph on three vertices, where every vertex is chosen;
4. the star `K_{1,3}` with a root bag `{0}` and three children, which exercises the sum of
   several child messages: the independence number `3` and two weighted values;
5. the executable program `mwisFPT` on the same decompositions: its values, its exact tick counts
   `273` on the weighted path and `97` on the single bag, a bag ordering that `IsBagOrder`
   rejects, and a compiled run on the orderings built by `sortedBags`;
6. a family of path decompositions of every depth `N`, on which `mwisFPT` takes exactly
   `120 N + 33` ticks, linear in the depth. The program is evaluated by `decide +kernel` at depth
   `40` and by `#guard` at depth `2000`.

Items 1 to 4 evaluate the specification `mwisValue`. The tick counts of items 5 and 6 are charged
inside the loops of `mwisFPT`.
-/

-- The `#guard` checks of sections 5 and 6 run the compiled program, at depth `2000` beyond the
-- reach of `decide`, and on `sortedBags`, which is not exposed.
set_option linter.hashCommand false

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

/-- So no independent set of the weighted path weighs more than `7`, and `{0, 2}` attains it. -/
example : IsGreatest {x | ∃ I : Finset (Fin 4), (pathGraph 4).IsIndepSet (↑I : Set (Fin 4)) ∧
    ∑ v ∈ I, pathWeight v = x} 7 := by
  have h := isGreatest_mwisValue pathDecomposition pathWeight
  rwa [show mwisValue pathDecomposition pathWeight = 7 by decide] at h

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

/-- Every vertex is chosen. -/
example : mwisValue bagDecomposition ![2, 3, 4] = 9 := by decide

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

/-! ### 5. The executable program -/

/-- The bags of `pathDecomposition`, in increasing order. -/
def pathBags : Fin 3 → List (Fin 4) := ![[0, 1], [1, 2], [2, 3]]

example : IsBagOrder pathDecomposition pathBags := by decide

/-- A list with a repeated vertex is not a bag ordering. -/
example : ¬IsBagOrder pathDecomposition ![[0, 1, 0], [1, 2], [2, 3]] := by decide

example : (mwisFPT pathDecomposition pathWeight pathBags).ret = 7 := by decide

/-- The executed tick count. The two nonroot nodes have bags of size `2` under bags of size `2`.
Each costs `processTime 2 2 = 119`: `3` for the bookkeeping, `4` to allocate `best`, `4 · 19` for
the four child masks (independence test `3`, parent-bag mask `6`, forgotten weight `6`, table
update `4`), and `4 · 9` for the four parent masks (restriction `6`, table update `3`). The root
costs `rootPassTime 2 = 4 · 8 = 32` and allocating the three tables costs `3`. -/
example : (mwisFPT pathDecomposition pathWeight pathBags).time = 273 := by decide

example : (mwisFPT pathDecomposition pathWeight pathBags).time = 3 + 2 * 119 + 32 := by
  rw [time_mwisFPT]
  decide

/-- The general bound for width one: `3 · fptNodeBound 2 = 408`. -/
example : (mwisFPT pathDecomposition pathWeight pathBags).time ≤ 408 :=
  (time_mwisFPT_le pathDecomposition pathWeight (by decide) (k := 1)
    (pathDecomposition.width_le_iff.2 (by decide))).trans_eq (by decide)

example : (mwisFPT cycleDecomposition ![1, 1, 10, 1, 1]
    ![[0, 1, 2], [0, 2, 3], [0, 3, 4]]).ret = 11 := by
  decide

/-- On the single bag only the root pass runs: `1` tick allocates the table and
`rootPassTime 3 = 8 · (6 + 3 + 3) = 96` ticks scan the eight root masks. -/
example : (mwisFPT bagDecomposition ![2, 3, 4] ![[0, 1, 2]]).ret = 9 ∧
    (mwisFPT bagDecomposition ![2, 3, 4] ![[0, 1, 2]]).time = 97 := by
  decide

example : (mwisFPT starDecomposition ![2, 1, 1, 1] ![[0], [0, 1], [0, 2], [0, 3]]).ret = 3 ∧
    (mwisFPT starDecomposition ![5, 1, 1, 1] ![[0], [0, 1], [0, 2], [0, 3]]).ret = 5 := by
  decide

/-- The independence number of the star, from the executable program. -/
example : star.indepNum = 3 := by
  rw [← mwisFPT_one_eq_indepNum starDecomposition
    (L := ![[0], [0, 1], [0, 2], [0, 3]]) (by decide)]
  decide

/-! ### 6. Deep path decompositions -/

/-- The path decomposition of the path on `N + 2` vertices: node `i` has bag `{i, i + 1}` and
parent `i - 1`, so the decomposition is a path of depth `N`. -/
def deepPath (N : ℕ) : (pathGraph (N + 2)).RootedTreeDecomposition N where
  parent i := ⟨i.val - 1, by omega⟩
  parent_zero := rfl
  parent_lt i hi := by
    have : i.val ≠ 0 := fun h => hi (Fin.ext h)
    rw [Fin.lt_def]
    simp only
    omega
  bag i := {⟨i.val, by omega⟩, ⟨i.val + 1, by omega⟩}
  exists_mem_bag v := ⟨⟨v.val - 1, by omega⟩, by
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega⟩
  exists_adj_mem_bag u v h := by
    rw [pathGraph_adj] at h
    refine ⟨⟨min u.val v.val, by omega⟩, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega
  top_unique v i j hi hi' hj hj' := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_zero] at hi hi' hj hj'
    ext
    omega

/-- The bags of `deepPath N` in increasing order. -/
def deepBags (N : ℕ) : Fin (N + 1) → List (Fin (N + 2)) :=
  fun i => [⟨i.val, by omega⟩, ⟨i.val + 1, by omega⟩]

theorem isBagOrder_deepBags (N : ℕ) : IsBagOrder (deepPath N) (deepBags N) := fun i =>
  ⟨by simp [deepBags, Fin.ext_iff], by simp [deepBags, deepPath]⟩

/-- On the path decomposition of depth `N` the program takes `120 N + 33` ticks, linear in the
depth: each nonroot node costs `processTime 2 2 + 1 = 120`. -/
theorem time_mwisFPT_deepPath (N : ℕ) (w : Fin (N + 2) → ℕ) :
    (mwisFPT (deepPath N) w (deepBags N)).time = 120 * N + 33 := by
  have h₁ : processTime 2 2 = 119 := by decide
  have h₂ : rootPassTime 2 = 32 := by decide
  rw [time_mwisFPT]
  simp only [deepBags, List.length_cons, List.length_nil, Nat.reduceAdd, h₁, h₂,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

/-- With unit weights it returns the independence number `21` of the path on `42` vertices. -/
example : (mwisFPT (deepPath 40) (fun _ => 1) (deepBags 40)).ret = 21 := by decide +kernel

example : (pathGraph 42).indepNum = 21 := by
  rw [← mwisFPT_one_eq_indepNum (deepPath 40) (isBagOrder_deepBags 40)]
  decide +kernel

/- Compiled evaluation at depth `2000`, where the tick count is `120 · 2000 + 33`. -/
#guard (mwisFPT (deepPath 2000) (fun _ => 1) (deepBags 2000)).ret == 1001
#guard (mwisFPT (deepPath 2000) (fun _ => 1) (deepBags 2000)).time == 120 * 2000 + 33

/-- `sortedBags` orders the bags of a decomposition of a linearly ordered vertex type, so
`ret_mwisFPT` applies to it. -/
example : (mwisFPT pathDecomposition pathWeight (sortedBags pathDecomposition)).ret = 7 := by
  rw [ret_mwisFPT _ _ (isBagOrder_sortedBags _)]
  decide

/- The compiled program on the orderings built by `sortedBags`, which `decide` cannot unfold. -/
#guard (mwisFPT pathDecomposition pathWeight (sortedBags pathDecomposition)).ret == 7
#guard (mwisFPT cycleDecomposition ![1, 1, 10, 1, 1] (sortedBags cycleDecomposition)).ret == 11

end Cslib.Tests.TreeDecompositionIndependentSet
