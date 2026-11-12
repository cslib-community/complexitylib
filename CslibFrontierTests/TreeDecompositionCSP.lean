/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.TreeDecomposition.CSP
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Fin.VecNotation

/-! # Tree-decomposition CSP counting and decision tests

Kernel-checked tests (with no `native_decide`) exercising `cspCountNiceM`, `cspDecideNiceM`,
`cspCountRootedM`, `cspDecideRootedM`, `cspCountActiveRootedM`, `cspDecideActiveRootedM`, and the
finite-alphabet equivalence bridges `ret_cspCountNiceM_equiv` / `ret_cspDecideNiceM_equiv`:

1. Proper `3`-coloring (`Fin 3`) of the 4-vertex path `P₄`: `cspCountNiceM` evaluates by `decide`
   to `24` (`3 * 2 ^ 3`), `cspDecideNiceM` evaluates to `true`, explicit DP tick counts obey the
   certified `dpNodeCost` bounds, and `cspCountRootedM` / `cspDecideRootedM` match.
2. Proper `3`-coloring (`Fin 3`) of `K₄` on a single-bag width-3 decomposition: `cspCountNiceM`
   evaluates by `decide` to `0` and `cspDecideNiceM` certifies `¬Satisfiable`.
3. Active primal graph DP (`cspCountActiveRootedM`, `cspDecideActiveRootedM`) and the
   `Bool ≃ Fin 2` bridge (`ret_cspCountNiceM_equiv` / `ret_cspDecideNiceM_equiv`) on a Boolean `≠`
   constraint over `{0, 1}` inside `Fin 3` with an isolated variable `2`.
-/

public section

namespace Cslib.Tests.TreeDecompositionCSP

open SimpleGraph Cslib.Logic.PL Cslib.Algorithms.Lean Cslib.Algorithms.Lean.TreeDecomposition

/-! ### 1. Non-Boolean `3`-coloring (`Fin 3`) on `P₄` -/

/-- Binary inequality relation (`a ≠ b`). -/
@[expose] def neqSem (q : ℕ) : Unit → List (Fin q) → Bool
  | (), [a, b] => decide (a ≠ b)
  | (), _ => false

/-- `3`-coloring CSP on `P₄`: edges `0-1`, `1-2`, `2-3`. -/
@[expose] def path4CSP : CSP Unit (Fin 4) :=
  [((), [0, 1]), ((), [1, 2]), ((), [2, 3])]

/-- Concrete `NiceTree` covering edges `{0, 1}`, `{1, 2}`, `{2, 3}` with width `1`. -/
@[expose] def path4NiceTree : NiceTree (Fin 4) :=
  .forget 3 (.forget 2 (.introduce 3 (.forget 1 (.introduce 2 (.forget 0
    (.introduce 1 (.introduce 0 .leaf)))))))

/-- Nice tree decomposition of `path4CSP.primalGraph`. -/
def path4Nice : path4CSP.primalGraph.NiceTreeDecomposition where
  tree := path4NiceTree
  localValid := by decide
  bag_root := by decide
  exists_mem_bag := by decide
  exists_adj_mem_bag := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      first
      | exact absurd huv (by decide)
      | (simp only [path4NiceTree, NiceTree.CoversFinset.eq_1, NiceTree.CoversFinset.eq_2,
          NiceTree.CoversFinset.eq_3, NiceTree.bag]; decide)

/-- Width-1 rooted tree decomposition covering `path4CSP.primalGraph`. -/
def path4Rooted : path4CSP.primalGraph.RootedTreeDecomposition 2 where
  parent := ![0, 0, 1]
  parent_zero := by decide
  parent_lt := by decide
  bag := ![{0, 1}, {1, 2}, {2, 3}]
  exists_mem_bag := by decide
  exists_adj_mem_bag := by decide
  top_unique := by decide

private lemma pos3 : 0 < 3 := by decide

example : path4Nice.width = 1 := by decide
example : (cspCountNiceM 3 pos3 (neqSem 3) path4CSP path4Nice).ret = 24 := by decide
example : CSP.modelCount (neqSem 3) path4CSP = 24 := by
  rw [← ret_cspCountNiceM pos3 (neqSem 3) path4Nice]
  decide

example : (cspDecideNiceM 3 pos3 (neqSem 3) path4CSP path4Nice).ret = true := by decide
example : CSP.Satisfiable (neqSem 3) path4CSP :=
  (ret_cspDecideNiceM pos3 (neqSem 3) path4Nice).mp (by decide)

example :
    (cspCountNiceM 3 pos3 (neqSem 3) path4CSP path4Nice).time ≤
      path4Nice.size * (3 ^ (path4Nice.width + 1) * dpNodeCost path4Nice.width path4CSP) :=
  time_cspCountNiceM_le 3 pos3 (neqSem 3) path4CSP path4Nice

example :
    (cspDecideNiceM 3 pos3 (neqSem 3) path4CSP path4Nice).time ≤
      path4Nice.size * (3 ^ (path4Nice.width + 1) * dpNodeCost path4Nice.width path4CSP) :=
  time_cspDecideNiceM_le 3 pos3 (neqSem 3) path4CSP path4Nice

example : (cspCountRootedM 3 pos3 (neqSem 3) path4CSP path4Rooted).ret = 24 := by
  rw [ret_cspCountRootedM, ← ret_cspCountNiceM pos3 (neqSem 3) path4Nice]
  decide

example : (cspDecideRootedM 3 pos3 (neqSem 3) path4CSP path4Rooted).ret = true := by
  rw [ret_cspDecideRootedM]
  exact (ret_cspDecideNiceM pos3 (neqSem 3) path4Nice).mp (by decide)

/-! ### 2. Unsatisfiable `3`-coloring on `K₄` -/

/-- `K₄` all-pairs inequality CSP over `Fin 4`. -/
@[expose] def k4CSP : CSP Unit (Fin 4) :=
  [((), [0, 1]), ((), [0, 2]), ((), [0, 3]), ((), [1, 2]), ((), [1, 3]), ((), [2, 3])]

/-- Single-bag `NiceTree` over `Fin 4` introducing `{0, 1, 2, 3}` then forgetting all. -/
@[expose] def k4NiceTree : NiceTree (Fin 4) :=
  .forget 3 (.forget 2 (.forget 1 (.forget 0
    (.introduce 3 (.introduce 2 (.introduce 1 (.introduce 0 .leaf)))))))

/-- Nice decomposition of `k4CSP.primalGraph`. -/
def k4Nice : k4CSP.primalGraph.NiceTreeDecomposition where
  tree := k4NiceTree
  localValid := by decide
  bag_root := by decide
  exists_mem_bag := by decide
  exists_adj_mem_bag := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      first
      | exact absurd huv (by decide)
      | (simp only [k4NiceTree, NiceTree.CoversFinset.eq_1, NiceTree.CoversFinset.eq_2,
          NiceTree.CoversFinset.eq_3, NiceTree.bag]; decide)

example : (cspCountNiceM 3 pos3 (neqSem 3) k4CSP k4Nice).ret = 0 := by decide
example : CSP.modelCount (neqSem 3) k4CSP = 0 := by
  rw [← ret_cspCountNiceM pos3 (neqSem 3) k4Nice]
  decide
example : ¬CSP.Satisfiable (neqSem 3) k4CSP := by
  rw [← ret_cspDecideNiceM pos3 (neqSem 3) k4Nice]
  decide

/-! ### 3. Active primal graph and `Equiv Bool (Fin 2)` bridge -/

/-- Boolean inequality constraint only on variables `0` and `1` (leaving `2` unconstrained). -/
@[expose] def boolXorSem : Unit → List Bool → Bool
  | (), [a, b] => a != b
  | (), _ => false

/-- CSP on `Fin 3` constraining only `{0, 1}`. -/
@[expose] def activePairCSP : CSP Unit (Fin 3) :=
  [((), [0, 1])]

/-- Decomposition over `activePairCSP.activePrimalGraph`: variable `2` is omitted from all bags. -/
def activePairRooted : activePairCSP.activePrimalGraph.RootedTreeDecomposition 0 where
  parent := ![0]
  parent_zero := by decide
  parent_lt := by decide
  bag := ![{(⟨0, by decide⟩ : ↥activePairCSP.vars.toFinset),
    (⟨1, by decide⟩ : ↥activePairCSP.vars.toFinset)}]
  exists_mem_bag := by
    rintro ⟨v, hv⟩
    fin_cases v
    · exact ⟨0, Finset.mem_insert_self _ _⟩
    · exact ⟨0, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
    · exact absurd hv (by decide)
  exists_adj_mem_bag := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩ _
    refine ⟨0, ?_, ?_⟩
    · fin_cases u
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · exact absurd hu (by decide)
    · fin_cases v
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · exact absurd hv (by decide)
  top_unique := by
    rintro ⟨v, hv⟩ i j _ _ _ _
    fin_cases i; fin_cases j; rfl

/-- Explicit `NiceTree` over `Fin 3` covering `{0, 1}` and `2` for `Equiv Bool (Fin 2)`. -/
@[expose] def pairFullNiceTree : NiceTree (Fin 3) :=
  .forget 2 (.introduce 2 (.forget 1 (.forget 0 (.introduce 1 (.introduce 0 .leaf)))))

/-- Nice decomposition over `activePairCSP.primalGraph`. -/
def pairFullNice : activePairCSP.primalGraph.NiceTreeDecomposition where
  tree := pairFullNiceTree
  localValid := by decide
  bag_root := by decide
  exists_mem_bag := by decide
  exists_adj_mem_bag := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      first
      | exact absurd huv (by decide)
      | (simp only [pairFullNiceTree, NiceTree.CoversFinset.eq_1, NiceTree.CoversFinset.eq_2,
          NiceTree.CoversFinset.eq_3, NiceTree.bag]; decide)

private lemma pos2 : 0 < 2 := by decide

/-- `ret_cspCountNiceM_equiv` and `ret_cspDecideNiceM_equiv` recover `Bool` CSP model count `2`
and satisfiability directly from kernel evaluation on `pairFullNice` (ignoring isolated `2`). -/
example : CSP.modelCount boolXorSem activePairCSP = 2 := by
  rw [← ret_cspCountNiceM_equiv boolXorSem pairFullNice finTwoEquiv.symm]
  decide

example : CSP.Satisfiable boolXorSem activePairCSP :=
  (ret_cspDecideNiceM_equiv boolXorSem pairFullNice finTwoEquiv.symm).mp (by decide)

/-- Counting and decision on `activePairCSP.activePrimalGraph` match `CSP.modelCount` (`2`) and
`CSP.Satisfiable` (`true`). -/
example :
    (cspCountActiveRootedM 2 pos2 (semFin boolXorSem finTwoEquiv.symm)
        activePairCSP activePairRooted).ret = 2 ∧
      (cspDecideActiveRootedM 2 pos2 (semFin boolXorSem finTwoEquiv.symm)
        activePairCSP activePairRooted).ret = true := by
  have hc : CSP.modelCount boolXorSem activePairCSP = 2 := by
    rw [← ret_cspCountNiceM_equiv boolXorSem pairFullNice finTwoEquiv.symm]
    decide
  have hs : CSP.Satisfiable boolXorSem activePairCSP :=
    (ret_cspDecideNiceM_equiv boolXorSem pairFullNice finTwoEquiv.symm).mp (by decide)
  refine ⟨?_, ?_⟩
  · rw [ret_cspCountActiveRootedM, modelCount_semFin pos2 boolXorSem finTwoEquiv.symm, hc]
  · rw [ret_cspDecideActiveRootedM, satisfiable_semFin_iff boolXorSem finTwoEquiv.symm]
    exact hs

end Cslib.Tests.TreeDecompositionCSP
