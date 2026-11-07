/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Lean.Matroid.Greedy
import Complexity.Algorithms.Lean.Query.Matroid.Greedy
import Complexity.Algorithms.Lean.Query.Matroid.LowerBound
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Data.Fintype.Fin

/-!
# Tests for Matroid Greedy Optimality and Independence-Oracle Query Bounds

Exercises:
1. Uniform matroid $U_{2,4}$ on `Fin 4`: maximum-weight basis, minimum-weight basis, negative-weight
   filtering (`matroidGreedyMaxIndep` making strictly fewer than `n` queries), and duplicate inputs.
2. Graphic (cycle) matroid of the 5-edge diamond graph on 4 vertices: Kruskal minimum-weight
   spanning tree via `matroidGreedyMinBasis` and certified optimality over all spanning trees.
3. Non-matroid hereditary matching system on the 3-edge path $P_4$: explicit greedy suboptimality
   (`3 < 4`) and formal refutation of matroid structure via the Rado–Edmonds characterization
   `exists_matroid_iff_forall_sum_le_greedyMaxBasis`.
4. Non-vacuity of `IsMatroidBasisAlg`, `IsMaxCardIndepAlg`, `UpperBound`, and `LowerBound` on the
   infinite ground type `ℕ` with matching bound `id`.
-/

namespace ComplexityTests.MatroidGreedy

open Cslib Cslib.Query Cslib.Algorithms.Lean.Matroid

/-! ## 1. Uniform matroid $U_{2,4}$ on `Fin 4` -/

private def u24Indep (S : Finset (Fin 4)) : Bool :=
  decide (S.card ≤ 2)

private def u24Oracle : {ι : Type} → IndepQuery (Fin 4) ι → ι :=
  IndepQuery.oracleOf u24Indep

private def u24Weights : Fin 4 → ℤ
  | 0 => -5
  | 1 => 10
  | 2 => 4
  | 3 => 7

section U24Checks
set_option linter.hashCommand false

-- Maximum-weight basis picks {1, 3} of weight 10 + 7 = 17 in 4 queries.
#guard (matroidGreedyMaxBasis u24Weights [0, 1, 2, 3]).eval u24Oracle == {1, 3}
example : (matroidGreedyMaxBasis u24Weights [0, 1, 2, 3]).eval u24Oracle = {1, 3} := by
  rw [eval_matroidGreedyMaxBasis, greedyMaxBasis_eq_insertionSort]
  decide
example : (matroidGreedyMaxBasis u24Weights [0, 1, 2, 3]).countQueries u24Oracle = 4 := by simp

-- Minimum-weight basis picks {0, 2} of weight -5 + 4 = -1 in 4 queries.
#guard (matroidGreedyMinBasis u24Weights [0, 1, 2, 3]).eval u24Oracle == {0, 2}
example : (matroidGreedyMinBasis u24Weights [0, 1, 2, 3]).eval u24Oracle = {0, 2} := by
  rw [eval_matroidGreedyMinBasis, greedyMinBasis_eq_insertionSort]
  decide
example : (matroidGreedyMinBasis u24Weights [0, 1, 2, 3]).countQueries u24Oracle = 4 := by simp

-- Duplicate candidates do not corrupt the basis output.
#guard (matroidGreedyMaxBasis u24Weights [1, 3, 1, 2, 0]).eval u24Oracle == {1, 3}
example : (matroidGreedyMaxBasis u24Weights [1, 3, 1, 2, 0]).eval u24Oracle = {1, 3} := by
  rw [eval_matroidGreedyMaxBasis, greedyMaxBasis_eq_insertionSort]
  decide

-- Mostly-negative weights: a basis must have size 2 (weight 6 + (-3) = 3), whereas
-- `matroidGreedyMaxIndep` filters negative candidates, selects `{1}` (weight 6), and makes only
-- 1 oracle query.
private def u24MostlyNeg : Fin 4 → ℤ
  | 0 => -10
  | 1 => 6
  | 2 => -3
  | 3 => -8

#guard (matroidGreedyMaxBasis u24MostlyNeg [0, 1, 2, 3]).eval u24Oracle == {1, 2}
#guard (matroidGreedyMaxIndep u24MostlyNeg [0, 1, 2, 3]).eval u24Oracle == {1}
#guard (matroidGreedyMaxIndep u24MostlyNeg [0, 1, 2, 3]).countQueries u24Oracle == 1
example : (matroidGreedyMaxBasis u24MostlyNeg [0, 1, 2, 3]).eval u24Oracle = {1, 2} := by
  rw [eval_matroidGreedyMaxBasis, greedyMaxBasis_eq_insertionSort]
  decide
example : (matroidGreedyMaxIndep u24MostlyNeg [0, 1, 2, 3]).eval u24Oracle = {1} := by
  rw [eval_matroidGreedyMaxIndep, greedyMaxIndep, greedyMaxBasis_eq_insertionSort]
  decide
example : (matroidGreedyMaxIndep u24MostlyNeg [0, 1, 2, 3]).countQueries u24Oracle = 1 := by
  simp [u24MostlyNeg]

end U24Checks

/-! ## 2. Graphic matroid of the 5-edge diamond graph (Kruskal MST) -/

/-- Acyclicity test for the 5-edge diamond graph on vertices `{0, 1, 2, 3}` with edges
`0:{0,1}`, `1:{1,2}`, `2:{0,2}`, `3:{1,3}`, `4:{2,3}`. The three simple cycles are `{0, 1, 2}`,
`{1, 3, 4}`, and `{0, 2, 3, 4}`. -/
def diamondAcyclic (S : Finset (Fin 5)) : Bool :=
  !(decide ((0 : Fin 5) ∈ S) && decide ((1 : Fin 5) ∈ S) && decide ((2 : Fin 5) ∈ S)) &&
  !(decide ((1 : Fin 5) ∈ S) && decide ((3 : Fin 5) ∈ S) && decide ((4 : Fin 5) ∈ S)) &&
  !(decide ((0 : Fin 5) ∈ S) && decide ((2 : Fin 5) ∈ S) &&
    decide ((3 : Fin 5) ∈ S) && decide ((4 : Fin 5) ∈ S))

def diamondOracle : {ι : Type} → IndepQuery (Fin 5) ι → ι :=
  IndepQuery.oracleOf diamondAcyclic

private theorem diamond_empty : diamondAcyclic ∅ = true := by decide

private theorem diamond_hered :
    ∀ ⦃A B : Finset (Fin 5)⦄, diamondAcyclic B = true → A ⊆ B → diamondAcyclic A = true := by
  decide

private theorem diamond_aug :
    ∀ ⦃I J : Finset (Fin 5)⦄,
      diamondAcyclic I = true → diamondAcyclic J = true → I.card < J.card →
      ∃ e ∈ J, e ∉ I ∧ diamondAcyclic (insert e I) = true := by
  decide

noncomputable def diamondMatroid : Matroid (Fin 5) :=
  (IndepMatroid.ofFinset Set.univ (fun S => diamondAcyclic S = true)
    diamond_empty diamond_hered diamond_aug (fun _ _ => Set.subset_univ _)).matroid

theorem diamondOracle_implements :
    IndepQuery.ImplementsMatroid diamondOracle diamondMatroid := by
  intro S
  simp [diamondOracle, diamondMatroid]

def diamondWeights : Fin 5 → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 5

-- Kruskal scans edges 0(1), 1(2), rejects 2(3) as closing {0,1,2}, accepts 3(4), rejects 4(5)
-- as closing {1,3,4}, yielding minimum spanning tree {0, 1, 3} of weight 7.
theorem diamond_mst_eq :
    (matroidGreedyMinBasis diamondWeights [0, 1, 2, 3, 4]).eval diamondOracle = {0, 1, 3} := by
  rw [eval_matroidGreedyMinBasis, greedyMinBasis_eq_insertionSort]
  decide

theorem diamond_mst_weight :
    ∑ e ∈ (matroidGreedyMinBasis diamondWeights [0, 1, 2, 3, 4]).eval diamondOracle,
      diamondWeights e = 7 := by
  rw [diamond_mst_eq]
  decide

-- Formal certificate that {0, 1, 3} minimizes weight across every spanning tree of the diamond.
theorem diamond_mst_le_all_bases {T : Finset (Fin 5)}
    (hT : diamondMatroid.IsBasis' (T : Set (Fin 5)) {e | e ∈ ([0, 1, 2, 3, 4] : List (Fin 5))}) :
    7 ≤ ∑ e ∈ T, diamondWeights e := by
  have hle := eval_matroidGreedyMinBasis_le_sum diamondOracle_implements
    diamondWeights [0, 1, 2, 3, 4] hT
  have hval := diamond_mst_weight
  omega

/-! ## 3. Non-matroid matching system on $P_4$: failure of greedy and Rado–Edmonds refutation -/

/-- Matchings on the 3-edge path `0 - 1 - 2` (`Fin 3`): adjacent edges cannot both be chosen. -/
def pathMatching (S : Finset (Fin 3)) : Bool :=
  !(decide ((0 : Fin 3) ∈ S) && decide ((1 : Fin 3) ∈ S)) &&
  !(decide ((1 : Fin 3) ∈ S) && decide ((2 : Fin 3) ∈ S))

def pathWeights : Fin 3 → ℕ
  | 0 => 2
  | 1 => 3
  | 2 => 2

-- Greedy picks the heavy middle edge `{1}` (weight 3), missing the optimal matching `{0, 2}`
-- (weight 4).
theorem path_greedy_eq : greedyMaxBasis pathMatching pathWeights [0, 1, 2] = {1} := by
  rw [greedyMaxBasis_eq_insertionSort]
  decide

theorem path_greedy_weight :
    ∑ e ∈ greedyMaxBasis pathMatching pathWeights [0, 1, 2], pathWeights e = 3 := by
  rw [path_greedy_eq]
  decide

example : pathMatching {0, 2} = true ∧ ∑ e ∈ ({0, 2} : Finset (Fin 3)), pathWeights e = 4 := by
  decide

/-- By the Rado–Edmonds characterization `exists_matroid_iff_forall_sum_le_greedyMaxBasis`,
`pathMatching` is not the independence predicate of any matroid on `{0, 1, 2}`. -/
theorem pathMatching_not_matroid :
    ¬ ∃ M : Matroid (Fin 3),
      M.E = {x | x ∈ ([0, 1, 2] : List (Fin 3))} ∧
        ∀ S : Finset (Fin 3), pathMatching S = true ↔ M.Indep (S : Set (Fin 3)) := by
  rw [exists_matroid_iff_forall_sum_le_greedyMaxBasis [0, 1, 2] pathMatching
    (by decide) (by decide) (by decide)]
  intro hopt
  have hle := hopt pathWeights {0, 2} (by decide)
  have h_lhs : ∑ x ∈ ({0, 2} : Finset (Fin 3)), pathWeights x = 4 := by decide
  have h_rhs := path_greedy_weight
  omega

/-! ## 4. Non-vacuity of tight `n`-query upper and lower bounds on `ℕ` -/

theorem nat_greedySelect_tight_bounds :
    UpperBound (matroidGreedySelect (α := ℕ)) List.length id ∧
      LowerBound (matroidGreedySelect (α := ℕ)) List.length id :=
  ⟨matroidGreedySelect_upperBound, matroidGreedySelect_isMatroidBasisAlg.lowerBound_infinite⟩

theorem nat_greedyMaxIndep_unit_tight_bounds :
    UpperBound (matroidGreedyMaxIndep (α := ℕ) (fun _ => (1 : ℕ))) List.length id ∧
      LowerBound (matroidGreedyMaxIndep (α := ℕ) (fun _ => (1 : ℕ))) List.length id :=
  ⟨matroidGreedyMaxIndep_upperBound _,
    matroidGreedyMaxIndep_unit_isMaxCardIndepAlg.lowerBound_infinite⟩

-- Even on non-matroid predicates with `indep ∅ = true`, `greedyMaxBasis` returns a feasible set,
-- and `Id.run` on the monadic wrappers recovers the pure counterparts.
example : pathMatching (greedyMaxBasis pathMatching pathWeights [0, 1, 2]) = true :=
  indep_greedySelect (by decide) _

example (xs : List (Fin 4)) :
    Id.run (greedyMaxBasisM (fun S => pure (u24Indep S)) u24Weights xs) =
      greedyMaxBasis u24Indep u24Weights xs ∧
    Id.run (greedyMinBasisM (fun S => pure (u24Indep S)) u24Weights xs) =
      greedyMinBasis u24Indep u24Weights xs ∧
    Id.run (greedyMaxIndepM (fun S => pure (u24Indep S)) u24Weights xs) =
      greedyMaxIndep u24Indep u24Weights xs := by
  simp

end ComplexityTests.MatroidGreedy
