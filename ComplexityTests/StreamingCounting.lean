/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.BooleanAnalysis.StreamingCounting
import Mathlib.Algebra.Field.ZMod
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Concrete finite-field counting: two Boolean variables, a quadratic constraint, and
nonconstant replacement rows coupling both variables. Only the all-true assignment satisfies
the constraint. The recovery uses two nonzero nodes and first-order marked supports. -/

open Finset Polynomial Cslib.BitString Cslib.AffineTaylor Cslib.ReplacementCounting
open scoped BigOperators

namespace StreamingCountingTests

private abbrev K := ZMod 7

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private noncomputable def factor (_ : Unit) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 * MvPolynomial.X 1

private noncomputable def rows (_ : Unit) (v i : Fin 2) : Polynomial K :=
  C (if i = v then 1 else 0) + X

private abbrev nodes : Fin 2 → K := ![1, 2]

private theorem factor_degree : (factor ()).totalDegree ≤ 2 := by
  simpa only [factor, MvPolynomial.totalDegree_X] using
    MvPolynomial.totalDegree_mul (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K)
      (MvPolynomial.X 1)

private theorem rows_degree (f : Unit) (v i : Fin 2) : (rows f v i).natDegree ≤ 1 := by
  rw [rows, add_comm, natDegree_add_C, natDegree_X]

private theorem nodes_distinct :
    ((univ : Finset (Fin 2)) : Set (Fin 2)).Pairwise fun i j => IsUnit (nodes i - nodes j) := by
  intro i _ j _ hij
  apply isUnit_iff_ne_zero.mpr
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

private theorem count_one : targetSum {()} (fun _ (v : Fin 2) => v) factor = (1 : K) := by
  simp only [targetSum, prod_singleton, factor, map_mul, MvPolynomial.eval_X,
    Function.comp_apply]
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp]
  norm_num [Fintype.sum_prod_type, Fintype.sum_bool, bitVal]

-- The untruncated polynomial retains the same degree bound at every node and every cutoff.
example (q : ℕ) (t : K) : (markedTaylorSum {()} factor rows q t).natDegree ≤ 2 := by
  have h := natDegree_markedTaylorSum_le {()} factor rows
    (d := 1) (fun f _ => rows_degree f) q t
  simp only [sum_singleton, mul_one] at h
  exact h.trans factor_degree

-- A complete instantiation: all row, node, field-size and interpolation hypotheses are proved.
example : (1 : K) = ∑ i : Fin 2, ∑ u : Kˣ,
    hermiteEvalKernel univ nodes (fun _ => 2) 0 i (u : K) *
      (markedTaylorSum {()} factor rows 1 (nodes i)).eval (u : K) := by
  rw [← count_one]
  apply targetSum_eq_sum_markedTaylorSum {()} (fun _ (v : Fin 2) => v) factor rows
    univ nodes 1 nodes_distinct
  · decide
  · intro f _ v i
    by_cases h : i = v <;> simp [rows, h]
  · intro f _ v i
    exact rows_degree f v i
  · simp only [sum_singleton, mul_one, card_univ, Fintype.card_fin]
    exact factor_degree.trans_lt (by decide)
  · simp only [sum_singleton, mul_one, ZMod.card]
    exact factor_degree.trans_lt (by decide)

-- Zero marked support still preserves the constant coefficient: it sums all baselines.
example : (markedTaylorSum {()} factor rows 0 (0 : K)).coeff 0 = 1 := by
  rw [coeff_markedTaylorSum _ _ _ _ (by decide : 0 ≤ 0), taylor_coeff_zero]
  rw [← targetPolynomial_eq_replacedSum]
  rw [eval_zero_targetPolynomial {()} (fun _ (v : Fin 2) => v) factor rows
    (by intro f _ v i; by_cases h : i = v <;> simp [rows, h])]
  exact count_one

-- With no factors, all four Boolean assignments still contribute, including at a nonzero node.
example : (markedTaylorSum (∅ : Finset Unit) factor rows 0 (3 : K)).coeff 0 = 4 := by
  rw [coeff_markedTaylorSum _ _ _ _ (by decide : 0 ≤ 0), replacedSum_empty]
  norm_num

end StreamingCountingTests
