/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.DecisionTree.Granularity
import Complexity.Computability.DecisionTree.Influence
import Complexity.Computability.DecisionTree.SpectralNorm
import Complexity.Computability.QueryComplexity.Degree
import Complexity.Computability.QueryComplexity.Monotone
import Complexity.Foundations.BooleanAnalysis.Decomposition
import Complexity.Foundations.BooleanAnalysis.Monotone
import Complexity.Foundations.BooleanAnalysis.RelevantCoordinates

/-! Clients and axiom guards for the Fourier analysis of decision trees, of low-degree Boolean
functions and of monotone Boolean functions. -/

namespace ComplexityTests.BooleanAnalysisDecisionTree

open Cslib Cslib.BitString Finset Function
open scoped BigOperators

/-- The conjunction of bits `0` and `1` of three, as a decision tree of depth two. -/
def andTree : DecisionTree (Fin 3) Bool :=
  .node 0 (.leaf false) (.node 1 (.leaf false) (.leaf true))

/-- The degree hypothesis of the low-degree results, discharged by the depth of a tree. -/
theorem andTree_mem_lowDegree :
    (fun x => signVal (andTree.eval x)) ∈ lowDegree ℝ (Fin 3) 2 :=
  DecisionTree.comp_eval_mem_lowDegree (fun b => signVal b) andTree

theorem fourierCoeff_andTree_eq_zero (S : Finset (Fin 3)) (hS : 2 < #S) :
    fourierCoeff (fun x => signVal (andTree.eval x)) S = 0 :=
  DecisionTree.fourierCoeff_eq_zero_of_depth_lt (fun b => signVal b) andTree hS

-- The Nisan–Szegedy bound, total influence, exact relevant coordinate count, irrelevant/relevant
-- coordinate influence, and granularity/spectral-norm/sparsity bounds on `andTree`.
example (S : Finset (Fin 3)) :
    andTree.depth = 2 ∧
    andTree.leafCount = 3 ∧
    #{i | ∃ x, andTree.eval (update x i !x i) ≠ andTree.eval x} ≤ 2 * 2 ^ (2 - 1) ∧
    totalInfluence (fun x => signVal (andTree.eval x)) ≤ 2 ∧
    #{i | ∃ x, andTree.eval (update x i !x i) ≠ andTree.eval x} = 2 ∧
    influence 2 (fun x => signVal (andTree.eval x)) = 0 ∧
    1 ≤ 2 ^ (2 - 1) * influence 0 (fun x => signVal (andTree.eval x)) ∧
    #{i | ∃ x, majority 3 (update x i !x i) ≠ majority 3 x} ≤
      QueryComplexity.degree (majority 3) * 2 ^ (QueryComplexity.degree (majority 3) - 1) ∧
    (∃ m : ℤ, fourierCoeff (fun x => signVal (andTree.eval x)) S = m / 2) ∧
    ∑ T, |fourierCoeff (fun x => signVal (andTree.eval x)) T| ≤ 3 ∧
    #{T | fourierCoeff (fun x => signVal (andTree.eval x)) T ≠ 0} ≤ 6 ∧
    andTree.leafCount ≤ 2 ^ andTree.depth ∧
    totalInfluence (fun x => signVal (andTree.eval x)) ≤ andTree.depth := by
  refine ⟨rfl, rfl,
    card_filter_exists_update_ne_le (fun x => andTree.eval x) andTree_mem_lowDegree,
    totalInfluence_signVal_le_of_degree (fun x => andTree.eval x) andTree_mem_lowDegree,
    by decide,
    not_not.1 ((influence_signVal_ne_zero_iff (fun x => andTree.eval x) 2).not.2 (by decide)),
    one_le_two_pow_mul_influence_of_degree (fun x => andTree.eval x) andTree_mem_lowDegree 0
      ((influence_signVal_ne_zero_iff (fun x => andTree.eval x) 0).2 ⟨fun _ => true, by decide⟩),
    card_filter_exists_update_ne_le (majority 3)
      (signVal_comp_mem_lowDegree_iff.2 (QueryComplexity.degree_le_iff_mem_lowDegree.1 le_rfl)),
    ?_,
    by exact_mod_cast DecisionTree.sum_abs_fourierCoeff_signVal_le_leafCount id andTree,
    DecisionTree.card_filter_fourierCoeff_signVal_ne_zero_le id andTree,
    DecisionTree.leafCount_le_two_pow_depth andTree,
    DecisionTree.totalInfluence_le_depth id andTree⟩
  have h :=
    DecisionTree.exists_fourierCoeff_signVal_eq_intCast_div_two_pow_depth_sub_one id andTree S
  rwa [show andTree.depth - 1 = 1 from rfl, pow_one] at h

-- Majority is monotone and its negation is antitone, so both have total influence at most `√n`;
-- plus the decomposition along a bit and symmetric-difference reindexing on `andTree`.
example (n : ℕ) (x : Fin 3 → Bool) :
    totalInfluence (fun y => signVal (majority n y)) ≤ √n ∧
    totalInfluence (fun y => signVal (!majority n y)) ≤ √n ∧
    signVal (andTree.eval x) =
      (signVal (andTree.eval (update x 0 false)) + signVal (andTree.eval (update x 0 true))) / 2 +
        chi ℝ {0} x * derivative 0 (fun y => signVal (andTree.eval y)) x ∧
    fourierCoeff (fun y => signVal (andTree.eval y)) {0} =
      𝔼 y, derivative 0 (fun z => signVal (andTree.eval z)) y ∧
    ∑ S, fourierCoeff (fun y => signVal (andTree.eval y)) (symmDiff {0} S) =
      ∑ S, fourierCoeff (fun y => signVal (andTree.eval y)) S := by
  refine ⟨?_, ?_,
    eq_add_chi_mul_derivative 0 (fun y => signVal (andTree.eval y)) x,
    fourierCoeff_singleton_eq_expect_derivative 0 (fun y => signVal (andTree.eval y)),
    Fintype.sum_symmDiff {0} (fun S => fourierCoeff (fun y => signVal (andTree.eval y)) S)⟩
  · have h := totalInfluence_le_sqrt_card_of_monotone (f := majority n) (monotone_threshold _)
    rwa [Fintype.card_fin] at h
  · have h := totalInfluence_le_sqrt_card_of_antitone (f := fun y => !majority n y)
      fun y z hyz => by
        have h := monotone_threshold (n := n) ((n + 1) / 2) hyz
        change (!threshold n ((n + 1) / 2) z) ≤ !threshold n ((n + 1) / 2) y
        revert h
        cases threshold n ((n + 1) / 2) y <;> cases threshold n ((n + 1) / 2) z <;> decide
    rwa [Fintype.card_fin] at h

/-! ### Axiom guards -/

/-- info: 'Cslib.DecisionTree.leafCount_le_two_pow_depth' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionTree.leafCount_le_two_pow_depth

end ComplexityTests.BooleanAnalysisDecisionTree
