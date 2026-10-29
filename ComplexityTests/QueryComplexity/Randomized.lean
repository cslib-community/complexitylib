/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Mathlib.Algebra.BigOperators.Fin
import Complexity.Computability.QueryComplexity.ApproximateDegree.Or
import Complexity.Computability.QueryComplexity.Randomized.Nisan
import Complexity.Computability.QueryComplexity.Yao

/-! Randomized decision trees, Nisan's bounds and Yao's minimax principle on concrete instances:
majority of three bits has bounded-error randomized complexity `1` but deterministic complexity
`3`, a hard distribution for it, the disjunction of `n` bits, and matching pennies for the minimax
theorem. Non-vacuity witnesses for the hypotheses. -/

namespace ComplexityTests.QueryComplexity.Randomized

open Cslib Cslib.BitString Cslib.QueryComplexity Convexity Finset

/-! ### Majority of three bits -/

/-- The uniform distribution on three points. -/
private noncomputable def uniformThree : StdSimplex ℝ (Fin 3) where
  weights := Finsupp.equivFunOnFinite.symm fun _ => 1 / 3
  nonneg i := by simp
  total := by
    rw [Finsupp.sum_fintype _ _ fun _ => rfl]
    simp only [Finsupp.coe_equivFunOnFinite_symm, sum_const, card_univ, Fintype.card_fin]
    norm_num

/-- Query a uniformly random bit and output it. -/
private noncomputable def randomBit : RandomizedDecisionTree (Fin 3) Bool :=
  uniformThree.map fun i => .node i (.leaf false) (.leaf true)

/-- At most one of three bits disagrees with their majority. -/
private theorem card_ne_majority_le (x : BitString 3) :
    ((if x 0 = majority 3 x then 0 else 1) + (if x 1 = majority 3 x then 0 else 1) +
      (if x 2 = majority 3 x then 0 else 1) : ℕ) ≤ 1 := by
  revert x
  decide

/-- Outputting a uniformly random bit computes the majority of three bits with error `1/3`. -/
private theorem randomBit_computes : randomBit.Computes (1 / 3) (majority 3) := by
  intro x
  rw [RandomizedDecisionTree.errorProb_eq_sum, randomBit, StdSimplex.weights_map,
    Finsupp.sum_mapDomain_index (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _, Fin.sum_univ_three]
  have h : ((if x 0 = majority 3 x then 0 else 1) + (if x 1 = majority 3 x then 0 else 1) +
      (if x 2 = majority 3 x then 0 else 1) : ℝ) ≤ 1 := by
    exact_mod_cast card_ne_majority_le x
  have hcond (b : Bool) : cond b true false = b := by cases b <;> rfl
  simp only [uniformThree, Finsupp.coe_equivFunOnFinite_symm, DecisionTree.eval_node,
    DecisionTree.eval_leaf, hcond]
  linarith

private theorem randomBit_depth : randomBit.depth ≤ 1 := by
  classical
  refine RandomizedDecisionTree.depth_le_iff.mpr fun t ht => ?_
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp
    (Finsupp.mapDomain_support (by simpa [randomBit, StdSimplex.weights_map] using ht))
  simp

/-- Read as signs, majority of three bits has Fourier coefficient `-1/2` on all three
coordinates. -/
private theorem fourierCoeff_majority_three_univ :
    fourierCoeff (fun x : BitString 3 => signVal (majority 3 x)) univ = -1 / 2 := by
  have hint : ∑ x : BitString 3, (if majority 3 x then (-1 : ℤ) else 1) * chi ℤ univ x = -4 := by
    decide
  have hreal : ∑ x : BitString 3, signVal (majority 3 x) * chi ℝ univ x = -4 := by
    rw [← show ((-4 : ℤ) : ℝ) = -4 by norm_num, ← hint]
    push_cast [signVal, chi]
    rfl
  rw [fourierCoeff_eq_sum, hreal, Fintype.card_fin]
  norm_num

/-- The uniform distribution on `000` and `111`. -/
private noncomputable def allEqual : StdSimplex ℝ (BitString 3) :=
  .duple (fun _ => false) (fun _ => true) (s := 1 / 2) (t := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)

/-- **Randomness helps** (`R_{1/3}(MAJ₃) = 1 < D(MAJ₃) = 3`), hard distribution lower bound via
Yao's principle, Nisan's general polynomial relations, `R(OR_n) ≥ n / 3` vs. `adeg(OR_n) = O(√n)`,
and matching pennies minimax. -/
example {n : ℕ} (ε : ℝ) (f : BooleanFunction n) (x : BitString n) :
    (randomizedComplexity (1 / 3) (majority 3) = 1 ∧
      DecisionTree.complexity (majority 3) = 3) ∧
    (1 ≤ distributionalComplexity (1 / 3) allEqual (majority 3) ∧
      1 ≤ randomizedComplexity (1 / 3) (majority 3)) ∧
    (blockSensitivity f ≤ 3 * randomizedComplexity (1 / 3) f ∧
      approxDegree (1 / 3) f ≤ randomizedComplexity (1 / 3) f ∧
      randomizedComplexity (1 / 3) f ≤ DecisionTree.complexity f ∧
      DecisionTree.complexity f ≤ 27 * randomizedComplexity (1 / 3) f ^ 3) ∧
    (randomizedComplexity 0 f = DecisionTree.complexity f ∧ randomizedComplexity (1 / 2) f = 0) ∧
    (n ≤ 3 * randomizedComplexity (1 / 3) (threshold n 1) ∧
      approxDegree (1 / 3) (threshold n 1) ≤ Nat.sqrt (2 * n) + 1) ∧
    distributionalComplexity 0 (StdSimplex.single x) f = 0 ∧
    (∃ ν : StdSimplex ℝ (BitString n),
      distributionalComplexity ε ν f = randomizedComplexity ε f ∧
      randomizedComplexity ε f = ⨆ ν' : StdSimplex ℝ (BitString n),
        distributionalComplexity ε ν' f) ∧
    (∃ p : StdSimplex ℝ (Fin 2), ∀ j, ∑ i, p.weights i * (if i = j then 1 else 0) ≤ 1 / 2) := by
  refine ⟨?_, ?_,
    ⟨blockSensitivity_le_three_mul_randomizedComplexity f,
      approxDegree_le_randomizedComplexity _ f,
      DecisionTree.randomizedComplexity_le_complexity (by norm_num) f,
      DecisionTree.complexity_le_mul_randomizedComplexity_pow_three f⟩,
    ⟨randomizedComplexity_zero f, randomizedComplexity_eq_zero_of_le le_rfl f⟩,
    ⟨by simpa [blockSensitivity_threshold_one_right] using
      blockSensitivity_le_three_mul_randomizedComplexity (threshold n 1),
      approxDegree_threshold_one_right_le_sqrt⟩,
    Nat.le_zero.mp (distributionalComplexity_le_depth (t := .leaf (f x))
      (by simp [DecisionTree.distributionalError_eq_sum])),
    (exists_distributionalComplexity_eq_randomizedComplexity ε f).imp fun _ h =>
      ⟨h, randomizedComplexity_eq_iSup_distributionalComplexity ε f⟩,
    StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le _ fun q => ?_⟩
  · refine ⟨le_antisymm ((randomizedComplexity_le_depth randomBit_computes).trans randomBit_depth)
      ?_, le_antisymm ((DecisionTree.complexity_le_card _).trans_eq (Fintype.card_fin 3)) ?_⟩
    · have h := blockSensitivity_le_three_mul_randomizedComplexity (majority 3)
      rw [show blockSensitivity (majority 3) = 2 by decide] at h
      omega
    · have h := card_le_degree_of_fourierCoeff_ne_zero (f := majority 3) (S := univ) (by
        rw [fourierCoeff_majority_three_univ]
        norm_num)
      rw [card_univ, Fintype.card_fin] at h
      exact h.trans (DecisionTree.degree_le_complexity _)
  · have h : 1 ≤ distributionalComplexity (1 / 3) allEqual (majority 3) := by
      obtain ⟨t, ht, hd⟩ := exists_distributionalError_le_depth_eq_distributionalComplexity
        (by norm_num : (0 : ℝ) ≤ 1 / 3) allEqual (majority 3)
      rw [← hd]
      by_contra! h0
      cases t with
      | node => simp at h0
      | leaf b =>
        rw [DecisionTree.distributionalError_eq_sum, allEqual, StdSimplex.weights_duple,
          Finsupp.sum_add_index' (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _,
          Finsupp.sum_single_index (zero_mul _), Finsupp.sum_single_index (zero_mul _)] at ht
        have h₀ : majority 3 (fun _ => false) = false := by decide
        have h₁ : majority 3 (fun _ => true) = true := by decide
        cases b <;> simp [h₀, h₁] at ht <;> norm_num at ht
    exact ⟨h, h.trans (distributionalComplexity_le_randomizedComplexity _ _ _)⟩
  · have h := q.total_fin_two
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ite_true]
    by_cases h₀ : q.weights 0 ≤ 1 / 2
    · exact ⟨0, h₀⟩
    · exact ⟨1, by linarith⟩

end ComplexityTests.QueryComplexity.Randomized
