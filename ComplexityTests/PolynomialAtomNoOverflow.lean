/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Probability.PolynomialAtomRows.NoOverflow
import Complexity.Foundations.Data.Finset.KthLargest.Truncation
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Static clipped comparison and no-overflow boundary cases

A small raw perturbation crosses the preparation support boundary. The static comparison
allows a negative common default and arbitrarily large signed second-coordinate loss. The
empty-schedule theorem retains the same strictly positive output error and has no preloss term.

A nonempty run uses size capacity one and rank two, so `K ≤ n` is false. Every raw input is
zero and the run has no overflow, yet its true preparation is one. The no-overflow comparison
applies with final envelope one, covering the range fallback and the absent capacity premise.
The separate `PolynomialAtomRows` regression exercises nonzero preloss with final raw error zero.
-/

namespace ComplexityTests.PolynomialAtomNoOverflow

open Finset Cslib Cslib.RowCompression

private noncomputable def truth : Fin 2 → Fin 2 → ℝ := ![![1 / 2, 0], ![0, 0]]

private noncomputable def raw : Fin 2 → Fin 2 → ℝ := ![![1 / 2 + 1 / 100000000, 0], ![0, 0]]

private noncomputable def signedLoss : Fin 2 → Fin 2 → ℝ := ![![0, 1000], ![0, -1000]]

private theorem second_rank_zero {v : Fin 2 → ℝ} (hv : v 1 = 0) : kthLargest 2 univ v = 0 := by
  apply le_antisymm _ kthLargest_nonneg
  refine not_lt.mp fun hlt => ?_
  have hc := (lt_kthLargest_iff (by norm_num) (le_refl (0 : ℝ))).mp hlt
  have hs : ({y | 0 < v y} : Finset (Fin 2)) ⊆ {0} := by
    intro y hy
    fin_cases y
    · simp
    · simp [hv] at hy
  have hb := hc.trans (card_le_card hs)
  norm_num at hb

private theorem boundary_error (y : Fin 2) :
    clippedError (truth y 0) (truth y 1) (raw y) ≤ 1 / 10000000 := by
  fin_cases y <;> norm_num [truth, raw, clippedError]

private theorem positive_boundary_error (z : ℝ) (hz : z ≤ 0) (loss : Fin 2 → Fin 2 → ℝ)
    (hloss : ∀ y, loss y 0 = 0) :
    0 < PolynomialAtomRow.preparation.stateRootError 1 univ 2
      ⟨z, raw + loss⟩ ⟨z, truth + loss⟩ 0 := by
  have hq : firstRank univ 2 z (raw + loss) = 0 := by
    unfold firstRank
    rw [second_rank_zero (by simp [raw, hloss])]
    exact max_eq_right hz
  have ha : PolynomialAtomRow.preparation.eval 1 ((raw + loss) 0 0)
      (firstRank univ 2 z (raw + loss)) =
      polynomialSwitch4 (1 / 2) (3 / 4) (1 / 2 + 1 / 100000000) := by
    rw [hq]
    have hv : (raw + loss) 0 0 = 1 / 2 + 1 / 100000000 := by simp [raw, hloss]
    rw [hv]
    change polynomialPrepRow4 1 (1 / 2 + 1 / 100000000) 0 = _
    rw [polynomialPrepRow4_of_rank_le (by norm_num) (by norm_num)]
    norm_num [polynomialPrepCutoff4]
  have hb : PolynomialAtomRow.preparation.eval 1 ((truth + loss) 0 0)
      (firstRank univ 2 z (truth + loss)) = 0 :=
    polynomialPrepRow4_eq_zero_of_entry_le (by norm_num) (by simp [truth, hloss])
  have hp : 0 < polynomialSwitch4 (1 / 2 : ℝ) (3 / 4) (1 / 2 + 1 / 100000000) := by
    have hn : polynomialSwitch4 (1 / 2 : ℝ) (3 / 4) (1 / 2 + 1 / 100000000) ≠ 0 := by
      rw [ne_eq, polynomialSwitch4_eq_zero_iff (by norm_num)]
      norm_num
    exact lt_of_le_of_ne (polynomialSwitch4_nonneg _ _ _) (Ne.symm hn)
  unfold PolynomialAtomRow.stateRootError
  rw [ha, hb, Real.zero_rpow (by norm_num : (4⁻¹ : ℝ) ≠ 0), sub_zero]
  exact Real.rpow_pos_of_pos hp _

-- A negative common default and large signed second-coordinate losses are admissible, while
-- the actual polynomial root error is strictly positive.
example : signedLoss 0 1 = 1000 ∧ signedLoss 1 1 = -1000 ∧
    ∃ C : ℝ, 0 ≤ C ∧
      0 < PolynomialAtomRow.preparation.stateRootError 1 univ 2
        ⟨-7, raw + signedLoss⟩ ⟨-7, truth + signedLoss⟩ 0 ∧
      |PolynomialAtomRow.preparation.stateRootError 1 univ 2
        ⟨-7, raw + signedLoss⟩ ⟨-7, truth + signedLoss⟩ 0| ≤ C / 10000000 := by
  refine ⟨by norm_num [signedLoss], by norm_num [signedLoss], ?_⟩
  obtain ⟨C, hC, hbound⟩ := PolynomialAtomRow.preparation.exists_commonLoss_root_bound
    (θ := 1) (by norm_num)
  refine ⟨C, hC, positive_boundary_error (-7) (by norm_num) signedLoss
    (fun y => by fin_cases y <;> norm_num [signedLoss]), ?_⟩
  have h := hbound univ 2 (-7) truth raw signedLoss (by norm_num)
    (fun y _ => by fin_cases y <;> norm_num [truth])
    (fun y _ => by fin_cases y <;> norm_num [signedLoss])
    (1 / 10000000) (by norm_num) (fun y _ => boundary_error y) 0 (mem_univ 0)
  simpa only [div_eq_mul_inv, one_mul] using h

-- Upper capping also preserves zero padding when the rank exceeds the retained cardinality
-- and an uncapped input is negative.
example : kthLargest 3 univ (fun y : Fin 2 => min (1 : ℝ) ((![-4, 1000] : Fin 2 → ℝ) y)) = 0 := by
  rw [kthLargest_min (by norm_num) (by norm_num)]
  norm_num [kthLargest, Fin.univ_succ, filter_insert, filter_singleton]

-- The empty schedule has a positive final-prefix output error and an exactly zero preloss sum.
example : ∃ C : ℝ, 0 ≤ C ∧
    0 < PolynomialAtomRow.preparation.stateRootError 1 univ 2 ⟨0, raw⟩ ⟨0, truth⟩ 0 ∧
    |PolynomialAtomRow.preparation.stateRootError 1 univ 2 ⟨0, raw⟩ ⟨0, truth⟩ 0| ≤
      C / 10000000 := by
  obtain ⟨Cfinal, hCfinal, hscales⟩ := PolynomialAtomRow.preparation.exists_noOverflow_root_bound
    (θ := 1) (by norm_num)
  obtain ⟨Cpre, _, hbound⟩ := hscales (1 / 20000) (by norm_num) (by norm_num)
  refine ⟨Cfinal, hCfinal, ?_, ?_⟩
  · simpa only [add_zero] using positive_boundary_error 0 (le_refl 0) 0 (by intros; rfl)
  · have h := hbound univ (fun _ => 0) (fun _ => 0) ⟨0, raw⟩ truth 2 (by norm_num) rfl 0
      (by simp) (fun y _ => by fin_cases y <;> norm_num [truth])
      (fun y _ => by fin_cases y <;> norm_num [truth]) (fun _ => 0) (by simp) (by simp)
      (1 / 10000000) (by norm_num)
      (fun y _ => by simpa only [uncompressedRow_zero] using boundary_error y) 0 (mem_univ 0)
    simpa only [iterate_zero, sum_range_zero, mul_zero, zero_add, div_eq_mul_inv, one_mul] using h

private noncomputable def smallCapacityTruth : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 0]]

private noncomputable def smallCapacityActual : State (Fin 2) :=
  iterate univ (fun _ => 1) (fun _ => 2) (dyadicFloor (1 / 20000) 1)
    (fun _ => 0) ⟨0, 0⟩ 1

private theorem smallCapacity_threshold :
    threshold (univ : Finset (Fin 2)) 1 (dyadicFloor (1 / 20000) 1 0) 0 0 = 1 / 20480000 := by
  norm_num [threshold, kthLargest, dyadicFloor, dyadicSlack, entrySize]

private theorem smallCapacity_default :
    newDefault (univ : Finset (Fin 2)) 1 2 (dyadicFloor (1 / 20000) 1 0) 0 0 =
      1 / 20480000 := by
  rw [newDefault, smallCapacity_threshold]
  norm_num [kthLargest]

private theorem smallCapacity_state : smallCapacityActual =
    ⟨1 / 20480000, fun _ => defaultEntry (1 / 20480000)⟩ := by
  change advance univ 1 2 (dyadicFloor (1 / 20000) 1 0) 0 ⟨0, 0⟩ = _
  simp only [advance, add_zero, smallCapacity_default]
  congr 1
  funext y
  rw [← smallCapacity_default]
  apply update_eq_default_of_size_le
  rw [smallCapacity_threshold]
  norm_num [entrySize]

private theorem smallCapacity_no_overflow : ∀ i < 1,
    stepThreshold (univ : Finset (Fin 2)) (fun _ => 1) (fun _ => 2) (dyadicFloor (1 / 20000) 1)
      (fun _ => 0) ⟨0, 0⟩ i ≤ dyadicFloor (1 / 20000) 1 i := by
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  simp only [stepThreshold, inputRow, iterate_zero, add_zero]
  rw [smallCapacity_threshold]
  norm_num [dyadicFloor, dyadicSlack]

private theorem smallCapacity_error :
    |PolynomialAtomRow.preparation.stateRootError 1 univ 2 smallCapacityActual
      ⟨0, smallCapacityTruth⟩ 0| = 1 := by
  have ha : PolynomialAtomRow.preparation.eval 1 (smallCapacityActual.row 0 0)
      (firstRank univ 2 smallCapacityActual.defaultValue smallCapacityActual.row) = 0 := by
    apply polynomialPrepRow4_eq_zero_of_entry_le (by norm_num)
    rw [smallCapacity_state]
    norm_num [defaultEntry]
  have hq : firstRank univ 2 0 smallCapacityTruth = 0 := by
    rw [firstRank, second_rank_zero (by norm_num [smallCapacityTruth])]
    norm_num
  have hb : PolynomialAtomRow.preparation.eval 1 (smallCapacityTruth 0 0)
      (firstRank univ 2 0 smallCapacityTruth) = 1 := by
    rw [hq]
    change polynomialPrepRow4 1 1 0 = 1
    rw [polynomialPrepRow4_of_rank_le (by norm_num) (by norm_num)]
    exact polynomialPrepCutoff4_eq_one (by norm_num) (by norm_num)
  unfold PolynomialAtomRow.stateRootError
  rw [ha, hb, Real.zero_rpow (by norm_num : (4⁻¹ : ℝ) ≠ 0), Real.one_rpow]
  norm_num

-- This positive-error, nonempty no-overflow run has n=1<K=2. A final envelope of one is
-- admitted without a smallness premise, and the theorem supplies the actual output bound.
example : (1 : ℕ) < 2 ∧
    ∃ Cfinal Cpre : ℝ, 0 ≤ Cfinal ∧ 0 ≤ Cpre ∧ 1 ≤ Cpre / 20480000 + Cfinal := by
  refine ⟨by norm_num, ?_⟩
  obtain ⟨Cfinal, hCfinal, hscales⟩ := PolynomialAtomRow.preparation.exists_noOverflow_root_bound
    (θ := 1) (by norm_num)
  obtain ⟨Cpre, hCpre, hbound⟩ := hscales (1 / 20000) (by norm_num) (by norm_num)
  refine ⟨Cfinal, Cpre, hCfinal, hCpre, ?_⟩
  have h := hbound univ (fun _ => 1) (fun _ => 0) ⟨0, 0⟩ smallCapacityTruth 2
    (by norm_num) rfl 1 smallCapacity_no_overflow
    (fun y _ => by fin_cases y <;> norm_num [smallCapacityTruth])
    (fun y _ => by fin_cases y <;> norm_num [smallCapacityTruth]) (fun _ => 1)
    (by intros; norm_num) (fun _ _ _ _ _ => clippedError_le_one _ _ _)
    1 (by norm_num) (fun _ _ => clippedError_le_one _ _ _) 0 (mem_univ 0)
  change |PolynomialAtomRow.preparation.stateRootError 1 univ 2 smallCapacityActual
    ⟨0, smallCapacityTruth⟩ 0| ≤ _ at h
  rw [smallCapacity_error] at h
  norm_num [dyadicFloor, dyadicSlack] at h
  simpa only [div_eq_mul_inv, one_mul] using h

end ComplexityTests.PolynomialAtomNoOverflow
