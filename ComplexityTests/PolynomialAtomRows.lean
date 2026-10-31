/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Probability.PolynomialAtomRows.FirstOverflow
import Complexity.Foundations.Probability.PolynomialAtomRows.NoOverflow
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Concrete polynomial stationary rows

A nonzero first increment incurs actual preloss `1/2097152`. Adding it to a true low entry
of `260` moves the witness rank strictly into its transition interval `(260,270)`. The true
high-endpoint witness is one, while the reference witness lies strictly between zero and one.
The remaining group raises the default and erases a second-coordinate value of `1/4`, yet
preserves that nonzero witness. Its fourth-root error satisfies the weighted bound.
Completing the second actual raw input to truth then gives a real first overflow at group one,
zero tail error, and a strictly positive actual-to-truth error paid entirely by weighted preloss.
Increasing the size capacity to three gives a second completion with no overflow at all. Its
final raw error is zero and the same positive witness error is paid entirely by weighted preloss.
-/

namespace ComplexityTests.PolynomialAtomRows

open Finset Cslib Cslib.RowCompression

private def initial : State (Fin 2) := { defaultValue := 0, row := ![![900, 0], ![0, 0]] }

private noncomputable def truth : Fin 2 → Fin 2 → ℝ := ![![900, 0], ![260, 1 / 4]]

private noncomputable def increments (i : ℕ) : Fin 2 → Fin 2 → ℝ :=
  if i = 0 then ![![0, 0], ![1 / 2097152, 0]] else 0

private noncomputable def rawRow : Fin 2 → Fin 2 → ℝ := ![![900, 0], ![1 / 2097152, 0]]

private theorem floor_zero : dyadicFloor 1 2 0 = 1 / 1048576 := by
  norm_num [dyadicFloor, dyadicSlack]

private theorem raw_rank_le : kthLargest 2 univ (fun y => rawRow y 0) ≤ 1 / 1048576 := by
  refine not_lt.mp fun hlt => ?_
  have hcard := (lt_kthLargest_iff (by norm_num)
    (by norm_num : (0 : ℝ) ≤ 1 / 1048576)).mp hlt
  have hsupport : ({y | (1 / 1048576 : ℝ) < rawRow y 0} : Finset (Fin 2)) = {0} := by
    ext y
    fin_cases y <;> norm_num [rawRow]
  rw [hsupport] at hcard
  norm_num at hcard

private theorem raw_threshold : threshold univ 2 (1 / 1048576) 0 rawRow = 1 / 1048576 := by
  have hs : (fun y => entrySize (rawRow y)) = fun y => rawRow y 0 := by
    funext y
    fin_cases y <;> norm_num [entrySize, rawRow]
  refine le_antisymm ?_ floor_le_threshold
  unfold threshold
  rw [hs]
  exact max_le (by norm_num) (max_le le_rfl raw_rank_le)

private theorem raw_default : newDefault univ 2 2 (1 / 1048576) 0 rawRow = 1 / 1048576 := by
  unfold newDefault
  rw [raw_threshold]
  exact max_eq_left ((min_le_left _ _).trans (max_le (by norm_num) raw_rank_le))

private theorem raw_one : uncompressedRow increments initial.row 1 = rawRow := by
  funext y ν
  fin_cases y <;> fin_cases ν <;> norm_num [uncompressedRow, initial, increments, rawRow]

private theorem actual_one :
    iterate univ (fun _ => 2) (fun _ => 2) (dyadicFloor 1 2) increments initial 1 =
      { defaultValue := 1 / 1048576, row := ![![900, 0], ![1 / 1048576, 0]] } := by
  have hin : initial.row + increments 0 = rawRow := by
    funext y ν
    fin_cases y <;> fin_cases ν <;> norm_num [initial, increments, rawRow]
  change advance univ 2 2 (dyadicFloor 1 2 0) (increments 0) initial = _
  unfold advance
  rw [hin, floor_zero]
  change State.mk (newDefault univ 2 2 (1 / 1048576) 0 rawRow)
    (update univ 2 2 (1 / 1048576) 0 rawRow) = _
  rw [raw_default]
  congr 1
  unfold update
  rw [raw_threshold, raw_default]
  funext y ν
  fin_cases y <;> fin_cases ν <;>
    norm_num [updateEntry, radius, entrySize, defaultEntry, rawRow]

private theorem no_overflow : ∀ i < 1,
    stepThreshold univ (fun _ => 2) (fun _ => 2) (dyadicFloor 1 2) increments initial i ≤
      dyadicFloor 1 2 i := by
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  have hin : inputRow univ (fun _ => 2) (fun _ => 2) (dyadicFloor 1 2) increments initial 0 =
      rawRow := by
    funext y ν
    fin_cases y <;> fin_cases ν <;> norm_num [inputRow, initial, increments, rawRow]
  unfold stepThreshold
  rw [hin, iterate_zero, floor_zero]
  exact raw_threshold.le

private noncomputable def reference : State (Fin 2) :=
  stationaryState univ (fun _ => 2) (fun _ => 2) (dyadicFloor 1 2) increments initial truth 1

private theorem reference_eq : reference =
    { defaultValue := 1 / 1048576, row := ![![900, 0], ![260 + 1 / 2097152, 1 / 4]] } := by
  unfold reference stationaryState
  rw [actual_one, raw_one]
  congr 1
  funext y ν
  fin_cases y <;> fin_cases ν <;> norm_num [truth, rawRow]

example : increments 0 1 0 = 1 / 2097152 ∧
    reference.row 1 0 - truth 1 0 = 1 / 2097152 := by
  rw [reference_eq]
  norm_num [increments, truth]

private theorem reference_rank : firstRank univ 2 reference.defaultValue reference.row =
    260 + 1 / 2097152 := by
  have hle : kthLargest 2 univ (fun y => reference.row y 0) ≤ 260 + 1 / 2097152 := by
    refine not_lt.mp fun hlt => ?_
    have hc := (lt_kthLargest_iff (by norm_num)
      (by norm_num : (0 : ℝ) ≤ 260 + 1 / 2097152)).mp hlt
    have hs : ({y | (260 + 1 / 2097152 : ℝ) < reference.row y 0} : Finset (Fin 2)) = {0} := by
      ext y
      rw [reference_eq]
      fin_cases y <;> norm_num
    rw [hs] at hc
    norm_num at hc
  have hge : (260 + 1 / 2097152 : ℝ) ≤ kthLargest 2 univ (fun y => reference.row y 0) := by
    apply (le_kthLargest_iff (by norm_num) (by norm_num : (0 : ℝ) < 260 + 1 / 2097152)).mpr
    have hs : ({y | (260 + 1 / 2097152 : ℝ) ≤ reference.row y 0} : Finset (Fin 2)) = univ := by
      ext y
      rw [reference_eq]
      fin_cases y <;> norm_num
    rw [hs]
    norm_num
  exact le_antisymm (max_le (by rw [reference_eq]; norm_num) hle)
    (hge.trans kthLargest_le_firstRank)

private theorem true_rank : firstRank univ 2 0 truth = 260 := by
  norm_num [firstRank, kthLargest, truth, Fin.univ_succ, filter_insert, filter_singleton]

private noncomputable def output (a : State (Fin 2)) : ℝ :=
  PolynomialAtomRow.witness.eval 10000 (a.row 0 0) (firstRank univ 2 a.defaultValue a.row)

private theorem reference_output : output reference =
    1 - polynomialSwitch4 260 270 (260 + 1 / 2097152) := by
  unfold output
  rw [reference_rank, reference_eq]
  change polynomialWitnessCutoff4 10000 900 (260 + 1 / 2097152) = _
  norm_num only [polynomialWitnessCutoff4]
  rw [polynomialSwitch4_of_ge (by norm_num) le_rfl, one_mul]

private theorem output_between : 0 < output reference ∧ output reference < 1 := by
  rw [reference_output]
  have h0 := polynomialSwitch4_nonneg 260 270 (260 + 1 / 2097152)
  have h1 := polynomialSwitch4_le_one 260 270 (260 + 1 / 2097152)
  have hn0 : polynomialSwitch4 (260 : ℝ) 270 (260 + 1 / 2097152) ≠ 0 := by
    rw [ne_eq, polynomialSwitch4_eq_zero_iff (by norm_num)]
    norm_num
  have hn1 : polynomialSwitch4 (260 : ℝ) 270 (260 + 1 / 2097152) ≠ 1 := by
    rw [ne_eq, polynomialSwitch4_eq_one_iff (by norm_num)]
    norm_num
  constructor
  · by_contra hn
    exact hn1 (by linarith)
  · by_contra hn
    exact hn0 (by linarith)

private theorem true_output : PolynomialAtomRow.witness.eval 10000 (truth 0 0)
    (firstRank univ 2 0 truth) = 1 := by
  rw [true_rank]
  exact polynomialWitnessCutoff4_eq_one (by norm_num) (by norm_num [truth]) (by norm_num)

private noncomputable def continued : State (Fin 2) :=
  stationaryContinuation univ (fun _ => 2) 2 (dyadicFloor 1 2) increments initial truth 1 1

private theorem preserved : output continued = output reference := by
  exact PolynomialAtomRow.witness.stationaryContinuation_eval_eq
    (s := univ) (n := fun _ => 2) (Δ := increments) (a := initial) (truth := truth)
    (θ := 10000) (η := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    2 1 1 (by norm_num) no_overflow
    (fun y _ => by fin_cases y <;> norm_num [truth])
    (fun y _ => by fin_cases y <;> norm_num [truth]) (by intros; norm_num) 0 (mem_univ 0)

-- The remaining group changes both the actual default and a row coordinate.
example : reference.defaultValue < continued.defaultValue ∧
    reference.row 1 1 = 1 / 4 ∧ continued.row 1 1 = 0 := by
  have hc : continued = advance univ 2 2 (dyadicFloor 1 2 1) 0 reference := rfl
  rw [hc, reference_eq]
  norm_num [advance, update, newDefault, threshold, firstRank, kthLargest, entrySize,
    dyadicFloor, dyadicSlack, Fin.univ_succ, filter_insert, filter_singleton,
    updateEntry, radius, defaultEntry]

-- The preserved output and its root discrepancy are both nonzero.
example : 0 < output continued ∧
    0 < |output continued ^ (4⁻¹ : ℝ) -
      PolynomialAtomRow.witness.eval 10000 (truth 0 0) (firstRank univ 2 0 truth) ^ (4⁻¹ : ℝ)| := by
  rw [preserved, true_output, Real.one_rpow]
  refine ⟨output_between.1, abs_pos.mpr ?_⟩
  exact sub_ne_zero.mpr (ne_of_lt (Real.rpow_lt_one output_between.1.le output_between.2
    (by norm_num)))

-- Apply the theorem to a valid raw-prefix error envelope, with no scalar-law premises.
example : ∃ C : ℝ, 0 ≤ C ∧
    |output continued ^ (4⁻¹ : ℝ) - 1| ≤ C / 1048576 := by
  obtain ⟨C, hC, hbound⟩ := PolynomialAtomRow.witness.exists_stationaryContinuation_root_bound
    (θ := 10000) (η := 1) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  have h := hbound univ (fun _ => 2) increments initial truth 2 (by norm_num)
    (by norm_num [initial]) (by norm_num [initial]) 2 1 1 (by norm_num) no_overflow
    (fun y _ => by fin_cases y <;> norm_num [truth])
    (fun y _ => by fin_cases y <;> norm_num [truth]) (by intros; norm_num)
    (fun _ => 1) (by intros; norm_num) (fun _ _ _ _ _ => clippedError_le_one _ _ _)
    0 (mem_univ 0)
  change |output continued ^ (4⁻¹ : ℝ) -
    PolynomialAtomRow.witness.eval 10000 (truth 0 0)
      (firstRank univ 2 0 truth) ^ (4⁻¹ : ℝ)| ≤ _ at h
  simpa only [true_output, Real.one_rpow, sum_range_succ, sum_range_zero, zero_add, mul_one,
    floor_zero, div_eq_mul_inv, one_mul] using h

-- The actual retained output has strict capacity, and a positive default still emits zero.
example : #{y ∈ (univ : Finset (Fin 2)) | PolynomialAtomRow.witness.eval 10000
    (reference.row y 0) (firstRank univ 2 reference.defaultValue reference.row) ≠ 0} < 2 :=
  PolynomialAtomRow.witness.card_filter_eval_ne_zero_lt (by norm_num) (by norm_num)

example : PolynomialAtomRow.witness.eval 10000 reference.defaultValue
    (firstRank univ 2 reference.defaultValue reference.row) = 0 :=
  PolynomialAtomRow.witness.eval_default_eq_zero (by norm_num)

-- When K exceeds the retained cardinality, positive dummy padding still affects the output.
-- The second raw coordinate is negative; it is not an input to this pre-incoming function.
example :
    let w : Unit → Fin 2 → ℝ := fun _ => ![900, -7]
    PolynomialAtomRow.witness.eval 10000 900 (firstRank univ 2 265 w) = 1 / 2 ∧
      PolynomialAtomRow.witness.eval 10000 900 (firstRank univ 2 0 w) = 1 := by
  norm_num [PolynomialAtomRow.eval, firstRank, kthLargest, polynomialWitnessCutoff4,
    polynomialSwitch4, polynomialTransition4, transitionPolynomial4]

-- Both bridges expose the polynomial row functions in the existing atom API.
example (G : Matrix (Fin 2) (Fin 2) ℝ) (x y : Fin 2) :
    Matrix.atomPrep (polynomialPrepCutoff4 10000) (polynomialRowCutoff4 10000) 2 1 G univ x y =
      PolynomialAtomRow.preparation.eval 10000 (G x y)
        (firstRank univ 2 0 fun z _ => G x z) := by
  rw [Matrix.atomPrep_polynomial_eq, PolynomialAtomRow.eval_firstRank_zero]
  simp only [div_one]

example (G : Matrix (Fin 2) (Fin 2) ℝ) (x y : Fin 2) :
    Matrix.auxScore (polynomialAuxCutoff4 10000) 2 1 G univ x y =
      PolynomialAtomRow.auxiliary.eval 10000 (G x y)
        (firstRank univ 2 0 fun z _ => G x z) := by
  rw [Matrix.auxScore_polynomial_eq, PolynomialAtomRow.eval_firstRank_zero]
  simp only [div_one]

private noncomputable def completingIncrements (i : ℕ) : Fin 2 → Fin 2 → ℝ :=
  if i = 0 then increments 0 else if i = 1 then truth - rawRow else 0

private noncomputable def completedRun : ℕ → State (Fin 2) :=
  iterate univ (fun _ => 2) (fun _ => 2) (dyadicFloor 1 2) completingIncrements initial

private theorem completing_zero : completingIncrements 0 = increments 0 := by
  simp [completingIncrements]

private theorem completed_one : completedRun 1 =
    iterate univ (fun _ => 2) (fun _ => 2) (dyadicFloor 1 2) increments initial 1 := by
  change advance univ 2 2 (dyadicFloor 1 2 0) (completingIncrements 0) initial = _
  rw [completing_zero]
  rfl

private theorem completing_raw_two :
    uncompressedRow completingIncrements initial.row 2 = truth := by
  funext y ν
  fin_cases y <;> fin_cases ν <;>
    norm_num [uncompressedRow, completingIncrements, increments, initial, truth, rawRow,
      sum_range_succ]

private theorem completing_input_one :
    inputRow univ (fun _ => 2) (fun _ => 2) (dyadicFloor 1 2)
      completingIncrements initial 1 = reference.row := by
  change (completedRun 1).row + completingIncrements 1 = reference.row
  rw [completed_one, actual_one, reference_eq]
  funext y ν
  fin_cases y <;> fin_cases ν <;> norm_num [completingIncrements, truth, rawRow]

private theorem completed_two : completedRun 2 = continued := by
  have hrow : (completedRun 1).row + completingIncrements 1 = reference.row := completing_input_one
  have hdefault : (completedRun 1).defaultValue = reference.defaultValue := by
    rw [completed_one, actual_one, reference_eq]
  change advance univ 2 2 (dyadicFloor 1 2 1) (completingIncrements 1) (completedRun 1) =
    advance univ 2 2 (dyadicFloor 1 2 1) 0 reference
  unfold advance
  rw [hrow, hdefault, add_zero]

private theorem completing_first_overflow : IsFirstOverflow univ (fun _ => 2) (fun _ => 2)
    (dyadicFloor 1 2) completingIncrements initial 1 := by
  constructor
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa only [stepThreshold, inputRow, iterate_zero, completing_zero] using
      no_overflow 0 (by norm_num)
  · change dyadicFloor 1 2 1 < threshold univ 2 (dyadicFloor 1 2 1)
      (completedRun 1).defaultValue
      (inputRow univ (fun _ => 2) (fun _ => 2) (dyadicFloor 1 2) completingIncrements initial 1)
    rw [completing_input_one]
    have hr : dyadicFloor 1 2 1 < kthLargest 2 univ (fun y => entrySize (reference.row y)) := by
      apply (lt_kthLargest_iff (by norm_num) (dyadicFloor_nonneg (by norm_num) 2 1)).mpr
      have hs : ({y | dyadicFloor 1 2 1 < entrySize (reference.row y)} :
          Finset (Fin 2)) = univ := by
        ext y
        rw [reference_eq]
        fin_cases y <;> norm_num [dyadicFloor, dyadicSlack, entrySize]
      rw [hs]
      norm_num
    exact hr.trans_le ((le_max_right _ _).trans (le_max_right _ _))

-- An actual first overflow with zero tail error still has a positive output error: the
-- preceding nonzero compression loss moved the witness rank into its transition interval.
example : IsFirstOverflow univ (fun _ => 2) (fun _ => 2) (dyadicFloor 1 2)
      completingIncrements initial 1 ∧
    clippedError (truth 1 0) (truth 1 1)
      (uncompressedRow completingIncrements initial.row 2 1) = 0 := by
  rw [completing_raw_two]
  exact ⟨completing_first_overflow, clippedError_self _ _ _ rfl rfl⟩

example : ∃ C : ℝ, 0 ≤ C ∧
    0 < |PolynomialAtomRow.witness.stateRootError 10000 univ 2 (completedRun 2) ⟨0, truth⟩ 0| ∧
    |PolynomialAtomRow.witness.stateRootError 10000 univ 2 (completedRun 2) ⟨0, truth⟩ 0| ≤
      C / 1048576 := by
  obtain ⟨Ctail, _, hscales⟩ := PolynomialAtomRow.witness.exists_firstOverflow_truth_root_bound
    (θ := 10000) (by norm_num)
  obtain ⟨Cpre, hCpre, hbound⟩ := hscales 1 (by norm_num) (by norm_num)
  refine ⟨Cpre, hCpre, ?_, ?_⟩
  · rw [completed_two]
    change 0 < |output continued ^ (4⁻¹ : ℝ) -
      PolynomialAtomRow.witness.eval 10000 (truth 0 0) (firstRank univ 2 0 truth) ^ (4⁻¹ : ℝ)|
    rw [preserved, true_output, Real.one_rpow]
    exact abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt (Real.rpow_lt_one
      output_between.1.le output_between.2 (by norm_num))))
  · have h := hbound univ (fun _ => 2) completingIncrements initial truth 2 (by norm_num) rfl
      2 1 (by norm_num) completing_first_overflow
      (fun y _ => by fin_cases y <;> norm_num [truth])
      (fun y _ => by fin_cases y <;> norm_num [truth]) (by intros; norm_num)
      (fun i => if i = 0 then 1 else 0) (by intro i _; split_ifs <;> norm_num)
      (by
        intro i hi y _ _
        have hi0 : i = 0 := by omega
        subst i
        simpa only [↓reduceIte] using clippedError_le_one (truth y 0) (truth y 1)
          (uncompressedRow completingIncrements initial.row 1 y))
      (by
        intro i hi hi' y _
        have hi1 : i = 1 := by omega
        subst i
        change clippedError (truth y 0) (truth y 1)
          (uncompressedRow completingIncrements initial.row 2 y) ≤ 0
        rw [completing_raw_two, clippedError_self _ _ _ rfl rfl]) 0 (mem_univ 0)
    norm_num [sum_range_succ, sum_Ico_eq_sum_range, floor_zero] at h
    simpa only [div_eq_mul_inv, one_mul, completedRun] using h

private theorem third_rank_zero (v : Fin 2 → ℝ) : kthLargest 3 univ v = 0 := by
  apply le_antisymm _ kthLargest_nonneg
  refine not_lt.mp fun hlt => ?_
  have hc := (lt_kthLargest_iff (by norm_num) (le_refl (0 : ℝ))).mp hlt
  have hb := card_filter_le (s := (univ : Finset (Fin 2))) (p := fun y => 0 < v y)
  norm_num at hb
  omega

private noncomputable def spaciousRun : ℕ → State (Fin 2) :=
  iterate univ (fun _ => 3) (fun _ => 2) (dyadicFloor 1 2) completingIncrements initial

private theorem spacious_one : spaciousRun 1 =
    ⟨1 / 1048576, ![![900, 0], ![1 / 1048576, 0]]⟩ := by
  have ht : threshold univ 3 (1 / 1048576) 0 rawRow = 1 / 1048576 := by
    rw [threshold, third_rank_zero]
    norm_num
  have hd : newDefault univ 3 2 (1 / 1048576) 0 rawRow = 1 / 1048576 := by
    unfold newDefault
    rw [ht]
    exact max_eq_left ((min_le_left _ _).trans (max_le (by norm_num) raw_rank_le))
  have hin : initial.row + completingIncrements 0 = rawRow := by
    funext y ν
    fin_cases y <;> fin_cases ν <;> norm_num [initial, completingIncrements, increments, rawRow]
  change advance univ 3 2 (dyadicFloor 1 2 0) (completingIncrements 0) initial = _
  unfold advance
  rw [hin, floor_zero]
  change State.mk (newDefault univ 3 2 (1 / 1048576) 0 rawRow)
    (update univ 3 2 (1 / 1048576) 0 rawRow) = _
  rw [hd]
  congr 1
  unfold update
  rw [ht, hd]
  funext y ν
  fin_cases y <;> fin_cases ν <;> norm_num [rawRow, updateEntry, radius, entrySize, defaultEntry]

private theorem spacious_input_one :
    inputRow univ (fun _ => 3) (fun _ => 2) (dyadicFloor 1 2)
      completingIncrements initial 1 = reference.row := by
  change (spaciousRun 1).row + completingIncrements 1 = reference.row
  rw [spacious_one, reference_eq]
  funext y ν
  fin_cases y <;> fin_cases ν <;> norm_num [completingIncrements, truth, rawRow]

private theorem spacious_no_overflow : ∀ i < 2,
    stepThreshold univ (fun _ => 3) (fun _ => 2) (dyadicFloor 1 2)
      completingIncrements initial i ≤ dyadicFloor 1 2 i := by
  intro i hi
  interval_cases i
  · simp only [stepThreshold, iterate_zero, initial, threshold, third_rank_zero]
    norm_num [dyadicFloor, dyadicSlack]
  · unfold stepThreshold
    rw [spacious_input_one]
    change threshold univ 3 (dyadicFloor 1 2 1) (spaciousRun 1).defaultValue reference.row ≤ _
    rw [spacious_one]
    simp only [threshold, third_rank_zero]
    norm_num [dyadicFloor, dyadicSlack]

private theorem reference_kth : kthLargest 2 univ (fun y => reference.row y 0) =
    260 + 1 / 2097152 := by
  have hz : reference.defaultValue < 260 + 1 / 2097152 := by rw [reference_eq]; norm_num
  have hle : 260 + 1 / 2097152 ≤
      max reference.defaultValue (kthLargest 2 univ fun y => reference.row y 0) := reference_rank.ge
  exact le_antisymm (kthLargest_le_firstRank.trans reference_rank.le)
    ((le_max_iff.mp hle).resolve_left (not_le.mpr hz))

private theorem spacious_two : spaciousRun 2 = ⟨3 / 1024, reference.row⟩ := by
  have ht : threshold univ 3 (1 / 1024) (1 / 1048576) reference.row = 1 / 1024 := by
    rw [threshold, third_rank_zero]
    norm_num
  have hd : newDefault univ 3 2 (1 / 1024) (1 / 1048576) reference.row = 3 / 1024 := by
    unfold newDefault
    rw [ht, reference_kth]
    norm_num
  change advance univ 3 2 (dyadicFloor 1 2 1) (completingIncrements 1) (spaciousRun 1) = _
  have hrow : (spaciousRun 1).row + completingIncrements 1 = reference.row := spacious_input_one
  unfold advance
  rw [hrow, spacious_one, show dyadicFloor (1 : ℝ) 2 1 = 1 / 1024 by
    norm_num [dyadicFloor, dyadicSlack], hd]
  congr 1
  unfold update
  rw [ht, hd, reference_eq]
  funext y ν
  fin_cases y <;> fin_cases ν <;> norm_num [updateEntry, radius, entrySize, defaultEntry]

private theorem spacious_output : PolynomialAtomRow.witness.eval 10000
    ((spaciousRun 2).row 0 0) (firstRank univ 2 (spaciousRun 2).defaultValue (spaciousRun 2).row) =
      output reference := by
  have hq : firstRank univ 2 (3 / 1024) reference.row = 260 + 1 / 2097152 := by
    unfold firstRank
    rw [reference_kth]
    norm_num
  rw [spacious_two]
  change PolynomialAtomRow.witness.eval 10000 (reference.row 0 0)
    (firstRank univ 2 (3 / 1024) reference.row) = output reference
  rw [hq]
  unfold output
  rw [reference_rank]

-- Two actual compression groups avoid overflow, but the first group's nonzero preloss shifts
-- the final witness rank. The final raw prefix is exactly truth, so the final-error term is zero.
example : (∀ i < 2, stepThreshold univ (fun _ => 3) (fun _ => 2) (dyadicFloor 1 2)
      completingIncrements initial i ≤ dyadicFloor 1 2 i) ∧
    uncompressedRow completingIncrements initial.row 2 = truth ∧
    (spaciousRun 1).row 1 0 - rawRow 1 0 = 1 / 2097152 ∧
    0 < |PolynomialAtomRow.witness.stateRootError 10000 univ 2 (spaciousRun 2) ⟨0, truth⟩ 0| := by
  refine ⟨spacious_no_overflow, completing_raw_two, ?_, ?_⟩
  · rw [spacious_one]
    norm_num [rawRow]
  · unfold PolynomialAtomRow.stateRootError
    rw [spacious_output, true_output, Real.one_rpow]
    exact abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt (Real.rpow_lt_one
      output_between.1.le output_between.2 (by norm_num))))

example : ∃ C : ℝ, 0 ≤ C ∧
    |PolynomialAtomRow.witness.stateRootError 10000 univ 2 (spaciousRun 2) ⟨0, truth⟩ 0| ≤
      C / 1048576 := by
  obtain ⟨Cfinal, _, hscales⟩ := PolynomialAtomRow.witness.exists_noOverflow_root_bound
    (θ := 10000) (by norm_num)
  obtain ⟨Cpre, hCpre, hbound⟩ := hscales 1 (by norm_num) (by norm_num)
  refine ⟨Cpre, hCpre, ?_⟩
  have h := hbound univ (fun _ => 3) completingIncrements initial truth 2 (by norm_num) rfl
    2 spacious_no_overflow
    (fun y _ => by fin_cases y <;> norm_num [truth])
    (fun y _ => by fin_cases y <;> norm_num [truth])
    (fun i => if i = 0 then 1 else 0) (by intro i _; split_ifs <;> norm_num)
    (by
      intro i hi y _ _
      interval_cases i
      · simpa only [↓reduceIte] using clippedError_le_one (truth y 0) (truth y 1)
          (uncompressedRow completingIncrements initial.row 1 y)
      · change clippedError (truth y 0) (truth y 1)
          (uncompressedRow completingIncrements initial.row 2 y) ≤ 0
        rw [completing_raw_two, clippedError_self _ _ _ rfl rfl])
    0 (le_refl 0) (by
      intro y _
      rw [completing_raw_two, clippedError_self _ _ _ rfl rfl]) 0 (mem_univ 0)
  norm_num [sum_range_succ, floor_zero] at h
  simpa only [div_eq_mul_inv, one_mul, spaciousRun] using h

end ComplexityTests.PolynomialAtomRows
