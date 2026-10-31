/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Probability.PolynomialAtomRows
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Concrete polynomial stationary rows

A nonzero first increment incurs actual preloss `1/2097152`. Adding it to a true low entry
of `260` moves the witness rank strictly into its transition interval `(260,270)`. The true
high-endpoint witness is one, while the reference witness lies strictly between zero and one.
The remaining group raises the default and erases a second-coordinate value of `1/4`, yet
preserves that nonzero witness. Its fourth-root error satisfies the new weighted bound.
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

end ComplexityTests.PolynomialAtomRows
