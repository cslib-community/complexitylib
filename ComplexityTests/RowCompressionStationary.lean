/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Analysis.RowCompression.Stationary
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Constructed stationary-reference examples

The first of two dyadic groups has a nonzero increment and actual nonzero compression loss.
The reference adds that loss to a different true row and retains the actual current default.
The remaining group preserves a nonzero gated output. A fourth-power ramp exhibits a strictly
positive fourth-root discrepancy and satisfies the weighted comparison theorem's scalar laws.
-/

namespace ComplexityTests.RowCompressionStationary

open Finset Cslib.RowCompression

private def initial : State (Fin 2) := { defaultValue := 0, row := ![![20, 0], ![0, 0]] }

private def truth : Fin 2 → Fin 2 → ℝ := ![![20, 0], ![2, 0]]

private noncomputable def increments (i : ℕ) : Fin 2 → Fin 2 → ℝ :=
  if i = 0 then ![![0, 0], ![1 / 2097152, 0]] else 0

private noncomputable def rawRow : Fin 2 → Fin 2 → ℝ := ![![20, 0], ![1 / 2097152, 0]]

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
      { defaultValue := 1 / 1048576, row := ![![20, 0], ![1 / 1048576, 0]] } := by
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
    { defaultValue := 1 / 1048576, row := ![![20, 0], ![2 + 1 / 2097152, 0]] } := by
  unfold reference stationaryState
  rw [actual_one, raw_one]
  congr 1
  funext y ν
  fin_cases y <;> fin_cases ν <;> norm_num [truth, rawRow]

-- The state is constructed from a nonzero increment and a strictly positive actual preloss.
example : increments 0 1 0 = 1 / 2097152 ∧
    reference.row 1 0 - truth 1 0 = 1 / 2097152 ∧
    reference.defaultValue =
      (iterate univ (fun _ => 2) (fun _ => 2) (dyadicFloor 1 2)
        increments initial 1).defaultValue := by
  rw [reference_eq, actual_one]
  norm_num [increments, truth]

private theorem reference_rank : firstRank univ 2 reference.defaultValue reference.row =
    2 + 1 / 2097152 := by
  have hle : kthLargest 2 univ (fun y => reference.row y 0) ≤ 2 + 1 / 2097152 := by
    refine not_lt.mp fun hlt => ?_
    have hc := (lt_kthLargest_iff (by norm_num)
      (by norm_num : (0 : ℝ) ≤ 2 + 1 / 2097152)).mp hlt
    have hs : ({y | (2 + 1 / 2097152 : ℝ) < reference.row y 0} : Finset (Fin 2)) = {0} := by
      ext y
      rw [reference_eq]
      fin_cases y <;> norm_num
    rw [hs] at hc
    norm_num at hc
  have hge : (2 + 1 / 2097152 : ℝ) ≤ kthLargest 2 univ (fun y => reference.row y 0) := by
    apply (le_kthLargest_iff (by norm_num) (by norm_num : (0 : ℝ) < 2 + 1 / 2097152)).mpr
    have hs : ({y | (2 + 1 / 2097152 : ℝ) ≤ reference.row y 0} : Finset (Fin 2)) = univ := by
      ext y
      rw [reference_eq]
      fin_cases y <;> norm_num
    rw [hs]
    norm_num
  exact le_antisymm (max_le (by rw [reference_eq]; norm_num) hle)
    (hge.trans kthLargest_le_firstRank)

private noncomputable def gatedOutput (x v r : ℝ) : ℝ :=
  if x ≤ 10 then 0 else if 3 ≤ r then 0 else x + v + max 1 r

private theorem gate_flat (x v q r : ℝ) (hq : q ∈ Set.Icc 0 (1 : ℝ))
    (hr : r ∈ Set.Icc 0 (1 : ℝ)) : gatedOutput x v q = gatedOutput x v r := by
  have hq' : ¬3 ≤ q := by linarith [hq.2]
  have hr' : ¬3 ≤ r := by linarith [hr.2]
  simp only [gatedOutput, hq', hr', ↓reduceIte, max_eq_left hq.2, max_eq_left hr.2]

-- The actual remaining schedule preserves a nonzero output of the constructed reference.
example :
    let c := stationaryContinuation univ (fun _ => 2) 2 (dyadicFloor 1 2)
      increments initial truth 1 1
    gatedOutput (c.row 0 0) (c.row 0 1) (firstRank univ 2 c.defaultValue c.row) =
      22 + 1 / 2097152 := by
  have h := stationaryContinuation_output_eq_dyadic (s := univ) (n := fun _ => 2) (K := 2)
    (Δ := increments) (a := initial) (truth := truth) (η := 1) (H := gatedOutput)
    (g := 3) (e := 10) (by norm_num) (by norm_num) 2 1 1 (by norm_num) no_overflow
    (fun y _ => by fin_cases y <;> norm_num [truth])
    (fun y _ => by fin_cases y <;> norm_num [truth]) (by intros; norm_num)
    (by norm_num) (by norm_num) (fun _ _ _ hx => by simp [gatedOutput, hx])
    (fun _ _ _ hr => by simp [gatedOutput, hr]) gate_flat 0 (mem_univ 0)
  refine h.trans ?_
  change gatedOutput (reference.row 0 0) (reference.row 0 1)
    (firstRank univ 2 reference.defaultValue reference.row) = _
  rw [reference_rank, reference_eq]
  norm_num [gatedOutput]

private noncomputable def fourthPowerRamp (x _v _r : ℝ) : ℝ := (max 0 (x - 1)) ^ 4

private theorem ramp_root (x v r : ℝ) :
    fourthPowerRamp x v r ^ (4⁻¹ : ℝ) = max 0 (x - 1) := by
  exact Real.pow_rpow_inv_natCast (le_max_left _ _) (by norm_num : (4 : ℕ) ≠ 0)

private theorem ramp_root_lipschitz (x v q x' v' q' : ℝ) :
    |fourthPowerRamp x v q ^ (4⁻¹ : ℝ) - fourthPowerRamp x' v' q' ^ (4⁻¹ : ℝ)| ≤
      1 * (|x - x'| + |v - v'| + |q - q'|) := by
  rw [ramp_root, ramp_root]
  have hm := abs_max_sub_max_le_max (0 : ℝ) (x - 1) 0 (x' - 1)
  have he : (x - 1) - (x' - 1) = x - x' := by ring
  simp only [sub_self, abs_zero, he, max_eq_right (abs_nonneg (x - x'))] at hm
  linarith [abs_nonneg (v - v'), abs_nonneg (q - q')]

-- The root discrepancy really is positive, rather than an equality between identical rows.
example :
    |fourthPowerRamp (reference.row 1 0) (reference.row 1 1)
        (firstRank univ 2 reference.defaultValue reference.row) ^ (4⁻¹ : ℝ) -
      fourthPowerRamp (truth 1 0) (truth 1 1) (firstRank univ 2 0 truth) ^ (4⁻¹ : ℝ)| =
        1 / 2097152 := by
  rw [ramp_root, ramp_root, reference_eq]
  norm_num [truth]

-- A constant-one raw-prefix envelope is valid, and the theorem gives a concrete finite bound.
example :
    |fourthPowerRamp (reference.row 1 0) (reference.row 1 1)
        (firstRank univ 2 reference.defaultValue reference.row) ^ (4⁻¹ : ℝ) -
      fourthPowerRamp (truth 1 0) (truth 1 1) (firstRank univ 2 0 truth) ^ (4⁻¹ : ℝ)| ≤
        27 / 262144 := by
  have h := abs_stationaryState_root_sub_le_weighted_dyadic (s := univ) (n := fun _ => 2)
    (K := 2) (Δ := increments) (a := initial) (truth := truth) (η := 1)
    (H := fourthPowerRamp) (p := (4⁻¹ : ℝ)) (C := 1) (ε := fun _ => 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [initial]) (by norm_num [initial])
    2 1 (by norm_num) no_overflow (by intros; norm_num)
    (fun _ _ _ _ _ => clippedError_le_one _ _ _)
    (fun x _ _ hx => by simp [fourthPowerRamp, max_eq_left (by linarith : x - 1 ≤ 0)])
    (by intros; rfl) (fun x v q x' v' q' _ _ _ _ => ramp_root_lipschitz x v q x' v' q')
    1 (mem_univ 1)
  norm_num [sum_range_succ, floor_zero] at h ⊢
  exact h

/-! The sensitivity clipping also handles low targets without charging their prefix errors. -/

private noncomputable def unitCutoff (x : ℝ) : ℝ := min 1 (max 0 (x - 1))

private theorem cutoff_nonneg (x : ℝ) : 0 ≤ unitCutoff x :=
  le_min zero_le_one (le_max_left _ _)

private theorem cutoff_le_one (x : ℝ) : unitCutoff x ≤ 1 := min_le_left _ _

private theorem cutoff_zero {x : ℝ} (hx : x ≤ 1) : unitCutoff x = 0 := by
  simp [unitCutoff, max_eq_left (by linarith : x - 1 ≤ 0)]

private theorem cutoff_lipschitz (x x' : ℝ) : |unitCutoff x - unitCutoff x'| ≤ |x - x'| := by
  have hmax := abs_max_sub_max_le_max (0 : ℝ) (x - 1) 0 (x' - 1)
  have he : (x - 1) - (x' - 1) = x - x' := by ring
  simp only [sub_self, abs_zero, he, max_eq_right (abs_nonneg (x - x'))] at hmax
  have hmin := abs_min_sub_min_le_max (1 : ℝ) (max 0 (x - 1)) 1 (max 0 (x' - 1))
  simp only [sub_self, abs_zero,
    max_eq_right (abs_nonneg (max 0 (x - 1) - max 0 (x' - 1)))] at hmin
  exact hmin.trans hmax

private noncomputable def rankOutput (x _v r : ℝ) : ℝ :=
  (unitCutoff x * (1 + unitCutoff r)) ^ 4

private theorem rank_output_root (x v r : ℝ) :
    rankOutput x v r ^ (4⁻¹ : ℝ) = unitCutoff x * (1 + unitCutoff r) := by
  exact Real.pow_rpow_inv_natCast
    (mul_nonneg (cutoff_nonneg x) (add_nonneg zero_le_one (cutoff_nonneg r)))
    (by norm_num : (4 : ℕ) ≠ 0)

private theorem rank_output_lipschitz (x v q x' v' q' : ℝ) :
    |rankOutput x v q ^ (4⁻¹ : ℝ) - rankOutput x' v' q' ^ (4⁻¹ : ℝ)| ≤
      2 * (|x - x'| + |v - v'| + |q - q'|) := by
  rw [rank_output_root, rank_output_root]
  have hp : 0 ≤ 1 + unitCutoff q' := add_nonneg zero_le_one (cutoff_nonneg q')
  have he : unitCutoff x * (1 + unitCutoff q) - unitCutoff x' * (1 + unitCutoff q') =
      unitCutoff x * (unitCutoff q - unitCutoff q') +
        (unitCutoff x - unitCutoff x') * (1 + unitCutoff q') := by ring
  calc
    _ ≤ |unitCutoff x * (unitCutoff q - unitCutoff q')| +
        |(unitCutoff x - unitCutoff x') * (1 + unitCutoff q')| := by
      rw [he]
      exact abs_add_le _ _
    _ = unitCutoff x * |unitCutoff q - unitCutoff q'| +
        |unitCutoff x - unitCutoff x'| * (1 + unitCutoff q') := by
      rw [abs_mul, abs_mul, abs_of_nonneg (cutoff_nonneg x), abs_of_nonneg hp]
    _ ≤ 1 * |q - q'| + |x - x'| * 2 := add_le_add
      (mul_le_mul (cutoff_le_one x) (cutoff_lipschitz q q') (abs_nonneg _) zero_le_one)
      (mul_le_mul (cutoff_lipschitz x x') (by linarith [cutoff_le_one q']) hp (abs_nonneg _))
    _ ≤ 2 * (|x - x'| + |v - v'| + |q - q'|) := by
      linarith [abs_nonneg (q - q'), abs_nonneg (v - v')]

-- This output is rank-flat on [0,1], but it really depends on ranks above that interval.
example : rankOutput 20 0 0 = 1 ∧ rankOutput 20 0 2 = 16 := by
  norm_num [rankOutput, unitCutoff]

private noncomputable def lowReference : State (Fin 2) :=
  stationaryState univ (fun _ => 2) (fun _ => 2) (dyadicFloor 1 2)
    increments initial initial.row 1

private theorem low_reference_eq : lowReference =
    { defaultValue := 1 / 1048576, row := rawRow } := by
  unfold lowReference stationaryState
  rw [actual_one, raw_one]
  congr 1
  funext y ν
  fin_cases y <;> fin_cases ν <;> norm_num [initial, rawRow]

private theorem low_reference_rank : firstRank univ 2 lowReference.defaultValue lowReference.row =
    1 / 1048576 := by
  rw [low_reference_eq]
  exact max_eq_left raw_rank_le

private theorem true_rank_zero : firstRank univ 2 0 initial.row = 0 := by
  norm_num [firstRank, kthLargest, initial, Fin.univ_succ, filter_insert, filter_singleton]

-- The low true target receives nonzero preloss and raises the padded rank within [0,eta].
example : lowReference.row 1 0 - initial.row 1 0 = 1 / 2097152 ∧
    firstRank univ 2 0 initial.row = 0 ∧
    0 < firstRank univ 2 lowReference.defaultValue lowReference.row ∧
    firstRank univ 2 lowReference.defaultValue lowReference.row ≤ 1 := by
  rw [low_reference_rank, true_rank_zero, low_reference_eq]
  norm_num [initial, rawRow]

-- Zero prefix error at every sensitive target suffices despite nonzero error at the low target.
-- The rank-dependent fourth root at the high endpoint remains exactly one.
example : rankOutput (lowReference.row 0 0) (lowReference.row 0 1)
    (firstRank univ 2 lowReference.defaultValue lowReference.row) ^ (4⁻¹ : ℝ) = 1 := by
  have herr : ∀ i < 1, ∀ y ∈ (univ : Finset (Fin 2)), (1 : ℝ) / 2 ≤ initial.row y 0 →
      clippedError (initial.row y 0) (initial.row y 1)
        (uncompressedRow increments initial.row (i + 1) y) ≤ 0 := by
    intro i hi y _ hd
    have hi0 : i = 0 := by omega
    subst i
    rw [raw_one]
    fin_cases y
    · norm_num [clippedError, initial, rawRow]
    · norm_num [initial] at hd
  have h := abs_stationaryState_root_sub_le_weighted_dyadic (s := univ) (n := fun _ => 2)
    (K := 2) (Δ := increments) (a := initial) (truth := initial.row) (η := 1)
    (H := rankOutput) (p := (4⁻¹ : ℝ)) (C := 2) (ε := fun _ => 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [initial]) (by norm_num [initial])
    2 1 (by norm_num) no_overflow (by intros; norm_num) herr
    (fun x _ _ hx => by simp [rankOutput, cutoff_zero hx])
    (fun _ _ _ _ hq hr => by simp only [rankOutput, cutoff_zero hq.2, cutoff_zero hr.2])
    (fun x v q x' v' q' _ _ _ _ => rank_output_lipschitz x v q x' v' q') 0 (mem_univ 0)
  have heq : rankOutput (lowReference.row 0 0) (lowReference.row 0 1)
      (firstRank univ 2 lowReference.defaultValue lowReference.row) ^ (4⁻¹ : ℝ) =
      rankOutput (initial.row 0 0) (initial.row 0 1)
        (firstRank univ 2 0 initial.row) ^ (4⁻¹ : ℝ) := by
    simp only [mul_zero, sum_const_zero] at h
    apply sub_eq_zero.mp
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  rw [heq, rank_output_root, true_rank_zero]
  norm_num [initial, unitCutoff]

end ComplexityTests.RowCompressionStationary
