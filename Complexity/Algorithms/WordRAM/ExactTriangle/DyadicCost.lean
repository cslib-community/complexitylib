/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ExactTriangle.ParameterChoice.CostGeometry
public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.TimeBound
public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.TimeBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Aggregate charges at the computed dyadic parameters

These original estimates apply to the existing proved native instruction budgets. The selected
prime's false positives are bounded using the existing hashing theorem, with one global scan
reserve. They do not yet compose parameter/prime selection and callable solving into one
program, dispatch small inputs or establish the source's tuned 3SUM exponent.

## Main results

* `fixedPrime_timeBound_le`: complete selected-prime native charge at the computed geometry.
* `selection_timeBound_le`: actual enumeration and concrete counters fit the same saving.
* `components_timeBound_le`: add these budgets and the real parameter-preparation allowance.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.DyadicCost

open Cslib.Matrix
open Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open ParameterChoice

private theorem one_le_scale {n : ℕ} (hn : 0 < n) :
    (1 : ℝ) ≤ (n : ℝ) ^ 3 / groups n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hg1 : (1 : ℝ) ≤ groups n := by exact_mod_cast one_le_groups n
  exact (one_le_mul_of_one_le_of_one_le hn1 hg1).trans (group_work_le hn)

/-- All actual root, query and record bookkeeping fits one common cost scale. -/
theorem controller_le {n : ℕ} (hn : 0 < n) :
    (4 * (n : ℝ) * groups n) *
      ((5 * Nat.sqrt (window n) + 8 * queryCap n (window n) + 61 : ℕ) : ℝ) ≤
      296 * ((n : ℝ) ^ 3 / groups n) := by
  have hr := root_work_le hn
  have hq := query_work_le hn
  have hg := group_work_le hn
  push_cast
  nlinarith only [hr, hq, hg]

/-- The aggregate product term simplifies exactly at the computed balance. -/
theorem product_eq (n : ℕ) :
    138412032 * ((19 * level n + 1 : ℕ) : ℝ) * (n : ℝ) ^ 3 * groups n /
        (window n : ℝ) ^ (1 / 18 : ℝ) =
      138412032 * ((19 * level n + 1 : ℕ) : ℝ) * ((n : ℝ) ^ 3 / groups n) := by
  rw [rpow_window]
  have hg : (groups n : ℝ) ≠ 0 := by exact_mod_cast (groups_pos n).ne'
  field_simp

/-- The actual global scan charge, including its constant overhead per executed scan. -/
theorem scans_le {n p : ℕ} {κ : ℝ} (hf : 0 < blocks n) (hκ : 1 ≤ κ)
    (wAB wBC wAC : Fin n → Fin n → ℤ)
    (hv : WeightsBoundedBy wAB wBC wAC ((n : ℝ) ^ κ))
    (hp : IsSelectedPrime wAB wBC wAC (window n) p) :
    (((42 * pieceSize (window n) (groups n) + 28) *
        (falsePositiveCount wAB wBC wAC p + 1) : ℕ) : ℝ) ≤
      (140 * falsePositiveConst + 140) * κ * Real.log n * ((n : ℝ) ^ 3 / groups n) := by
  have hn := pos_of_blocks_pos hf
  have hD := window_ge_sixteen hf
  have hg1 := one_le_groups n
  have hg : (groups n : ℝ) ≤ Real.sqrt (window n) := by
    exact (le_self_pow₀ (by exact_mod_cast hg1) (by decide : 2 ≠ 0)).trans
      (groups_sq_le_sqrt n)
  have hpiece := pieceSize_pos hD hg1
  have hb := falsePositiveCount_add_one_mul_pieceSize_le wAB wBC wAC hD (window_le hn)
    hg1 hg hκ hv hp
  have hlocal : 42 * pieceSize (window n) (groups n) + 28 ≤
      70 * pieceSize (window n) (groups n) := by omega
  have hmul := Nat.mul_le_mul_right (falsePositiveCount wAB wBC wAC p + 1) hlocal
  have hcast : (((42 * pieceSize (window n) (groups n) + 28) *
        (falsePositiveCount wAB wBC wAC p + 1) : ℕ) : ℝ) ≤
      70 * (((falsePositiveCount wAB wBC wAC p : ℝ) + 1) *
        pieceSize (window n) (groups n)) := by
    have hc := (Nat.cast_le (α := ℝ)).mpr hmul
    push_cast at hc ⊢
    nlinarith only [hc]
  calc
    _ ≤ 70 * (((falsePositiveCount wAB wBC wAC p : ℝ) + 1) *
        pieceSize (window n) (groups n)) := hcast
    _ ≤ 70 * ((2 * falsePositiveConst + 2) *
        (κ * (n : ℝ) ^ 3 * Real.log n / groups n)) := by gcongr
    _ = _ := by ring

/-- The complete existing halt-inclusive fixed-prime budget at the actual dyadic parameters
and a selected prime. Original weights are bounded by n^κ; no execution/time law is assumed.
This is a cost theorem for that proved component, not yet the composed fast ET program. -/
theorem fixedPrime_timeBound_le {n p : ℕ} {κ : ℝ} (hf : 0 < blocks n) (hκ : 1 ≤ κ)
    (values : List ℤ) (mem : ℕ → ℕ)
    (hv : WeightsBoundedBy
      (fun u v : Fin n => values.getD (pairIndex (u, v)) 0)
      (fun u v => values.getD (n * n + pairIndex (u, v)) 0)
      (fun u v => values.getD (2 * (n * n) + pairIndex (u, v)) 0) ((n : ℝ) ^ κ))
    (hp : IsSelectedPrime
      (fun u v : Fin n => values.getD (pairIndex (u, v)) 0)
      (fun u v => values.getD (n * n + pairIndex (u, v)) 0)
      (fun u v => values.getD (2 * (n * n) + pairIndex (u, v)) 0) (window n) p) :
    (FixedPrime.timeBound (m := level n) (pos_of_blocks_pos hf) (groups n) p values mem : ℝ) ≤
      (993 + 138412032 * ((19 * level n + 1 : ℕ) : ℝ) +
        (140 * falsePositiveConst + 140) * κ * Real.log n) *
          ((n : ℝ) ^ 3 / groups n) := by
  have hn := pos_of_blocks_pos hf
  have h := FixedPrime.timeBound_le (m := level n) hn values mem (window_ge_sixteen hf)
    (one_le_groups n) hp.1 (geometry hn)
  have hs := scans_le hf hκ _ _ _ hv hp
  have hc := controller_le hn
  have hprep := mul_le_mul_of_nonneg_left (preparation_le hn) (by norm_num : (0 : ℝ) ≤ 690)
  have hseven := mul_le_mul_of_nonneg_left (one_le_scale hn) (by norm_num : (0 : ℝ) ≤ 7)
  dsimp only at h
  change (_ : ℝ) ≤ 690 * (n : ℝ) ^ 2 * window n * groups n +
    138412032 * ((19 * level n + 1 : ℕ) : ℝ) * (n : ℝ) ^ 3 * groups n /
      (window n : ℝ) ^ (1 / 18 : ℝ) +
    (4 * (n : ℝ) * groups n) *
      ((5 * Nat.sqrt (window n) + 8 * queryCap n (window n) + 61 : ℕ) : ℝ) +
    (((42 * pieceSize (window n) (groups n) + 28) *
      (falsePositiveCount _ _ _ p + 1) + 7 : ℕ) : ℝ) at h
  rw [product_eq] at h
  push_cast at h hs hc ⊢
  nlinarith only [h, hs, hc, hprep, hseven]

private theorem padded_dimension_le {n : ℕ} (hn : 0 < n) :
    (n + 1 : ℝ) ^ (281 / 100 : ℝ) ≤ 8 * (n : ℝ) ^ (281 / 100 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have htwo : (2 : ℝ) ^ (281 / 100 : ℝ) ≤ 8 := by
    calc
      _ ≤ (2 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 8 := by norm_num
  calc
    _ ≤ (2 * (n : ℝ)) ^ (281 / 100 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    _ = (2 : ℝ) ^ (281 / 100 : ℝ) * (n : ℝ) ^ (281 / 100 : ℝ) :=
      Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right htwo (by positivity)

private theorem selector_kernel_le {n : ℕ} (hn : 0 < n) :
    (Nat.sqrt (window n) + 1 : ℝ) ^ 3 * (n + 1 : ℝ) ^ (281 / 100 : ℝ) ≤
      64 * ((n : ℝ) ^ 3 / groups n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hg0 : (0 : ℝ) < groups n := by exact_mod_cast groups_pos n
  have hg1 : (1 : ℝ) ≤ groups n := by exact_mod_cast one_le_groups n
  have hs : (Nat.sqrt (window n) + 1 : ℝ) ≤ 2 * (groups n : ℝ) ^ 18 := by
    rw [sqrt_window, Nat.cast_pow]
    have hpow : (1 : ℝ) ≤ (groups n : ℝ) ^ 18 := one_le_pow₀ hg1
    linarith
  have hc : (Nat.sqrt (window n) + 1 : ℝ) ^ 3 ≤ 8 * (groups n : ℝ) ^ 54 := by
    calc
      _ ≤ (2 * (groups n : ℝ) ^ 18) ^ 3 := by gcongr
      _ = _ := by ring
  have hg : (groups n : ℝ) ^ 55 ≤ (n : ℝ) ^ (19 / 100 : ℝ) :=
    (groups_pow_le_rpow hn 55).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num))
  have htotal : (groups n : ℝ) ^ 55 * (n : ℝ) ^ (281 / 100 : ℝ) ≤ (n : ℝ) ^ 3 := by
    calc
      _ ≤ (n : ℝ) ^ (19 / 100 : ℝ) * (n : ℝ) ^ (281 / 100 : ℝ) := by gcongr
      _ = _ := by rw [← Real.rpow_add (by positivity)]; norm_num
  calc
    _ ≤ (8 * (groups n : ℝ) ^ 54) * (8 * (n : ℝ) ^ (281 / 100 : ℝ)) := by
      exact mul_le_mul hc (padded_dimension_le hn) (by positivity) (by positivity)
    _ ≤ 64 * ((n : ℝ) ^ 3 / groups n) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hg0).mpr
      nlinarith only [htotal]

/-- Actual prime enumeration and all its concrete counters are cheaper than the common
scale. The explicit runtime-prime dependence is absorbed using the proved size reserve. -/
theorem selection_timeBound_le {n : ℕ} (hn : 0 < n) :
    ((PrimeSelection.timeBound n (window n) + 16 : ℕ) : ℝ) ≤
      237140 * ((n : ℝ) ^ 3 / groups n) := by
  have h := PrimeSelection.timeBound_le_subcubic n (window n)
  have hk := mul_le_mul_of_nonneg_left (selector_kernel_le hn) (by norm_num : (0 : ℝ) ≤ 3704)
  have hd : (window n : ℝ) ≤ (n : ℝ) ^ 3 / groups n :=
    (show (window n : ℝ) ≤ (n : ℝ) * groups n from by
      have hn' : (window n : ℝ) ≤ n := by exact_mod_cast window_le hn
      exact hn'.trans (le_mul_of_one_le_right (Nat.cast_nonneg n)
        (by exact_mod_cast one_le_groups n))).trans (group_work_le hn)
  have hunit := one_le_scale hn
  nlinarith only [h, hk, hd, hunit]

/-- Sum of the parameter-preparation allowance, the actual selector budget and the actual
selected fixed-prime budget. This adds proved component charges; execution composition,
callable adaptation and small-regime dispatch remain separate obligations. -/
theorem components_timeBound_le {n p : ℕ} {κ : ℝ} (hf : 0 < blocks n) (hκ : 1 ≤ κ)
    (values : List ℤ) (mem : ℕ → ℕ)
    (hv : WeightsBoundedBy
      (fun u v : Fin n => values.getD (pairIndex (u, v)) 0)
      (fun u v => values.getD (n * n + pairIndex (u, v)) 0)
      (fun u v => values.getD (2 * (n * n) + pairIndex (u, v)) 0) ((n : ℝ) ^ κ))
    (hp : IsSelectedPrime
      (fun u v : Fin n => values.getD (pairIndex (u, v)) 0)
      (fun u v => values.getD (n * n + pairIndex (u, v)) 0)
      (fun u v => values.getD (2 * (n * n) + pairIndex (u, v)) 0) (window n) p) :
    ((12 * Nat.log 2 n + 36 + (PrimeSelection.timeBound n (window n) + 16) +
        FixedPrime.timeBound (m := level n) (pos_of_blocks_pos hf)
          (groups n) p values mem : ℕ) : ℝ) ≤
      (238169 + 12 * (Nat.log 2 n : ℝ) +
        138412032 * ((19 * level n + 1 : ℕ) : ℝ) +
        (140 * falsePositiveConst + 140) * κ * Real.log n) *
          ((n : ℝ) ^ 3 / groups n) := by
  have hn := pos_of_blocks_pos hf
  have hfixed := fixedPrime_timeBound_le hf hκ values mem hv hp
  have hselect := selection_timeBound_le hn
  have hparam := le_mul_of_one_le_right
    (show (0 : ℝ) ≤ (12 * Nat.log 2 n + 36 : ℕ) by positivity) (one_le_scale hn)
  push_cast at hparam hfixed hselect ⊢
  nlinarith only [hfixed, hselect, hparam]

end Cslib.Algorithms.WordRAM.ExactTriangle.DyadicCost
