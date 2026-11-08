/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import CslibFrontier.Algorithms.WordRAM.ExactTriangle.DyadicCost.Asymptotics
import Mathlib.Data.List.GetD

/-!
# Closed uniform subcubic component-budget clients

For original constant-weight matrices, the clients discharge every weight, geometry and
selected-prime premise beyond a genuine threshold. Both zero and nonzero signed input words
are covered. These are budget clients, not executions of an assembled solver.
-/

namespace ComplexityTests.WordRAMExactTriangleSubcubicBudget

open Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.WordRAM.ExactTriangle
open ParameterChoice Filter

private def data (n : ℕ) (z : ℤ) : List ℤ := List.replicate (3 * (n * n)) z

private theorem pair_bound {n : ℕ} (a b : Fin n) : pairIndex (a, b) < n * n := by
  have h := Nat.mul_le_mul_right n (Nat.succ_le_of_lt a.isLt)
  dsimp only [pairIndex]
  nlinarith only [h, b.isLt]

private def ConstantBudget (z : ℤ) : Prop :=
  ∃ N : ℕ, 2 ^ 2394 ≤ N ∧ ∀ n ≥ N, ∃ hn : 0 < n, ∃ p,
    IsSelectedPrime (fun _ _ : Fin n => z) (fun _ _ => z) (fun _ _ => z) (window n) p ∧
      ∀ mem : ℕ → ℕ,
        ((16 * Nat.log 2 n + 36 + (PrimeSelection.timeBound n (window n) + 16) +
            FixedPrime.timeBound (m := level n) hn (groups n) p (data n z) mem : ℕ) : ℝ) ≤
          16 * (n : ℝ) ^ (3 - 33 / 20000 : ℝ)

-- Permit normalization of the existing concrete fast-threshold numeral in this client.
set_option exponentiation.threshold 2394 in
private theorem constant_budget (z : ℤ) (hz : |z| ≤ 1) : ConstantBudget z := by
  have hevent := DyadicCost.costCoefficient_eventually_le_rpow
    (by norm_num : (1 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) < 2 / 1197 - 33 / 20000)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨max N (2 ^ 2394), le_max_right _ _, ?_⟩
  intro n hnN
  have hthreshold : 2 ^ 2394 ≤ n := (le_max_right _ _).trans hnN
  have hn : 0 < n := (Nat.two_pow_pos 2394).trans_le hthreshold
  have hf : 0 < blocks n := (blocks_pos_iff n).mpr hthreshold
  obtain ⟨p, hp⟩ := exists_isSelectedPrime (fun _ _ : Fin n => z)
    (fun _ _ => z) (fun _ _ => z) (window n) (window_ge_sixteen hf)
  have hab (a b : Fin n) : (data n z).getD (pairIndex (a, b)) 0 = z :=
    List.getD_replicate z (by have h := pair_bound a b; omega)
  have hbc (a b : Fin n) : (data n z).getD (n * n + pairIndex (a, b)) 0 = z :=
    List.getD_replicate z (by have h := pair_bound a b; omega)
  have hac (a b : Fin n) : (data n z).getD (2 * (n * n) + pairIndex (a, b)) 0 = z :=
    List.getD_replicate z (by have h := pair_bound a b; omega)
  have hzR : ((|z| : ℤ) : ℝ) ≤ 1 := by exact_mod_cast hz
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hv : WeightsBoundedBy (fun _ _ : Fin n => z) (fun _ _ => z) (fun _ _ => z)
      ((n : ℝ) ^ (1 : ℝ)) := by
    rw [Real.rpow_one]
    exact ⟨fun _ _ => hzR.trans hnR, fun _ _ => hzR.trans hnR, fun _ _ => hzR.trans hnR⟩
  refine ⟨hn, p, hp, ?_⟩
  intro mem
  have hv' : WeightsBoundedBy
      (fun u v : Fin n => (data n z).getD (pairIndex (u, v)) 0)
      (fun u v => (data n z).getD (n * n + pairIndex (u, v)) 0)
      (fun u v => (data n z).getD (2 * (n * n) + pairIndex (u, v)) 0)
      ((n : ℝ) ^ (1 : ℝ)) := by simpa only [hab, hbc, hac] using hv
  have hp' : IsSelectedPrime
      (fun u v : Fin n => (data n z).getD (pairIndex (u, v)) 0)
      (fun u v => (data n z).getD (n * n + pairIndex (u, v)) 0)
      (fun u v => (data n z).getD (2 * (n * n) + pairIndex (u, v)) 0)
      (window n) p := by simpa only [hab, hbc, hac] using hp
  have hcost := DyadicCost.components_timeBound_le hf (by norm_num : (1 : ℝ) ≤ 1)
    (data n z) mem hv' hp'
  change (_ : ℝ) ≤ DyadicCost.costCoefficient 1 n * ((n : ℝ) ^ 3 / groups n) at hcost
  have hcoeff := hN n ((le_max_left _ _).trans hnN)
  calc
    _ ≤ DyadicCost.costCoefficient 1 n * ((n : ℝ) ^ 3 / groups n) := hcost
    _ ≤ (n : ℝ) ^ (2 / 1197 - 33 / 20000 : ℝ) * ((n : ℝ) ^ 3 / groups n) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ ≤ (n : ℝ) ^ (2 / 1197 - 33 / 20000 : ℝ) *
        (16 * (n : ℝ) ^ (3 - 2 / 1197 : ℝ)) :=
      mul_le_mul_of_nonneg_left (cubic_div_groups_le hn) (by positivity)
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add (by exact_mod_cast hn)]
      norm_num

-- A genuine zero-triangle family, with all cost hypotheses discharged.
example : ConstantBudget 0 := constant_budget 0 (by norm_num)

-- Nonzero original signed words use the same quantified component theorem.
example : ConstantBudget 1 := constant_budget 1 (by norm_num)
example : ConstantBudget (-1) := constant_budget (-1) (by norm_num)

end ComplexityTests.WordRAMExactTriangleSubcubicBudget
