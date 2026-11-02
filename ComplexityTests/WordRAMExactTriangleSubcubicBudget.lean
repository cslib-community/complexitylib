/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.DyadicCost.Asymptotics
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
open ParameterChoice

private def data (n : ℕ) (z : ℤ) : List ℤ := List.replicate (3 * (n * n)) z

private theorem pair_bound {n : ℕ} (a b : Fin n) : pairIndex (a, b) < n * n := by
  have h := Nat.mul_le_mul_right n (Nat.succ_le_of_lt a.isLt)
  dsimp only [pairIndex]
  nlinarith only [h, b.isLt]

private def ConstantBudget (z : ℤ) : Prop :=
  ∃ N : ℕ, 2 ^ 1296 ≤ N ∧ ∀ n ≥ N, ∃ hn : 0 < n, ∃ p,
    IsSelectedPrime (fun _ _ : Fin n => z) (fun _ _ => z) (fun _ _ => z) (window n) p ∧
      ∀ mem : ℕ → ℕ,
        ((12 * Nat.log 2 n + 36 + (PrimeSelection.timeBound n (window n) + 16) +
            FixedPrime.timeBound (m := level n) hn (groups n) p (data n z) mem : ℕ) : ℝ) ≤
          4 * (n : ℝ) ^ (3 - 1 / 1296 : ℝ)

-- Permit normalization of the existing concrete fast-threshold numeral in this client.
set_option exponentiation.threshold 1296 in
private theorem constant_budget (z : ℤ) (hz : |z| ≤ 1) : ConstantBudget z := by
  obtain ⟨N, hthreshold, hcost⟩ :=
    DyadicCost.exists_components_subcubic_threshold (by norm_num : (1 : ℝ) ≤ 1)
  refine ⟨N, hthreshold, ?_⟩
  intro n hnN
  have hn : 0 < n := (Nat.two_pow_pos 1296).trans_le (hthreshold.trans hnN)
  have hf : 0 < blocks n := (blocks_pos_iff n).mpr (hthreshold.trans hnN)
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
  apply hcost n hnN hn (data n z) mem p
  · simpa only [hab, hbc, hac] using hv
  · simpa only [hab, hbc, hac] using hp

-- A genuine zero-triangle family, with all cost hypotheses discharged.
example : ConstantBudget 0 := constant_budget 0 (by norm_num)

-- Nonzero original signed words use the same quantified component theorem.
example : ConstantBudget 1 := constant_budget 1 (by norm_num)
example : ConstantBudget (-1) := constant_budget (-1) (by norm_num)

end ComplexityTests.WordRAMExactTriangleSubcubicBudget
