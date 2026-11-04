/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.DyadicCost
import Mathlib.Data.List.GetD

/-!
# Nonvacuous aggregate-cost clients

The infinite dyadic family below discharges the fast-regime and selected-prime hypotheses for
original zero matrices. It applies the actual native component budgets, rather than assuming
an execution/time certificate. This is a cost client, not a huge interpreter evaluation or
an already composed ET/3SUM solver.
-/

namespace ComplexityTests.WordRAMExactTriangleDyadicCost

open Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.WordRAM.ExactTriangle
open ParameterChoice

private def family (k : ℕ) : ℕ := 2 ^ (1296 * (k + 1))
private def zeros (n : ℕ) : List ℤ := List.replicate (3 * (n * n)) 0

private theorem blocks_family (k : ℕ) : blocks (family k) = k + 1 := by
  rw [blocks, family, Nat.log_pow (by decide)]
  omega

private theorem family_fast (k : ℕ) : 0 < blocks (family k) := by rw [blocks_family]; omega

private theorem zero_read (n q : ℕ) : (zeros n).getD q 0 = 0 :=
  List.getElem?_getD_replicate_default_eq _ _ _

-- Every member has exact nontrivial fast geometry; no giant constant power is evaluated.
example (k : ℕ) : groups (family k) ^ 36 = window (family k) ∧
    16 ≤ window (family k) ∧ window (family k) ^ 18 ≤ family k :=
  ⟨groups_pow _, window_ge_sixteen (family_fast k), geometry (pos_of_blocks_pos (family_fast k))⟩

-- The full selector charge, including the actual native counter calls, has the saving.
example (k : ℕ) :
    ((PrimeSelection.timeBound (family k) (window (family k)) + 16 : ℕ) : ℝ) ≤
      237140 * ((family k : ℝ) ^ 3 / groups (family k)) :=
  DyadicCost.selection_timeBound_le (pos_of_blocks_pos (family_fast k))

-- All component-cost hypotheses are discharged on genuine original arrays and a prime
-- whose existence follows from the existing finite selected-prime theorem.
example (k : ℕ) :
    ∃ p, IsSelectedPrime (fun _ _ : Fin (family k) => (0 : ℤ))
      (fun _ _ => 0) (fun _ _ => 0) (window (family k)) p ∧
      ((12 * Nat.log 2 (family k) + 36 +
          (PrimeSelection.timeBound (family k) (window (family k)) + 16) +
          FixedPrime.timeBound (m := level (family k)) (pos_of_blocks_pos (family_fast k))
            (groups (family k)) p (zeros (family k)) (fun _ => 0) : ℕ) : ℝ) ≤
        (238169 + 12 * (Nat.log 2 (family k) : ℝ) +
          138412032 * ((19 * level (family k) + 1 : ℕ) : ℝ) +
          (140 * falsePositiveConst + 140) * (1 : ℝ) * Real.log (family k)) *
            ((family k : ℝ) ^ 3 / groups (family k)) := by
  obtain ⟨p, hp⟩ := exists_isSelectedPrime (fun _ _ : Fin (family k) => (0 : ℤ))
    (fun _ _ => 0) (fun _ _ => 0) (window (family k)) (window_ge_sixteen (family_fast k))
  have hv : WeightsBoundedBy
      (fun u v : Fin (family k) => (zeros (family k)).getD (pairIndex (u, v)) 0)
      (fun u v => (zeros (family k)).getD (family k * family k + pairIndex (u, v)) 0)
      (fun u v => (zeros (family k)).getD (2 * (family k * family k) + pairIndex (u, v)) 0)
      ((family k : ℝ) ^ (1 : ℝ)) := by
    simp only [WeightsBoundedBy, zero_read, abs_zero, Int.cast_zero]
    refine ⟨?_, ?_, ?_⟩ <;> intro a b <;> positivity
  have hp' : IsSelectedPrime
      (fun u v : Fin (family k) => (zeros (family k)).getD (pairIndex (u, v)) 0)
      (fun u v => (zeros (family k)).getD (family k * family k + pairIndex (u, v)) 0)
      (fun u v => (zeros (family k)).getD (2 * (family k * family k) + pairIndex (u, v)) 0)
      (window (family k)) p := by simpa only [zero_read] using hp
  exact ⟨p, hp, DyadicCost.components_timeBound_le (family_fast k) (by norm_num)
    (zeros (family k)) (fun _ => 0) hv hp'⟩

-- The real-power gain is explicit, but logarithmic factors are still outside that exponent.
example (k : ℕ) : (family k : ℝ) ^ 3 / groups (family k) ≤
    4 * (family k : ℝ) ^ (3 - 1 / 648 : ℝ) :=
  cubic_div_groups_le (pos_of_blocks_pos (family_fast k))

end ComplexityTests.WordRAMExactTriangleDyadicCost
