/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.PropertyTesting.Distribution.ClosenessFlattening

/-! Concrete instances of occurrence counts, split distributions and the flattening tester. -/

namespace ComplexityTests.DistributionTestingClosenessFlattening

open Cslib.Probability.PMF Cslib.DistributionTesting

-- Occurrence counts of concrete samples, and their sum.
example : occurrenceCount (![0, 1, 0] : Fin 3 → Fin 2) 0 = 2 := by decide

example : ∑ b, occurrenceCount (![0, 1, 0] : Fin 3 → Fin 2) b = 3 := sum_occurrenceCount _

-- Flattening counts: `0` occurs three times in `0, 1` and `0, 0` together, `1` once.
example : flatteningCount (![0, 1] : Fin 2 → Fin 2) ![0, 0] 0 = 3 := by decide

example : flatteningCount (![0, 1] : Fin 2 → Fin 2) ![0, 0] 1 = 1 := by decide

-- Splitting a fair coin's `0` into three cells: each cell has mass `1 / 6`.
example : (split (uniformOfFintype (Fin 2)) ![2, 0] ⟨0, 1⟩).toReal = 1 / 6 := by
  rw [split_apply_toReal]
  norm_num [uniformOfFintype_apply]

-- The split domain of `Fin 2` with counts `2, 0` has `2 + 2 = 4` points.
example : Fintype.card (Σ i : Fin 2, Fin ((![2, 0] : Fin 2 → ℕ) i + 1)) = 4 := by
  rw [card_sigma_split]
  decide

-- Splitting each side of a fair coin in two gives collision probability `1 / 4`, as for the
-- uniform distribution on the four cells.
example : collisionProbability (split (uniformOfFintype (Fin 2)) fun _ => 1) = 1 / 4 := by
  rw [collisionProbability_split]
  norm_num [uniformOfFintype_apply]

-- Splitting preserves the distance between two point masses.
example : dist (split (PMF.pure true) fun _ => 3) (split (PMF.pure false) fun _ => 3) = 1 := by
  rw [dist_split, dist_eq]
  norm_num [PMF.pure_apply]

-- A satisfiable instance of the main hypothesis on `100` points with `ε = 1`: `99` flattening
-- samples (`√100 = 10`) and `5151` testing samples, since `864 · 298 = 257472 ≤ 5 · 5150 · 10`.
example : IsClosenessTester (closenessFlatteningTester (α := Fin 100) 99 5151 1) 1 := by
  refine isClosenessTester_closenessFlatteningTester (by norm_num) ?_
  have h : Real.sqrt ((99 : ℕ) + 1) = 10 := by
    rw [show ((99 : ℕ) : ℝ) + 1 = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h, Fintype.card_fin]
  norm_num

/-- The flattening tester on `Bool` with `3` flattening samples (`√4 = 2`) and `2766` testing
samples is a closeness tester with proximity `1 / 2`, since `864 · 8 = 6912 ≤ 5 · 2765 / 4 · 2`. -/
theorem isClosenessTester_bool :
    IsClosenessTester (closenessFlatteningTester (α := Bool) 3 2766 (1 / 2)) (1 / 2) := by
  refine isClosenessTester_closenessFlatteningTester (by norm_num) ?_
  have h : Real.sqrt ((3 : ℕ) + 1) = 2 := by
    rw [show ((3 : ℕ) : ℝ) + 1 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h, Fintype.card_bool]
  norm_num

-- Completeness: it accepts a fair coin against itself with probability at least `2 / 3`.
example : 2 / 3 ≤ acceptProb₂ (closenessFlatteningTester (α := Bool) 3 2766 (1 / 2))
    (uniformOfFintype Bool) (uniformOfFintype Bool) :=
  isClosenessTester_bool.accept _

-- Nonvacuity: it rejects two point masses on different values with probability at least `2 / 3`.
example : acceptProb₂ (closenessFlatteningTester (α := Bool) 3 2766 (1 / 2))
    (PMF.pure true) (PMF.pure false) ≤ 1 / 3 := by
  refine isClosenessTester_bool.reject _ _ ?_
  rw [dist_eq]
  norm_num [PMF.pure_apply]

-- The rate corollary applies on every nonempty domain.
example : ∃ m k : ℕ, ((m + k : ℕ) : ℝ) ≤
    520 * max ((Fintype.card (Fin 1000) : ℝ) ^ (2 / 3 : ℝ) / (1 / 10 : ℝ) ^ (4 / 3 : ℝ))
      (Real.sqrt (Fintype.card (Fin 1000)) / (1 / 10) ^ 2) + 3 ∧
    IsClosenessTester (closenessFlatteningTester (α := Fin 1000) m k (1 / 10)) (1 / 10) :=
  exists_isClosenessTester_closenessFlatteningTester (by norm_num)

end ComplexityTests.DistributionTestingClosenessFlattening
