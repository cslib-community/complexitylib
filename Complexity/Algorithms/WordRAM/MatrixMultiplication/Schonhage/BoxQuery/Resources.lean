/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Kernel
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Bounds

/-!
# Separate shared and sparse native query costs

The actual prefix traversal is charged by the existing alpha counts through the
threshold. Table construction is a separate cost: shared geometry is polynomial-depth
times the encoding span, while one retained tile is controlled by the beta counts.
These bounds describe this native implementation, not a simulation of a source trace.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The reusable query's actual charged bound is linear in its sparse leaf count,
with one depth factor for all prefix tasks. It does not scan the complete encoding span. -/
theorem queryTime_eq_alpha {L m : ℕ} (t : ℕ) (η : OutStr L)
    (hη : (innerSetO η).card = m) :
    queryTime m t η = 258 * (L + 1) * (∑ d ∈ Finset.range (t + 1), alpha m d) + 28 := by
  unfold queryTime
  rw [card_queryLeaves t η hη]

/-- Original input adaptation, shared geometry and one compact retained tile are
charged separately from every query. -/
theorem preparationTime_le (L m t : ℕ) (hm : m ≤ L) (ht : t ≤ m) :
    preparationTime L m t ≤ 4 * L + 21 + 64 * (L + 1) ^ 2 * 10 ^ L +
      328 * (m + 1) * (∑ d ∈ Finset.Icc t m, beta L m d) + 8 := by
  have hg := BoxTable.geometryTime_le L m t hm
  have hb := BoxTable.tileTime_le L m t hm ht
  unfold preparationTime
  unfold BoxTable.tileTime at hb
  omega

/-- Directory, descriptors, retained values and uncleared sparse traversal stack
all use polynomial-depth times the original encoding-array length. -/
theorem allocation_le (L m t : ℕ) (hm : m ≤ L) :
    memoryEnd L m t - directoryBase L ≤ 10 * (L + 1) * 10 ^ L + 50 := by
  have hB := Nat.count_le (BoxTable.Eligible L (m - t)) (n := (m - t + 1) * 10 ^ L)
  rw [BoxTable.count_eligible_eq_card_boxes] at hB
  have hS := Nat.mul_le_mul_right (10 ^ L) (by omega : m - t + 1 ≤ L + 1)
  unfold memoryEnd stackBase valueBase recordBase stackCapacity
  apply Nat.sub_le_of_le_add
  nlinarith

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
