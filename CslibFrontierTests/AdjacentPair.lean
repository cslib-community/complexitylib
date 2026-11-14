/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.QueryComplexity.AdjacentPair

/-! # Adjacent-pair block functions (Arora–Barak Chapter 11 Exercise 2) -/

open Cslib Cslib.BitString Cslib.QueryComplexity

/-! ## The local predicate -/

-- The middle pair is allowed, even though it is not one of the disjoint pairs (0,1), (2,3).
example : adjacentPair 4 ![false, true, true, false] = true := by decide
-- Separated true bits and a pair plus an extra bit are rejected.
example : adjacentPair 4 ![true, false, true, false] = false := by decide
example : adjacentPair 4 ![true, true, true, false] = false := by decide
example : adjacentPair 4 ![true, true, false, true] = false := by decide
example : adjacentPair 5 ![false, false, false, true, true] = true := by decide

-- Empty and one-bit blocks never contain an adjacent pair.
example : adjacentPair 0 (fun _ => false) = false := by decide
example : adjacentPair 1 ![true] = false := by decide

-- A false three-bit block may be completed by either neighbor of its sole true bit.
example : sensitivityAt (adjacentPair 3) ![false, true, false] = 2 := by decide
example : sensitivityAt (adjacentPair 3) ![true, true, false] = 3 := by decide

/-! ## The nonsquare layout `n = 7`: two blocks of sizes 4 and 3 -/

example : Nat.sqrt 7 = 2 := Nat.eq_sqrt.mpr (by decide) |>.symm
example : ∀ i, sqrtBlockSizes 7 i = if i.val = 0 then 4 else 3 := by decide +kernel

-- An overlapping pair inside the first block, and a pair inside the second block.
example : adjacentPairSqrt 7 ![false, true, true, false, false, false, false] = true := by
  decide +kernel
example : adjacentPairSqrt 7 ![false, false, false, false, false, true, true] = true := by
  decide +kernel
-- Positions 3 and 4 are adjacent in `Fin 7` but lie in different blocks.
example : adjacentPairSqrt 7 ![false, false, false, true, true, false, false] = false := by
  decide +kernel
-- A pair plus an extra bit in the same block, and separated bits, are rejected.
example : adjacentPairSqrt 7 ![true, true, false, true, false, false, false] = false := by
  decide +kernel
example : adjacentPairSqrt 7 ![true, false, true, false, false, false, false] = false := by
  decide +kernel
-- An accepted block is enough even if another block is rejected.
example : adjacentPairSqrt 7 ![true, true, false, false, true, false, true] = true := by
  decide +kernel

/-! ## Small-length conventions -/

example (x : BitString 0) : adjacentPairSqrt 0 x = false := adjacentPairSqrt_zero_length x
-- For `1 ≤ n ≤ 3` there is one block of `n` bits.
example : adjacentPairSqrt 1 ![true] = false := by decide +kernel
example : adjacentPairSqrt 3 ![false, true, true] = true := by decide +kernel

/-! ## Measures -/

-- The four native measures at the nonsquare length `n = 7`.
example : 2 ≤ sensitivity (adjacentPairSqrt 7) ∧ sensitivity (adjacentPairSqrt 7) ≤ 6 ∧
    7 ≤ 3 * blockSensitivity (adjacentPairSqrt 7) ∧
    blockSensitivity (adjacentPairSqrt 7) ≤ certificateComplexity (adjacentPairSqrt 7) ∧
    certificateComplexity (adjacentPairSqrt 7) ≤ DecisionTree.complexity (adjacentPairSqrt 7) ∧
    DecisionTree.complexity (adjacentPairSqrt 7) ≤ 7 := by
  have hs : Nat.sqrt 7 = 2 := (Nat.eq_sqrt.mpr (by decide)).symm
  simpa only [hs] using adjacentPairSqrt_measures (n := 7) (by decide)

-- The general statement for every length `n ≥ 4`.
example (n : ℕ) (hn : 4 ≤ n) :
    Nat.sqrt n ≤ sensitivity (adjacentPairSqrt n) ∧
      n ≤ 3 * blockSensitivity (adjacentPairSqrt n) :=
  ⟨sqrt_le_sensitivity_adjacentPairSqrt hn, card_le_three_mul_blockSensitivity_adjacentPairSqrt hn⟩

-- The disjoint sensitive-pair family at zero is nonempty: it has `4 / 2 + 3 / 2 = 3` pairs.
example : (adjacentPairSensitiveFamily (sum_sqrtBlockSizes 7)).card = 3 := by
  rw [card_adjacentPairSensitiveFamily]
  decide +kernel

example : (adjacentPairSensitiveFamily (sum_sqrtBlockSizes 7)).Nonempty := by
  rw [← Finset.card_pos, card_adjacentPairSensitiveFamily]
  decide +kernel

example : IsSensitiveFamily (adjacentPairSqrt 7) (fun _ => false)
    (adjacentPairSensitiveFamily (sum_sqrtBlockSizes 7)) :=
  isSensitiveFamily_adjacentPairSensitiveFamily _

/-! ## Unequal blocks in general -/

-- Three blocks of sizes 2, 5 and 3: sensitivity at most `max (3 * 3) 5 = 9`.
example : sensitivity (adjacentPairBlocks (sizes := ![2, 5, 3]) (n := 10) (by decide)) ≤ 9 := by
  simpa using sensitivity_adjacentPairBlocks_le (sizes := ![2, 5, 3]) (n := 10) (by decide)
    (M := 5) (by decide)
