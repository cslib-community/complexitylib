/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.NearNeighbor.Hamming
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum

/-!
# Tests for the LSH near-neighbour structure

1. Concrete runs of `candidates`, `query` and `queryRepeat` on `Fin 8` with two tables keyed by
   bits 0 and 1. The stop rule decides the outcome: with `T ≤ 2` the two far candidates exhaust
   the budget, and with `T = 3` the near candidate is returned.
2. The failure bound `e⁻¹ + 1 / 3` is below `1`, so the guarantee is not vacuous.
3. Concrete parameters: `numHashes 16 (1 / 2) = 4`, and `ρ ≤ 1 / 2` for bit sampling with
   `r / d = 1 / 4`, `c = 2`.
4. Nonvacuity of the Hamming-space theorem: its hypotheses hold for a three-word set in
   `Fin 8 → Bool`.
-/

public section

namespace ComplexityTests.NearNeighbor

open Cslib.Probability Cslib.DataStructure.NearNeighbor

/-! ### Concrete runs -/

/-- Two bit-extraction hashes on `Fin 8`: seed `false` reads bit 0, seed `true` reads bit 1. -/
def toyHash (b : Bool) (x : Fin 8) : Bool :=
  if b then (x.val / 2) % 2 == 1 else x.val % 2 == 1

/-- Far means differing by at least `2`. -/
@[expose] def toyFar (x y : Fin 8) : Prop := 2 ≤ Int.natAbs ((x.val : ℤ) - y.val)

instance : DecidableRel toyFar := fun x y =>
  inferInstanceAs (Decidable (2 ≤ Int.natAbs ((x.val : ℤ) - y.val)))

/-- Table `0` reads bit 0 and table `1` reads bit 1. -/
def toySeeds : Fin 2 → Bool := ![false, true]

-- Query `5` (odd, bit 1 clear) against `[0, 7, 4]`: table 0 (odd words) gives `7`, table 1
-- (bit 1 clear) gives `0, 4`.
example : candidates toyHash toySeeds [0, 7, 4] 5 = [7, 0, 4] := by decide

-- `7` and `0` are far from `5`, `4` is not: the stop rule decides.
example : query toyHash toyFar toySeeds 1 [0, 7, 4] 5 = none := by decide
example : query toyHash toyFar toySeeds 2 [0, 7, 4] 5 = none := by decide
example : query toyHash toyFar toySeeds 3 [0, 7, 4] 5 = some 4 := by decide

-- Repetition: the second structure (both tables on bit 1) succeeds with `T = 2`.
example : queryRepeat toyHash toyFar ![toySeeds, ![true, true]] 2 [0, 7, 4] 5 = some 4 := by
  decide

/-! ### Numerics -/

/-- The single-structure failure bound is below `1`. -/
example : Real.exp (-1) + 1 / 3 < 1 := by
  have := Real.exp_neg_one_lt_d9
  norm_num at this ⊢
  linarith

/-- With `R = 10` repetitions the failure bound drops below `0.03`. -/
example : (Real.exp (-1) + 1 / 3) ^ 10 < 0.03 := by
  have h0 : 0 ≤ Real.exp (-1) + 1 / 3 := by positivity
  have h1 : Real.exp (-1) + 1 / 3 ≤ 0.702 := by
    have := Real.exp_neg_one_lt_d9
    norm_num at this ⊢
    linarith
  calc (Real.exp (-1) + 1 / 3) ^ 10 ≤ (0.702 : ℝ) ^ 10 := pow_le_pow_left₀ h0 h1 10
    _ < 0.03 := by norm_num

/-- `k = ⌈log 16 / log 2⌉ = 4`. -/
example : numHashes 16 (1 / 2) = 4 := by
  have h : Real.log (16 : ℕ) / Real.log (1 / (1 / 2)) = 4 := by
    rw [one_div_one_div, show ((16 : ℕ) : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    have : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    field_simp
    norm_num
  rw [numHashes, h]
  norm_num

/-- Bit sampling with `r / d = 1 / 4` and `c = 2` has `ρ ≤ 1 / 2`. -/
example : rho (1 - 1 / 4) (1 - 2 * (1 / 4)) ≤ 1 / 2 :=
  rho_one_sub_le (by norm_num) (by norm_num) (by norm_num)

/-! ### Nonvacuity of the Hamming-space theorem -/

/-- A query and a word at Hamming distance `1` from it. -/
def word₀ : Fin 8 → Bool := fun _ => false
def word₁ : Fin 8 → Bool := fun i => i = 0

example : hammingDist word₁ word₀ = 1 := by decide

/-- The hypotheses of `toOuterMeasure_query_bitSampling_eq_none_le` hold with `r = 1`, `c = 2`,
`d = 8`, for the set `{word₁, ¬word₀, word₀ ∘ succ}`. -/
example :
    ((PMF.iid (PMF.iid (PMF.uniformOfFintype (Fin 8))
        (numHashes 3 (1 - 2 * 1 / Fintype.card (Fin 8))))
        (numTables 3 (1 - 1 / Fintype.card (Fin 8))
          (1 - 2 * 1 / Fintype.card (Fin 8)))).toOuterMeasure
        {s | query (andHash (fun i (z : Fin 8 → Bool) => z i)
          (numHashes 3 (1 - 2 * 1 / Fintype.card (Fin 8))))
          (fun x y => 2 * 1 ≤ (hammingDist x y : ℝ)) s
          (3 * numTables 3 (1 - 1 / Fintype.card (Fin 8)) (1 - 2 * 1 / Fintype.card (Fin 8)))
          [word₁, fun _ => true, fun i => i = 7] word₀ = none}).toReal ≤
      Real.exp (-1) + 1 / 3 :=
  toOuterMeasure_query_bitSampling_eq_none_le (P := [word₁, fun _ => true, fun i => i = 7])
    (x₀ := word₁) one_pos one_lt_two (by simp only [Fintype.card_fin]; norm_num)
    List.mem_cons_self (by norm_num [show hammingDist word₁ word₀ = 1 by decide])

end ComplexityTests.NearNeighbor
