/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORDecay
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Arbitrary-bit Add/XNOR spectrum clients and boundary cases -/

public section

namespace CslibFrontierTests.AddXNORSpectrum

open Cslib.Cryptanalysis.AddXNOR
open scoped BigOperators Topology

-- The bit-two two-addition correlation is nonzero, although bit one's is zero.
/-- An explicit higher-bit signed correlation. -/
theorem bit_two_two : bitRunFactor 3 2 2 = -1/4 := by
  rw [bitRunFactor_low 0 2 2]
  have hu : (Finset.univ : Finset (BitVec 2)) = {0#2, 1#2, 2#2, 3#2} := by
    ext x
    rcases x with ⟨x⟩
    fin_cases x <;> decide
  norm_num [lowRun, Function.iterate_succ_apply', lowTransfer,
    Finset.expect_eq_sum_div_card, hu, BitVec.carry_width, sign, BitVec.toNat_add,
    BitVec.toNat_ofNat]

example : bitRunFactor 3 1 2 = 0 := by
  rw [bitRunFactor_bit_one 1]
  norm_num [runFactor, Function.iterate_succ_apply']

example : bitRunFactor 12 2 2 = -1/4 := by
  rw [bitRunFactor_low 9 2 2, ← bitRunFactor_low 0 2 2, bit_two_two]

-- A reset separates genuinely higher-bit runs; zero runs encode extra XNORs.
example : bitCorrelation 12 2 (runs [2, 0, 2]) = 1/16 := by
  rw [bitCorrelation_runs]
  have hz : bitRunFactor 12 2 0 = 1 := by
    simp [bitRunFactor, bitCorrelation, bitFrom, sign]
  have ht : bitRunFactor 12 2 2 = -1/4 := by
    rw [bitRunFactor_low 9 2 2, ← bitRunFactor_low 0 2 2, bit_two_two]
  norm_num [hz, ht]

-- Matrix orientation: only a wrap has a negative entry.
example : carryMatrix 3 (1#3) (6#3) = -1 := by decide
example : carryMatrix 3 (6#3) (1#3) = 1 := by decide
example : BitVec.carry 3 (6#3) (3#3) false = true ∧
    (6#3 + 3#3).toNat = 1 := by decide

-- Empty runs, zero-width words, and out-of-width observations are admitted.
example : bitCorrelation 0 7 [] = 1 := by simp [bitCorrelation, bitFrom, sign]
example : bitRunFactor 8 3 0 = 1 := by
  simp [bitRunFactor, bitCorrelation, bitFrom, sign]

-- A full-word client of the exact spectral formula, not a supplied transfer model.
example (z : ℕ) : (bitRunFactor 12 3 z : ℂ) =
    (2 ^ 3 : ℂ)⁻¹ ^ (z + 2) * ∑ k : Fin (2 ^ 3),
      (Complex.normSq (carryEigenvalue (2 ^ 3) k) : ℂ) *
        carryEigenvalue (2 ^ 3) k ^ z := bitRunFactor_spectrum 8 3 z


-- Quantified decay, strict extremality, equality subsequence and limit.
example (z : ℕ) : |(bitRunFactor 12 3 z : ℝ)| ≤ (1 / Real.sqrt 2) ^ z :=
  abs_bitRunFactor_le_bit_one 8 3 z (by decide)
example : bitDecay 3 < bitDecay 1 := bitDecay_strictAnti (by decide)
example (t : ℕ) : |(bitRunFactor 12 1 (4 * t) : ℝ)| =
    (1 / Real.sqrt 2) ^ (4 * t) := abs_bitRunFactor_bit_one_four 10 t
example (bs : List Bool) : |(bitCorrelation 12 3 bs : ℝ)| ≤
    (1 / Real.sqrt 2) ^ bs.count false := abs_bitCorrelation_le_bit_one 8 3 bs (by decide)

end CslibFrontierTests.AddXNORSpectrum
