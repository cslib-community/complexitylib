/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.PartialCoverThresholdNative
import Mathlib.Tactic

/-!
# Uniform native threshold-search clients

The actual multiplication/guard loop reaches exact integral thresholds, stops
between powers for non-dyadic rationals, and performs no multiplication when the
budget already holds. The native certificate uses the same source count.
-/

open Cslib.Probability.StochasticOracle.PartialCover
open ThresholdNative Instance Turing.MultiTapeTM

private def exactPower : Input := ⟨⟨1 / 2, 1 / 8⟩, by constructor <;> norm_num⟩
private def betweenPowers : Input := ⟨⟨2 / 3, 1 / 4⟩, by constructor <;> norm_num⟩
private def zeroPower : Input := ⟨⟨1 / 2, 2⟩, by constructor <;> norm_num⟩

example : count exactPower = 3 := by
  have hi := (pow_le_iff_rationalRepetitions_le (1 / 2 : ℚ) (1 / 8)
    (by norm_num) (by norm_num) (by norm_num) 3).mp (by norm_num)
  have hlo := (pow_le_iff_rationalRepetitions_le (1 / 2 : ℚ) (1 / 8)
    (by norm_num) (by norm_num) (by norm_num) 2).not.mp (by norm_num)
  change count exactPower ≤ 3 at hi
  change ¬count exactPower ≤ 2 at hlo
  omega

example : count betweenPowers = 4 := by
  have hi := (pow_le_iff_rationalRepetitions_le (2 / 3 : ℚ) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) 4).mp (by norm_num)
  have hlo := (pow_le_iff_rationalRepetitions_le (2 / 3 : ℚ) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) 3).not.mp (by norm_num)
  change count betweenPowers ≤ 4 at hi
  change ¬count betweenPowers ≤ 3 at hlo
  omega

example : count zeroPower = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (pow_le_iff_rationalRepetitions_le (1 / 2 : ℚ) 2
    (by norm_num) (by norm_num) (by norm_num) 0).mp (by norm_num)

example : (ThresholdNative.step^[3] (initial exactPower.val)).map State.index = some 3 ∧
    ThresholdNative.step^[4] (initial exactPower.val) = none := by
  norm_num [Function.iterate_succ_apply', ThresholdNative.step, initial, exactPower]

example : (ThresholdNative.step^[4] (initial betweenPowers.val)).map State.index = some 4 ∧
    ThresholdNative.step^[5] (initial betweenPowers.val) = none := by
  norm_num [Function.iterate_succ_apply', ThresholdNative.step, initial, betweenPowers]

example : ThresholdNative.step (initial zeroPower.val) = none := by
  norm_num [ThresholdNative.step, initial, zeroPower]

-- A single machine and resource polynomial work for all valid binary rational inputs.
-- In particular the machine is not chosen separately for the three examples above.
example : ∃ c d : ℕ, ComputableInTimeAndSpace count inputEncoding encUnary
    (fun x => c * (count x + 1) * (count x + (inputEncoding x).length + 1) ^ d)
    (fun x => c * (count x + (inputEncoding x).length + 1) ^ d) := uniform_threshold

example (x : Input) : count x = repetitions (x.val.q : ℝ) (x.val.budget : ℝ) :=
  count_eq_repetitions x
