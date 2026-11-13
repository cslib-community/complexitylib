/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.MachineLearning.PACLearning.AgnosticVCSharp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith

/-! Ordinary-module clients of the sharp agnostic sample-size API: its explicit numeric bound
and the sample-complexity endpoint for a class of finite VC dimension. -/

namespace CslibFrontierTests.AgnosticVCSharp

open Cslib.MachineLearning.PACLearning
open scoped NNReal ENNReal

/-- The chaining sample size of thresholds at `ε = δ = 1 / 10` is
`400 (16384 + 32 log 40) ≤ 6607000`, since `40 ≤ 2 ^ 6`. -/
public theorem chainingSampleSize_tenth_le :
    chainingSampleSize 1 ((1 / 10 : ℝ) / 2) (1 / 10) ≤ 6607000 := by
  have h40 : Real.log (4 / (1 / 10 : ℝ)) ≤ 6 * Real.log 2 := by
    calc Real.log (4 / (1 / 10 : ℝ)) ≤ Real.log ((2 : ℝ) ^ 6) :=
          Real.log_le_log (by norm_num) (by norm_num)
      _ = 6 * Real.log 2 := by rw [Real.log_pow]; norm_num
  rw [chainingSampleSize, div_le_iff₀ (by norm_num)]
  push_cast
  nlinarith [Real.log_two_lt_d9]

/-- The public sample-complexity endpoint is available through an ordinary import. -/
example {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    {C : ConceptClass α Bool} (hC : HasFiniteVCDim C) (ε δ : Set.Ioo (0 : ℝ≥0) 1) :
    sampleComplexity IsPACLearnerFor C ε δ Set.univ ≤
      ⌈chainingSampleSize (vcDim C) ((ε.val : ℝ) / 2) δ.val⌉₊ :=
  sampleComplexity_univ_le_chainingSampleSize hC ε δ

end CslibFrontierTests.AgnosticVCSharp
