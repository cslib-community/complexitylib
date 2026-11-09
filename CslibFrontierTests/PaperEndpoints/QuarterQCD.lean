/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.FacilityLocation.QuarterQCD

/-! Regression clients for the actual normalized quarter-QCD mechanism. -/

open Cslib.FacilityLocation.QuarterQCD

public theorem profitable_deviation : cost 1 3 4 0 < cost 0 3 4 0 := quarterQCD_counterexample.2.1

example : ∀ t : ℝ, 0 ≤ t → t < 8 → 4 ≤ socialCost 0 3 4 t := witness_optimum.2

example : ¬ Strategyproof := quarterQCD_counterexample.1
