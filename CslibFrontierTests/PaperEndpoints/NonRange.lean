/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Statistics.LeastSquares.NonRange
import all CslibFrontier.Statistics.LeastSquares.NonRange
import Mathlib.Tactic.NormNum

/-! Positive and negative clients for the retained-set geometric semantics. -/

open Cslib.LeastSquares.NonRange

public theorem optimum_not_range : ¬ IsRange retained := not_range

example : IsRange ∅ := by
  refine ⟨![0, 0, 0, 1], fun i => ?_⟩
  norm_num [planeValue]

example (s : Finset (Fin 6)) (hs : s.card = 4) (hne : s ≠ retained) :
    scatter retained < scatter s := nonrange_optimum.2.2.2.1 s hs hne

example : scatter retained = -37469/8000 := unique_minimum.2.1
