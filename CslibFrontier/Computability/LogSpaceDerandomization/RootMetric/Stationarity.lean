/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.RootMetric.ConditionalWalk

/-!
# Stationarity on retained environment slices

Conditional walks preserve the uniform mean of their actual retained-pair slice,
including when that slice is empty. No independence between coordinates is required.
-/

public section

namespace Cslib

open Finset
open scoped BigOperators

variable {Ω V D : Type*} [Fintype Ω] [Fintype D] [Nonempty D]
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]

/-- Stationarity of the genuine conditional walk, also on an empty retained slice. -/
theorem rowSliceMean_conditionalWalk
    (G : ∀ x y, RotationMap (RetainedPairSlice X Y x y) D) (t : V → V → ℕ)
    (F : Ω → V → V → ℝ) (x y : V) :
    rowSliceMean X Y (conditionalWalk X Y G t F) x y = rowSliceMean X Y F x y := by
  unfold rowSliceMean
  rw [← expect_retainedPairSlice X Y x y, ← expect_retainedPairSlice X Y x y]
  simp only [conditionalWalk_coe]
  exact (G x y).expect_walk_pow (2 * t x y) (fun σ => F σ.val x y)

end Cslib
