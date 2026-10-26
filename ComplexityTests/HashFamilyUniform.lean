/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Probability.HashFamily.Uniform
import Mathlib.Data.ZMod.Basic

/-! The shared uniform-function laws retain arbitrary finite domains and additive groups.
Empty domains and a one-element codomain need no additional hypotheses.
-/

open Cslib Cslib.Probability
open scoped ENNReal

example {X G : Type*} [Fintype X] [DecidableEq X] [AddGroup G] [Fintype G] [Nonempty G] :
    IsDeltaUniversalHash (PMF.uniformOfFintype (X → G)) id (Fintype.card G : ℝ≥0∞)⁻¹ :=
  isDeltaUniversalHash_uniformOfFintype

example {X G : Type*} [Fintype X] [DecidableEq X] [AddGroup G] [Fintype G] [Nonempty G] :
    IsDeltaUniversalHash (PMF.uniformOfFintype (X → G)) (fun f x => -f x)
      (Fintype.card G : ℝ≥0∞)⁻¹ :=
  isDeltaUniversalHash_neg_uniformOfFintype

example : IsDeltaUniversalHash (PMF.uniformOfFintype (Empty → ZMod 3)) id
    (Fintype.card (ZMod 3) : ℝ≥0∞)⁻¹ :=
  isDeltaUniversalHash_uniformOfFintype

example : IsDeltaUniversalHash (PMF.uniformOfFintype (Bool → ZMod 1)) (fun f x => -f x)
    (Fintype.card (ZMod 1) : ℝ≥0∞)⁻¹ :=
  isDeltaUniversalHash_neg_uniformOfFintype
