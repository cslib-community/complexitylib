/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Frontier.Rectangle

/-! The generic rectangle API is available without the quadratic-form layer. -/

open Cslib.Circuits.Frontier Set
open scoped Finset

example {ι U : Type*} (X : Set ι) (A : Set (X → U)) (B : Set (↥Xᶜ → U)) :
    (rectangle X A B).ncard = A.ncard * B.ncard :=
  ncard_rectangle X A B

example (S R : Set (Fin 1 → Bool)) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ R)] :
    signedCount S R = ∑ x with x ∈ R, if x ∈ S then (1 : ℝ) else -1 :=
  signedCount_eq_sum S R

-- The zero-coordinate cube has one input, so the signed count is nonzero.
example : signedCount (univ : Set (Fin 0 → Bool)) univ = 1 := by
  rw [signedCount_eq_sum]
  simp
