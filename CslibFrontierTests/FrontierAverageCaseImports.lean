/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Frontier.AverageCase

/-! Generic correlation clients need only the average-case layer. -/

open Cslib.Circuits.Frontier Set
open scoped Finset

example {ι U : Type*} [Finite ι] [Finite U] [Nonempty U] (S T : Set (ι → U)) :
    correlation S T = 2 * agreement S T - 1 :=
  correlation_eq_two_mul_agreement_sub_one S T

example (S T : Set (Fin 1 → Bool)) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] :
    correlation S T * Fintype.card (Fin 1 → Bool) =
      ∑ x, if (x ∈ S ↔ x ∈ T) then (1 : ℝ) else -1 :=
  correlation_mul_card_eq_sum S T

-- Opposite constant functions disagree on the unique zero-coordinate input.
example : correlation (univ : Set (Fin 0 → Bool)) ∅ = -1 := by
  rw [correlation_eq_two_mul_agreement_sub_one]
  simp [agreement]
