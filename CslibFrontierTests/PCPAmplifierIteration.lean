/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.PCP.Amplifier

/-! Shared amplification induction and the initial violated-edge lower bound. -/

namespace ComplexityTests.PCPAmplifierIteration

open Cslib.PCP

-- A concrete step reaches the positive threshold after three rounds.
example : (1 : ℝ) ≤ ((fun x : ℝ => min (2 * x) 1)^[3]) (1 / 8) := by
  convert min_two_pow_mul_le_iterate (fun x : ℝ => min (2 * x) 1) id
    (by norm_num) (fun _ => le_rfl) 3 (1 / 8) using 1 <;> norm_num

-- Negative starting values are permitted, including when the threshold is zero.
example (k : ℕ) : min (2 ^ k * (-1 : ℝ)) 0 ≤
    ((fun x : ℝ => min (2 * x) 0)^[k]) (-1) :=
  min_two_pow_mul_le_iterate _ id le_rfl (fun _ => le_rfl) k (-1)

-- A negative threshold invalidates the claimed lower bound after two rounds.
example : ¬ min ((2 : ℝ) ^ 2 * 0) (-1) ≤
    ((fun x : ℝ => min (2 * x) (-1))^[2]) 0 := by
  norm_num [Function.iterate_succ_apply']

private def violatedLoop : ConstraintGraph Unit Unit Bool where
  src := fun _ => ()
  dst := fun _ => ()
  rel := fun _ _ _ => False

-- The cardinality bound attains one on a graph with a single violated self-loop.
example : violatedLoop.unsatVal = 1 := by
  refine le_antisymm violatedLoop.unsatVal_le_one ?_
  have h : ¬ violatedLoop.Satisfiable := fun ⟨_, hσ⟩ => hσ ()
  simpa only [Fintype.card_unique, Nat.cast_one, one_mul] using
    violatedLoop.one_le_card_mul_unsatVal h

end ComplexityTests.PCPAmplifierIteration
