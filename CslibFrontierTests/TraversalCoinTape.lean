/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Languages.Probabilistic.Traverse.CoinTape
import CslibFrontier.Languages.Probabilistic.BitString

/-! Flat traversal tapes preserve separate draws at repeated inputs and need a component
realization only on actual list members. Empty lists and zero-width blocks are included. -/

namespace ComplexityTests.TraversalCoinTape

open Cslib Cslib.Probability

private def evaluate (n : ℕ) (seed : List Bool) : List Bool := decide (n = 1) :: seed

private noncomputable def program (n : ℕ) : ProbComp (List Bool) :=
  if n < 2 then evaluate n <$> BitString.sampleList 1 else BitString.sampleList 2

-- The supplied one-bit evaluator is valid at every input in this traversal.
-- No matching evaluator is required for the two-bit branch at input 2.
example : ProbComp.eval ([0, 1, 0].mapM program) =
    (BitString.uniformList 3).map (fun tape =>
      List.zipWith evaluate [0, 1, 0] (BitString.listRows 3 1 tape)) := by
  apply ProbComp.eval_mapM_of_uniformList program evaluate 1 [0, 1, 0]
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl <;>
    simp [program, ProbComp.eval_map, BitString.eval_sampleList]

-- Repeated input 0 does not reuse its earlier seed: first and last output bits differ.
example : List.zipWith evaluate [0, 1, 0] (BitString.listRows 3 1 [true, false, false]) =
    [[false, true], [true, false], [false, false]] := by decide

-- Outside the actual input list the proposed realization is intentionally different.
example : [true, false] ∈ (ProbComp.eval (program 2)).support ∧
    [true, false] ∉ ((BitString.uniformList 1).map (evaluate 2)).support := by
  constructor
  · change [true, false] ∈ (ProbComp.eval (BitString.sampleList 2)).support
    rw [BitString.eval_sampleList]
    exact BitString.mem_support_uniformList_iff.mpr rfl
  · rw [PMF.mem_support_map_iff]
    rintro ⟨seed, _, heq⟩
    simp [evaluate] at heq

example : ProbComp.eval (([] : List ℕ).mapM program) =
    (BitString.uniformList 0).map (fun tape =>
      List.zipWith evaluate [] (BitString.listRows 0 1 tape)) := by
  apply ProbComp.eval_mapM_of_uniformList program evaluate 1 []
  simp

-- Width zero retains a separate empty block for every input.
example : BitString.listRows 3 0 [] = [[], [], []] := by decide

example (values : List Bool) : ProbComp.eval (values.mapM fun bit => pure (!bit)) =
    (BitString.uniformList (values.length * 0)).map (fun tape =>
      List.zipWith (fun bit _ => !bit) values (BitString.listRows values.length 0 tape)) := by
  apply ProbComp.eval_mapM_of_uniformList (fun bit => pure (!bit)) (fun bit _ => !bit) 0 values
  intro bit _
  simp

end ComplexityTests.TraversalCoinTape
