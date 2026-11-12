/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.DepthTwoInputs
import CslibFrontier.Computability.Circuit.Boolean.Formula.Andreev
import Mathlib.Algebra.BigOperators.Fin

/-!
Depth-two circuits whose top gate reads inputs, and sign-coherent bottom weights.
-/

open Cslib Cslib.Circuits

namespace WeightedThresholdDepthTwoInputsTests

open Boolean.WeightedThreshold Finset

/-- Exclusive or with one bottom gate: `x₀ + x₁ - 2 · [x₀ + x₁ ≥ 2] ≥ 1`. A `depthTwo` circuit,
whose top gate reads only gates, would need a second bottom gate for this. -/
noncomputable def xorCircuit : Circuit signature 2 1 :=
  depthTwoInputs (G := 1) (fun _ => ⟨2, fun _ => 1, 2⟩) (fun _ => id) (fun _ => -2) (fun _ => 1) 1

example (x : Fin 2 → Bool) : xorCircuit.eval interpretation x 0 = (x 0 ^^ x 1) := by
  rw [xorCircuit, eval_depthTwoInputs]
  simp only [interpretation, Fin.sum_univ_two, Fin.sum_univ_one, id_eq]
  cases x 0 <;> cases x 1 <;> norm_num

example : xorCircuit.size = 2 := size_depthTwoInputs ..

example : xorCircuit.depth ≤ 2 := depth_depthTwoInputs_le ..

-- A bottom gate reading every input once with its own weights has those weights as aggregated
-- weights; repeated reads add up.
example (w : Fin 3 → ℝ) : argWeight ⟨3, w, 0⟩ id = w := argWeight_id w 0

example : argWeight (n := 1) ⟨2, ![1, 2], 0⟩ (fun _ => 0) 0 = 3 := by
  simp only [argWeight, lineWeight, inputLine]
  change ∑ a : Fin 2, ![(1 : ℝ), 2] a = 3
  simp [Fin.sum_univ_two]
  norm_num

-- A gate that reads every address block through its sum with coefficient one is sign-coherent
-- for Andreev's block layout; so is its negation, and so is any multiple.
example (b m : ℕ) (S : Finset (Fin b)) :
    IsSignCoherent (Boolean.andreevBlockVar b m) fun i =>
      if ∃ j ∈ S, ∃ t, Boolean.andreevBlockVar b m j t = i then (1 : ℝ) else 0 := by
  refine IsSignCoherent.of_mem_zero_one fun j t => ?_
  split_ifs <;> simp

example (b m : ℕ) (w : Fin (2 ^ b + b * m) → ℝ)
    (hw : IsSignCoherent (Boolean.andreevBlockVar b m) w) (c : ℝ) :
    IsSignCoherent (Boolean.andreevBlockVar b m) (-(c • w)) :=
  (hw.smul c).neg

-- The bottom gate of `xorCircuit` has weights `1, 1`, so every gate read by its output gate has
-- sign-coherent input weights for the single block `{0, 1}`.
example {top : Fin xorCircuit.size} (htop : xorCircuit.outputs 0 = .gate top)
    {k : Fin xorCircuit.size} (hk : k ∈ gateSupport xorCircuit.program top) :
    IsSignCoherent (n := 2) (b := 1) (m := 2) (fun _ t => t) (inputWeight xorCircuit.program k) :=
  isSignCoherent_inputWeight_depthTwoInputs _ _ _ _ _
    (fun _ => by rw [argWeight_id]; exact IsSignCoherent.of_nonneg fun _ _ => zero_le_one)
    htop hk

-- Mixed signs inside one block are not sign-coherent.
example : ¬ IsSignCoherent (n := 2) (b := 1) (m := 2) (fun _ t => t) ![1, -1] := by
  intro h
  rcases h 0 with h | h
  · have := h 1; norm_num at this
  · have := h 0; norm_num at this

end WeightedThresholdDepthTwoInputsTests
