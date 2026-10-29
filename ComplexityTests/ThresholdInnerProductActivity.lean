/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.WeightedThreshold.InnerProduct
import Mathlib.Algebra.BigOperators.Fin

/-! Concrete and boundary clients for the inner-product pattern and activity inequalities. -/

open Cslib Cslib.Circuits Cslib.BitString Finset Matrix
open Cslib.Circuits.Boolean.WeightedThreshold

namespace ThresholdInnerProductActivity

-- With no coordinates or gates, the constant false readout genuinely computes inner product.
example :
    1 ≤ (attainableTranscripts (Program.empty : Program signature 0 0)).card ^ 2 ∧
      1 ≤ (∑ j ∈ range (gateActivity (Program.empty : Program signature 0 0) + 1),
        Nat.choose 0 j) ^ 2 :=
  ⟨two_pow_le_card_attainableTranscripts_sq_of_dotProduct Program.empty
      (finSumFinEquiv : Fin 0 ⊕ Fin 0 ≃ Fin 0).symm (fun _ => false)
      (fun _ _ => by simp [dotProduct, Bool.zero_eq_false]),
    two_pow_le_sum_choose_gateActivity_sq_of_dotProduct Program.empty
      (finSumFinEquiv : Fin 0 ⊕ Fin 0 ≃ Fin 0).symm (fun _ => false)
      (fun _ _ => by simp [dotProduct, Bool.zero_eq_false])⟩

-- At positive dimension, zero input-reading activity cannot compute inner product.
example {n g : ℕ} (p : Program signature n g) (split : Fin n ≃ Fin 1 ⊕ Fin 1)
    (readout : (Fin g → Bool) → Bool) (he : inputActivity p = 0) :
    ¬ ∀ x y, readout (p.eval interpretation (inputOfSplit split x y)) = x ⬝ᵥ y := by
  intro h
  have := two_pow_le_sum_choose_sq_of_dotProduct p split readout h
  simp [he] at this

private abbrev andCircuit : Circuit signature 2 1 :=
  ⟨Program.empty.gate ⟨⟨2, fun _ => 1, 2⟩, Wire.input⟩, fun _ => .gate 0⟩

private theorem andCircuit_computes (x y : Fin 1 → Bool) :
    andCircuit.eval interpretation
      (inputOfSplit (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm x y) 0 = x ⬝ᵥ y := by
  change (Program.empty.gate _).eval interpretation _ (Fin.last 0) = _
  rw [Program.eval_gate_last]
  cases hx : x 0 <;> cases hy : y 0 <;>
    dsimp only [Line.eval, interpretation, Function.comp_apply, Wire.elim] <;>
    norm_num [Fin.sum_univ_two, inputOfSplit, finSumFinEquiv, Fin.addCases,
      dotProduct, Bool.mul_eq_and, hx, hy]

-- The single gate at threshold two supplies a nonconstant circuit computing one-bit inner product,
-- and the total-activity bound forces `0 < gateActivity andCircuit.program`.
example :
    2 ≤ (∑ j ∈ range (inputActivity andCircuit.program + 1),
        (inputGates andCircuit.program).card.choose j) ^ 2 ∧
      0 < gateActivity andCircuit.program := by
  refine ⟨two_pow_le_sum_choose_sq_of_circuit_dotProduct andCircuit
    (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm ⟨0, rfl⟩ andCircuit_computes, ?_⟩
  by_contra h
  have h0 : gateActivity andCircuit.program = 0 := by omega
  have hle := two_pow_le_sum_choose_gateActivity_sq_of_circuit_dotProduct andCircuit
    (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm ⟨0, rfl⟩ andCircuit_computes
  simp [h0] at hle

-- The pattern theorem also implies `andCircuit.program` has at least two attainable transcripts.
example : 2 ≤ (attainableTranscripts andCircuit.program).card := by
  have h : 2 ≤ (attainableTranscripts andCircuit.program).card ^ 2 := by
    apply two_pow_le_card_attainableTranscripts_sq_of_dotProduct andCircuit.program
      (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm (fun z => z 0)
    intro x y
    simpa only [andCircuit, Circuit.eval, Function.comp_apply, Program.trace_gateWire,
      Program.gateFunction_apply] using andCircuit_computes x y
  nlinarith

-- Appending an unused active gate preserves the output but increases the total gate count.
private abbrev paddedAndCircuit : Circuit signature 2 1 :=
  ⟨andCircuit.program.gate ⟨⟨0, Fin.elim0, 0⟩, Fin.elim0⟩, fun _ => .gate 0⟩

example : 2 ≤ (∑ j ∈ range (gateActivity paddedAndCircuit.program + 1), Nat.choose 2 j) ^ 2 := by
  apply two_pow_le_sum_choose_gateActivity_sq_of_circuit_dotProduct paddedAndCircuit
    (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm ⟨0, rfl⟩
  intro x y
  change (andCircuit.program.gate _).eval interpretation _ (Fin.castSucc 0) = _
  rw [Program.eval_gate_castSucc]
  exact andCircuit_computes x y

-- Shifted-baseline inner-product bounds on `andCircuit.program` at positive dimension (`m = 1`).
example (v : inputGates andCircuit.program → Bool) :
    2 ≤ (∑ j ∈ range (inputActivityFrom andCircuit.program v + 1),
      (inputGates andCircuit.program).card.choose j) ^ 2 := by
  apply two_pow_le_sum_choose_inputActivityFrom_sq_of_dotProduct andCircuit.program
    (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm v (fun z => z 0)
  intro x y
  simpa only [andCircuit, Circuit.eval, Function.comp_apply, Program.trace_gateWire,
    Program.gateFunction_apply] using andCircuit_computes x y

example (v : Fin 1 → Bool) :
    2 ≤ (∑ j ∈ range (gateActivityFrom andCircuit.program v + 1), Nat.choose 1 j) ^ 2 := by
  apply two_pow_le_sum_choose_gateActivityFrom_sq_of_dotProduct andCircuit.program
    (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm v (fun z => z 0)
  intro x y
  simpa only [andCircuit, Circuit.eval, Function.comp_apply, Program.trace_gateWire,
    Program.gateFunction_apply] using andCircuit_computes x y

end ThresholdInnerProductActivity
