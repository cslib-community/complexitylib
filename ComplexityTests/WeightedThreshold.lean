/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.WeightedThreshold
import Complexity.Computability.Circuit.Boolean.Threshold.Parity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
Weighted threshold clients: repeated coefficients, nullary gates, native circuit translation,
and the exact boundary for output determinacy.
-/

open Cslib Cslib.Circuits

namespace WeightedThresholdTests

open Boolean.WeightedThreshold

-- Nullary gates use the empty sum (equality is accepted), and a negative coefficient implements
-- negation without adding a separate operation.
example (x₀ : Fin 0 → Bool) (x₁ : Fin 1 → Bool) :
    interpretation ⟨0, Fin.elim0, 0⟩ x₀ = true ∧
    interpretation ⟨0, Fin.elim0, 1⟩ x₀ = false ∧
    interpretation ⟨1, fun _ => 0, 0⟩ x₁ = true ∧
    interpretation ⟨1, fun _ => -1, 0⟩ x₁ = !x₁ 0 :=
  ⟨by norm_num [interpretation],
    by norm_num [interpretation],
    by norm_num [interpretation],
    by cases hx : x₁ 0 <;> norm_num [interpretation, hx]⟩

private def cancelLine : Line signature 1 0 :=
  ⟨⟨2, ![3, -3], 0⟩, fun _ => .input 0⟩

private def cancelled : Program signature 1 1 :=
  Program.empty.gate cancelLine

private theorem cancelled_inputWeight (gate input : Fin 1) :
    inputWeight cancelled gate input = 0 := by
  fin_cases gate; fin_cases input
  change lineWeight ((Program.empty.gate cancelLine).lines (Fin.last 0)) (.input 0) = 0
  rw [Program.lines_gate_last]
  dsimp only [lineWeight, Line.mapWires, cancelLine]
  norm_num [Fin.sum_univ_two]

-- Equal coefficients on repeated wires add, rather than being deduplicated.
private def repeated : Line signature 1 0 :=
  ⟨⟨2, ![1, 2], 3⟩, fun _ => .input 0⟩

-- Opposite coefficients on repeated occurrences of one wire cancel before counting inputs, while
-- equal coefficients add.
example (x : Fin 1 → Bool) :
    lineWeight cancelLine (.input 0) = 0 ∧
    inputGates cancelled = ∅ ∧
    cancelled.eval interpretation x 0 = true ∧
    lineWeight repeated (.input 0) = 3 ∧
    repeated.eval interpretation x Fin.elim0 = x 0 := by
  refine ⟨by dsimp only [lineWeight, cancelLine]; norm_num [Fin.sum_univ_two],
    by ext gate; simp [cancelled_inputWeight], ?_,
    by dsimp only [lineWeight, repeated]; norm_num [Fin.sum_univ_two],
    by
      cases hx : x 0 <;>
        dsimp only [repeated, Line.eval, interpretation, Function.comp_apply, Wire.elim] <;>
        norm_num [Fin.sum_univ_two, hx]⟩
  change (Program.empty.gate cancelLine).eval interpretation x (Fin.last 0) = true
  rw [Program.eval_gate_last]
  dsimp only [Line.eval, interpretation, cancelLine, Function.comp_apply, Wire.elim]
  norm_num [Fin.sum_univ_two]

private def readInput : Program signature 2 1 :=
  Program.empty.gate ⟨⟨1, fun _ => 1, 1⟩, fun _ => .input 0⟩

private def negatePrior : Program signature 2 2 :=
  readInput.gate ⟨⟨1, fun _ => -1, 0⟩, fun _ => .gate 0⟩

-- This gate is semantically constant, but its direct input coefficient is nonzero.
-- Cancellation with an earlier gate's value does not erase direct input reading.
private def mixed : Program signature 2 3 :=
  negatePrior.gate ⟨⟨2, ![1, -1], 0⟩, ![.input 0, .gate 0]⟩

example : inputGates mixed = {0, 2} := by
  ext gate
  simp only [mem_inputGates]
  fin_cases gate
  · change (∃ i, lineWeight (⟨⟨1, fun _ => 1, 1⟩, fun _ => .input 0⟩ :
        Line signature 2 3) (.input i) ≠ 0) ↔ _
    dsimp only [lineWeight]
    norm_num [Fin.exists_fin_succ]
  · change (∃ i, lineWeight (⟨⟨1, fun _ => -1, 0⟩, fun _ => .gate 0⟩ :
        Line signature 2 3) (.input i) ≠ 0) ↔ _
    dsimp only [lineWeight]
    norm_num
  · change (∃ i, lineWeight ((⟨⟨2, ![1, -1], 0⟩, ![.input 0, .gate 0]⟩ :
        Line signature 2 2).mapWires Wire.Renaming.castSucc) (.input i) ≠ 0) ↔ _
    dsimp only [lineWeight, Line.mapWires]
    norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.exists_fin_succ]

example (x : Fin 2 → Bool) : mixed.eval interpretation x 2 = true := by
  have hread : negatePrior.eval interpretation x 0 = x 0 := by
    change readInput.eval interpretation x (Fin.last 0) = x 0
    rw [readInput, Program.eval_gate_last]
    cases hx : x 0 <;>
      dsimp only [Line.eval, interpretation, Function.comp_apply, Wire.elim] <;>
      norm_num [hx]
  change (negatePrior.gate _).eval interpretation x (Fin.last 2) = true
  rw [Program.eval_gate_last]
  dsimp only [Line.eval, interpretation, Function.comp_apply]
  simp [Fin.sum_univ_two, hread]

-- Selected gate outputs may share a gate and omit other gates.
private def gateOutputs : Circuit signature 2 2 :=
  ⟨mixed, fun _ => .gate 1⟩

-- Gate-weight acyclicity and transcript determinacy use only the transcript hypothesis.
example {x y : Fin 2 → Bool} (h : transcript mixed x = transcript mixed y) :
    gateWeight mixed 1 1 = 0 ∧
    gateWeight mixed 1 2 = 0 ∧
    gateOutputs.eval interpretation x = gateOutputs.eval interpretation y :=
  ⟨gateWeight_eq_zero_of_le mixed 1 1 le_rfl,
    gateWeight_eq_zero_of_le mixed 1 2 (by decide),
    circuit_eval_eq_of_transcript_eq gateOutputs (fun _ => ⟨(1 : Fin 3), rfl⟩) h⟩

-- The generic translation API is available independently of the transcript example.
example (n : ℕ) (z : Fin n → Bool) :
    ((Boolean.Threshold.parityCircuit n).mapOp ofThreshold).size =
      (Boolean.Threshold.parityCircuit n).size ∧
    ((Boolean.Threshold.parityCircuit n).mapOp ofThreshold).eval interpretation z =
      (Boolean.Threshold.parityCircuit n).eval Boolean.Threshold.interpretation z :=
  ⟨Circuit.size_mapOp _, Circuit.eval_mapOp _ _⟩

-- The fixed two-bit circuit has four gates and computes true on an odd-parity input.
-- Evaluate the Boolean source, then transfer through the interpretation-preserving translation.
example :
    ((Boolean.Threshold.parityCircuit 2).mapOp ofThreshold).size = 4 ∧
    (Boolean.Threshold.parityCircuit 2).size = 4 ∧
    ((Boolean.Threshold.parityCircuit 2).mapOp ofThreshold).eval interpretation
      ![true, false] 0 = true ∧
    (Boolean.Threshold.parityCircuit 2).eval Boolean.Threshold.interpretation
      ![true, false] 0 = true := by
  refine ⟨by decide, by decide, ?_, by decide⟩
  calc
    _ = (Boolean.Threshold.parityCircuit 2).eval Boolean.Threshold.interpretation
        ![true, false] 0 := congrFun (Circuit.eval_mapOp _ _) 0
    _ = true := by decide

-- A free original-input output is a genuine counterexample without the gate-output premise.
example : ∃ x y : Fin 1 → Bool,
    transcript (Circuit.id signature 1).program x =
      transcript (Circuit.id signature 1).program y ∧
    (Circuit.id signature 1).eval interpretation x ≠
      (Circuit.id signature 1).eval interpretation y := by
  refine ⟨fun _ => false, fun _ => true, ?_, ?_⟩
  · funext gate
    exact gate.val.elim0
  · intro h
    exact Bool.false_ne_true (congrFun h 0)

end WeightedThresholdTests
