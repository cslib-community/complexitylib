/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

import Complexity.Computability.Circuit.Boolean.WeightedThreshold
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Andreev
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.AndreevApproxMajority
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.AndreevAverage
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.AndreevLowerBound
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.RandomRestriction
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.ThresholdCounting
import Complexity.Computability.Circuit.Boolean.Threshold.Parity
import Complexity.Foundations.Combinatorics.ApproximateMajority
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
Weighted threshold clients: repeated coefficients, nullary gates, native circuit translation,
and the exact boundary for output determinacy.
-/

open Cslib Cslib.Circuits

namespace WeightedThresholdTests

open Boolean.WeightedThreshold Finset

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

-- Exact depth-two weighted threshold circuit for Andreev's function at `b = 2, m = 2` (`8` bits):
-- 48 bottom gates, 49 total gates, depth at most 2, and mixed truth-table evaluation where
-- changing block parities changes the selected truth-table entry.
example :
    (andreevCircuit 2 2).Computes interpretation (single (Boolean.andreev 2 2)) ∧
    (andreevCircuit 2 2).size = 49 ∧
    (andreevCircuit 2 2).depth ≤ 2 ∧
    (andreevCircuit 2 2).wireCount ≤ 432 ∧
    (andreevCircuit 2 2).eval interpretation
      (fun i => decide (i = 1 ∨ i = 2 ∨ i = 4)) 0 = true ∧
    (andreevCircuit 2 2).eval interpretation
      (fun i => decide (i = 1 ∨ i = 2 ∨ i = 4 ∨ i = 5)) 0 = false := by
  refine ⟨computes_andreevCircuit 2 2, size_andreevCircuit_two_two, depth_andreevCircuit_le 2 2,
    wireCount_andreevCircuit_two_two_le, ?_, ?_⟩
  · rw [eval_andreevCircuit_eq_evalInt]
    exact andreevCircuitEvalInt_two_two_mixed.1
  · rw [eval_andreevCircuit_eq_evalInt]
    exact andreevCircuitEvalInt_two_two_mixed.2

-- Windowed depth-two weighted threshold circuit and subcube correlation at `b = 2, m = 2, r = 1`:
-- `andreevWindowedCircuit 2 2 1 4` uses `33` gates (`≤ 288` active wires) at depth at most `2`
-- and matches `Boolean.andreev 2 2` on the mixed concrete truth-table inputs; at `B = 5` (`41`
-- gates, `≤ 360` active wires), every input lies in-window (`|X_S(w)| ≤ 4` and
-- `|t_S(w) - (#S * 2) / 2| ≤ 1`), so `andreevWindowedCircuit 2 2 1 5` agrees with
-- `andreevSubcubeEval 2 2 1` everywhere and matches `Boolean.andreev 2 2` on `192` of the `256`
-- inputs (`2 * 192 = 384 = 256 + 128`); and at `B = 9, t = 17 / 6` (`3 * t + 1 / 2 = 9 ≤ B`), the
-- analytic Hoeffding correlation theorem gives a lower bound strictly exceeding `1 / 2`.
example :
    (andreevWindowedCircuit 2 2 1 4).size = 33 ∧
    (andreevWindowedCircuit 2 2 1 4).depth ≤ 2 ∧
    (andreevWindowedCircuit 2 2 1 4).wireCount ≤ 288 ∧
    (andreevWindowedCircuit 2 2 1 4).eval interpretation
      (fun i => decide (i = 1 ∨ i = 4)) 0 = true ∧
    (andreevWindowedCircuit 2 2 1 4).eval interpretation
      (fun i => decide (i = 1 ∨ i = 4 ∨ i = 5)) 0 = false ∧
    (andreevWindowedCircuit 2 2 1 5).size = 41 ∧
    2 * #{w : BitString (2 ^ 2 + 2 * 2) |
      (andreevWindowedCircuit 2 2 1 5).eval interpretation w 0 =
        Boolean.andreev 2 2 w} = 384 ∧
    (2 ^ (2 ^ 2 + 2 * 2) : ℝ) * (1 / 2 + 1 / (2 * Real.sqrt (2 * 2 ^ (2 - 1)))) -
      2 ^ 1 * (2 * 2 ^ (2 ^ 2 + 2 * 2)) *
        (Real.exp (-(2 * (17 / 6 : ℝ) ^ 2 / (2 ^ 2 : ℝ))) +
          Real.exp (-(2 * (17 / 6 : ℝ) ^ 2 / (2 * 2 : ℝ)))) ≤
      (#{w : BitString (2 ^ 2 + 2 * 2) |
        (andreevWindowedCircuit 2 2 1 9).eval interpretation w 0 =
          Boolean.andreev 2 2 w} : ℝ) := by
  have hin (w : BitString (2 ^ 2 + 2 * 2)) : andreevInWindow 2 2 1 5 w := by
    intro S hS σ
    have hcard : #S ≤ 1 :=
      (Finset.card_le_card ((mem_andreevPrefixSubsets S).mp hS)).trans
        (by rw [card_andreevPrefixCoords (by decide : 1 ≤ 2)])
    have hX := andreevTableScore_bounds 2 2 S w
    have ht := andreevBlockSum_bounds 2 2 S w
    cases σ <;>
      simp only [andreevWindowLower, andreevWindowCenter, andreevLinearForm, ↓reduceIte,
        Bool.false_eq_true, Nat.cast_mul, Nat.cast_ofNat] <;>
      omega
  refine ⟨by rw [size_andreevWindowedCircuit (by decide)]; rfl,
    depth_andreevWindowedCircuit_le 2 2 1 4,
    (wireCount_andreevWindowedCircuit_le (by decide) 2 4).trans (by decide),
    by rw [eval_andreevWindowedCircuit_eq_evalInt]; decide,
    by rw [eval_andreevWindowedCircuit_eq_evalInt]; decide,
    by rw [size_andreevWindowedCircuit (by decide)]; rfl,
    by
      simp_rw [fun w => eval_andreevWindowedCircuit_eq_subcubeEval_of_inWindow (hin w) 0]
      exact (two_mul_card_andreevSubcubeEval_eq_andreev (by decide) 2).trans (by decide),
    card_eval_andreevWindowedCircuit_eq_andreev_ge_sqrt (by decide) 2 9 0
      (by norm_num) (by norm_num)⟩

-- Erdős–Littlewood–Offord anti-concentration and Kane–Williams block-partition gate and wire
-- random restriction lemmas instantiated on the Andreev block-variable partition
-- `Boolean.andreevBlockVar 2 2` and a depth-one gate.
example :
    #{w : Fin 4 → Bool |
      (2 : ℝ) ≤ ∑ i : Fin 4, (1 : ℝ) * (w i).toNat ∧
        (∑ i : Fin 4, (1 : ℝ) * (w i).toNat) < 2 + 1} ≤ (4 : ℕ).choose (4 / 2) ∧
    (∀ x : Fin 2 → Bool,
      ((Boolean.Threshold.parityCircuit 2).mapOp ofThreshold).program.eval interpretation x
        ⟨0, by decide⟩ =
        ltfEval
          (inputWeight ((Boolean.Threshold.parityCircuit 2).mapOp ofThreshold).program
            ⟨0, by decide⟩)
          (((Boolean.Threshold.parityCircuit 2).mapOp ofThreshold).program.lines
            ⟨0, by decide⟩).op.threshold
          x) ∧
    (∑ σ : Fin 2 → Fin 2,
      (#{w : BitString (2 ^ 2 + 2 * 2) |
        ¬ ForcedToConst
          (ltfEval (inputWeight (andreevCircuit 2 2).program ⟨0, by decide⟩)
            ((andreevCircuit 2 2).program.lines ⟨0, by decide⟩).op.threshold)
          (Cslib.Combinatorics.LittlewoodOfford.blockLiveSet (Boolean.andreevBlockVar 2 2) σ)
          w} : ℝ)) ≤
      (Fintype.card (Fin 2 → Fin 2) : ℝ) * (2 : ℝ) ^ Fintype.card (Fin (2 ^ 2 + 2 * 2)) *
        (4 * (1 / (Fintype.card (Fin 2) : ℝ)) *
          Real.sqrt #(inputSupport (andreevCircuit 2 2).program ⟨0, by decide⟩)) ∧
    (∑ σ : Fin 2 → Fin 2,
      (#{w : BitString (2 ^ 2 + 2 * 2) |
        ¬ ForcedToAtMostOne
          (ltfEval (inputWeight (andreevCircuit 2 2).program ⟨0, by decide⟩)
            ((andreevCircuit 2 2).program.lines ⟨0, by decide⟩).op.threshold)
          (Cslib.Combinatorics.LittlewoodOfford.blockLiveSet (Boolean.andreevBlockVar 2 2) σ)
          w} : ℝ)) ≤
      (Fintype.card (Fin 2 → Fin 2) : ℝ) * (2 : ℝ) ^ Fintype.card (Fin (2 ^ 2 + 2 * 2)) *
        (4 * (#(inputSupport (andreevCircuit 2 2).program ⟨0, by decide⟩) : ℝ) *
          (1 / (Fintype.card (Fin 2) : ℝ)) *
          Real.sqrt (1 / (Fintype.card (Fin 2) : ℝ))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using
      Cslib.Combinatorics.LittlewoodOfford.card_filter_sum_bool_le_choose_of_forall_le_abs
        (fun _ : Fin 4 => (1 : ℝ)) (P := fun s => (2 : ℝ) ≤ s ∧ s < 2 + 1) (δ := 1)
        (fun _ => by norm_num) (fun x y hx hy => by rw [abs_lt]; constructor <;> linarith)
  · intro x
    exact eval_eq_ltfEval_inputWeight_of_depths_le_one
      ((Boolean.Threshold.parityCircuit 2).mapOp ofThreshold).program x (by decide)
  · simpa [ltfSupport_inputWeight_eq_inputSupport] using
      sum_card_not_forcedToConst_blockLiveSet_le (Boolean.andreevBlockVar 2 2)
        (andreevBlockVar_joint_injective 2 2)
        (inputWeight (andreevCircuit 2 2).program ⟨0, by decide⟩)
        ((andreevCircuit 2 2).program.lines ⟨0, by decide⟩).op.threshold
  · simpa [ltfSupport_inputWeight_eq_inputSupport] using
      sum_card_not_forcedToAtMostOne_blockLiveSet_le (Boolean.andreevBlockVar 2 2)
        (andreevBlockVar_joint_injective 2 2)
        (inputWeight (andreevCircuit 2 2).program ⟨0, by decide⟩)
        ((andreevCircuit 2 2).program.lines ⟨0, by decide⟩).op.threshold

-- OR is constant after fixing the other input true, a nonconstant literal when it is false,
-- and genuinely depends on two inputs when both are live.
private theorem ltfEval_or (w : Fin 2 → Bool) :
    ltfEval (fun _ : Fin 2 => (1 : ℝ)) 1 w = (w 0 || w 1) := by
  cases h₀ : w 0 <;> cases h₁ : w 1 <;>
    norm_num [ltfEval, Fin.sum_univ_two, h₀, h₁]

example : ForcedToConst (ltfEval (fun _ : Fin 2 => (1 : ℝ)) 1) {0} (fun _ => true) := by
  simp only [funext ltfEval_or, ForcedToConst, restrictUpdate]
  decide

example : ¬ ForcedToConst (ltfEval (fun _ : Fin 2 => (1 : ℝ)) 1) {0}
    (fun _ => false) := by
  simp only [funext ltfEval_or, ForcedToConst, restrictUpdate]
  decide

example : ForcedToAtMostOne (ltfEval (fun _ : Fin 2 => (1 : ℝ)) 1) {0}
    (fun _ => false) := by
  simp only [funext ltfEval_or, ForcedToAtMostOne, ForcedToConst, restrictUpdate]
  decide

example : ¬ ForcedToAtMostOne (ltfEval (fun _ : Fin 2 => (1 : ℝ)) 1) univ
    (fun _ => false) := by
  simp only [funext ltfEval_or, ForcedToAtMostOne, ForcedToConst, restrictUpdate]
  decide

-- The live second coordinate has zero weight: it cannot prevent constancy. With both live,
-- the first coordinate remains a nonconstant literal, despite the extra zero-weight input.
private theorem ltfEval_zero_weight (w : Fin 2 → Bool) :
    ltfEval (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) 1 w = w 0 := by
  cases h : w 0 <;> norm_num [ltfEval, Fin.sum_univ_two, h]

example : ForcedToConst (ltfEval (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) 1)
    {1} (fun _ => false) := by
  simp only [funext ltfEval_zero_weight, ForcedToConst, restrictUpdate]
  decide

example : ForcedToAtMostOne (ltfEval (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) 1)
    univ (fun _ => false) ∧
    ¬ ForcedToConst (ltfEval (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) 1)
      univ (fun _ => false) := by
  simp only [funext ltfEval_zero_weight, ForcedToAtMostOne, ForcedToConst, restrictUpdate]
  decide

-- Chow-parameter LTF counting, depth-two subcube collapse, and the simultaneous-in-`q`
-- depth-two gate and wire correlation and lower bounds for Andreev's function (`b = 2, m = 2`).
open Classical in
example (σ : Fin 2 → Fin 2) (w : BitString (2 ^ 2 + 2 * 2)) (u : BitString 2) :
    #(univ.filter (IsLTF (κ := Fin 2))) ≤ 125 ∧
    #(univ.filter (IsDepthTwoWithGates (κ := Fin 2) 1)) ≤ 78125 ∧
    Boolean.andreev 2 2 (embedUpdate (andreevLiveVar 2 2 σ) w u) =
      w (Boolean.andreevTableIndex 2 2
        (BitString.equivFin 2 (u + andreevResidualParities 2 2 σ w))) ∧
    IsDepthTwoWithGates
      (circuitUnforcedConstCount (andreevCircuit 2 2) 0
        (Cslib.Combinatorics.LittlewoodOfford.blockLiveSet (Boolean.andreevBlockVar 2 2) σ) w)
      (fun u' : BitString 2 =>
        (andreevCircuit 2 2).eval interpretation (embedUpdate (andreevLiveVar 2 2 σ) w u') 0) ∧
    IsDepthTwoWithGates
      (circuitUnforcedAtMostOneCount (andreevCircuit 2 2) 0
        (Cslib.Combinatorics.LittlewoodOfford.blockLiveSet (Boolean.andreevBlockVar 2 2) σ) w)
      (fun u' : BitString 2 =>
        (andreevCircuit 2 2).eval interpretation (embedUpdate (andreevLiveVar 2 2 σ) w u') 0) := by
  refine ⟨(card_isLTF_le (κ := Fin 2)).trans (by decide : _ ≤ 125),
    (card_isDepthTwoWithGates_le (κ := Fin 2) 1).trans (by decide : _ ≤ 78125),
    andreev_embedUpdate_andreevLiveVar 2 2 σ w u, ?_, ?_⟩
  · rw [← univ_image_andreevLiveVar_eq_blockLiveSet]
    exact isDepthTwoWithGates_eval_embedUpdate_const (andreevCircuit 2 2)
      (depth_andreevCircuit_le 2 2) 0 (andreevLiveVar_injective 2 2 σ) w
  · rw [← univ_image_andreevLiveVar_eq_blockLiveSet]
    exact isDepthTwoWithGates_eval_embedUpdate (andreevCircuit 2 2)
      (depth_andreevCircuit_le 2 2) 0 (andreevLiveVar_injective 2 2 σ) w

/-- A fixed weight vector has at most five threshold behaviours on two bits. -/
example (β : Fin 2 → ℝ) : #{g : BitString 2 → Bool | IsThresholdShift β g} ≤ 5 := by
  simpa using card_isThresholdShift_le β

/-- The canonical simultaneous tail is uniformly small, even for the empty weight family. -/
example : andreevWeightTail 14 1 (andreevWeightScale 14 1)
    (((14 : ℕ) + 2 : ℝ) * Real.sqrt ((2 : ℝ) ^ 14)) ≤ (1 / 2 : ℝ) ^ 20 :=
  andreevWeightTail_scale_le 14 (by decide)

/-- A strict-majority vote of an odd number `t` of depth-two circuits computing Andreev's function
has strictly more than `t / 2` correct members, so the top fan-in bound applies. -/
example {b m t s : ℕ} (hm : 0 < m) (hmN : m ≤ 2 ^ b) (ht : Odd t)
    (hb : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ 1 / (2 * t))
    (C : Fin t → Circuit signature (2 ^ b + b * m) 1) (hd : ∀ i, (C i).depth ≤ 2)
    (hs : ∀ i, (C i).size ≤ s)
    (hcomp : ∀ w,
      strictMajority t (fun i => (C i).eval interpretation w 0) = Boolean.andreev b m w) :
    (m : ℝ) * (2 : ℝ) ^ b ≤
      576 * ((b : ℝ) + 2) * (t : ℝ) ^ 2 * (s : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) :=
  size_ge_of_majorityVote_andreev_of_le_two_pow hm hmN hb C hd hs fun w =>
    lt_two_mul_card_filter_eq_of_strictMajority_eq ht (hcomp w)

-- With an even number of votes, a tie outputs `false`, so a correct strict-majority vote need not
-- have a strict majority of correct votes.
example : strictMajority 2 ![true, false] = false ∧
    ¬ 2 < 2 * #{i | ![true, false] i = false} := by decide

end WeightedThresholdTests
