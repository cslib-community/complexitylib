/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.WeightedThreshold.TranscriptTree
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-! Native scalar-stage clients: composition, sparse padding, ties and repeated wires. -/

open Cslib Cslib.Circuits Cslib.Circuits.Boolean.WeightedThreshold

private theorem empty_readers (n : ℕ) :
    (inputGates (Program.empty : Program signature n 0)).card = 0 := by
  have h : inputGates (Program.empty : Program signature n 0) = ∅ :=
    Finset.ext (fun j => Fin.elim0 j)
  exact congrArg Finset.card h

private def scalarRoot : Program signature 2 2 :=
  ScalarStage.append Program.empty (Fin.elim0 : Fin 0 → Fin 0)
    (fun (_ : Fin 1) (_ : Fin 0) => false) (fun _ => 1) (fun _ => 2) 3

private theorem scalarRoot_eval (x : Fin 2 → Bool) :
    scalarRoot.eval interpretation x 1 = (x 0 && x 1) := by
  change scalarRoot.eval interpretation x (Fin.last 1) = _
  rw [scalarRoot, ScalarStage.eval_append_last]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    norm_num [funext_iff, h0, h1]

private theorem scalarRoot_readers : (inputGates scalarRoot).card = 1 := by
  rw [scalarRoot, ScalarStage.card_inputGates_append, empty_readers]
  norm_num [funext_iff]

-- The root's true branch has terminated. Only its false prefix gets a second-stage flag.
private def scalarChild : Program signature 2 4 :=
  ScalarStage.append scalarRoot (fun _ : Fin 1 => 1)
    (fun (_ : Fin 1) (_ : Fin 1) => false) (fun _ => 1) (fun _ => 1) 3

private theorem scalarChild_eval (x : Fin 2 → Bool) :
    scalarChild.eval interpretation x 3 = (x 0 ^^ x 1) := by
  refine (ScalarStage.eval_append_last scalarRoot (fun _ : Fin 1 => (1 : Fin 2))
    (fun (_ : Fin 1) (_ : Fin 1) => false) (fun _ : Fin 2 => (1 : ℝ))
    (fun _ : Fin 1 => (1 : ℝ)) 3 x).trans ?_
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    norm_num [Fin.sum_univ_two, funext_iff, scalarRoot_eval, h0, h1]

private theorem scalarChild_root_eval (x : Fin 2 → Bool) :
    scalarChild.eval interpretation x 1 = scalarRoot.eval interpretation x 1 := by
  exact ScalarStage.eval_append_castSucc scalarRoot (fun _ : Fin 1 => 1)
    (fun (_ : Fin 1) (_ : Fin 1) => false) (fun _ => 1) (fun _ => 1) 3 x 1

private theorem scalarChild_readers : (inputGates scalarChild).card = 2 := by
  rw [scalarChild, ScalarStage.card_inputGates_append, scalarRoot_readers]
  norm_num [funext_iff]

-- The two native input-reading queries never fire together.
example (x : Fin 2 → Bool) :
    (scalarChild.eval interpretation x 1).toNat +
      (scalarChild.eval interpretation x 3).toNat ≤ 1 := by
  rw [scalarChild_root_eval, scalarRoot_eval, scalarChild_eval]
  cases x 0 <;> cases x 1 <;> decide

-- Attach a native input-free OR readout. This is a Circuit, not a free readout function.
private def compiledOrProgram : Program signature 2 5 :=
  scalarChild.gate (ScalarStage.queryLine (fun _ => 0)
    (fun j : Fin 2 => if j = 0 then 1 else 3) (fun _ => 1) 1)

private def compiledOrCircuit : Circuit signature 2 1 :=
  ⟨compiledOrProgram, fun _ => .gate 4⟩

example : compiledOrCircuit.size = 5 := rfl

example (x : Fin 2 → Bool) :
    compiledOrCircuit.eval interpretation x 0 = (x 0 || x 1) := by
  change compiledOrProgram.eval interpretation x (Fin.last 4) = _
  rw [compiledOrProgram, Program.eval_gate_last, ScalarStage.queryLine_eval]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    norm_num [Fin.sum_univ_two, scalarChild_root_eval, scalarRoot_eval, scalarChild_eval, h0, h1]

-- The same stage implements accepting-leaf readout, without another constructor.
-- The accepting paths [false,true] and [true] become [false,true] and [true,false].
private def acceptingReadout : Program signature 2 7 :=
  ScalarStage.append scalarChild (fun j : Fin 2 => if j = 0 then 1 else 3)
    (fun a j : Fin 2 => decide (a ≠ j)) (fun _ => 0) (fun _ => 0) 1

example : (inputGates acceptingReadout).card = 2 := by
  have hz : (fun _ : Fin 2 => (0 : ℝ)) = 0 := funext (fun _ => rfl)
  rw [acceptingReadout, ScalarStage.card_inputGates_append, scalarChild_readers, ite_eq_left hz]

example (x : Fin 2 → Bool) :
    acceptingReadout.eval interpretation x 6 = (x 0 || x 1) := by
  change acceptingReadout.eval interpretation x (Fin.last 6) = _
  rw [acceptingReadout, ScalarStage.eval_append_readout]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    norm_num [funext_iff, Fin.forall_fin_two, Fin.exists_fin_two,
      scalarChild_root_eval, scalarRoot_eval, scalarChild_eval, h0, h1]

-- An empty accepting bank rejects, including for a zero-dimensional input.
example : (ScalarStage.append (Program.empty : Program signature 0 0)
    (Fin.elim0 : Fin 0 → Fin 0) (Fin.elim0 : Fin 0 → Fin 0 → Bool)
      (fun _ => 0) (fun _ => 0) 1).eval interpretation (fun _ => false) (Fin.last 0) = false := by
  rw [ScalarStage.eval_append_readout]
  simp

-- Repeated reads with contradictory requested bits must give a false indicator.
example (x : Fin 2 → Bool) (z : Fin 1 → Bool) :
    (ScalarStage.prefixLine (fun _ : Fin 2 => (0 : Fin 1))
      (fun j : Fin 2 => decide (j = 0))).eval interpretation x z = false := by
  rw [ScalarStage.prefixLine_eval]
  cases z 0 <;> simp [funext_iff, Fin.forall_fin_two]

-- Empty prefixes produce the true flag even in dimension zero.
example : (ScalarStage.prefixLine (n := 0) (g := 0)
    (Fin.elim0 : Fin 0 → Fin 0) (fun _ => false)).eval interpretation
      (fun _ => false) (fun _ => false) = true := by
  rw [ScalarStage.prefixLine_eval]
  simp

-- Empty banks still emit a query. A nonzero vector is counted even when padding is false.
private def paddingStage : Program signature 1 1 :=
  ScalarStage.append Program.empty (Fin.elim0 : Fin 0 → Fin 0)
    (Fin.elim0 : Fin 0 → Fin 0 → Bool) (fun _ => 1) Fin.elim0 2

example (x : Fin 1 → Bool) : paddingStage.eval interpretation x 0 = false := by
  change paddingStage.eval interpretation x (Fin.last 0) = _
  rw [paddingStage, ScalarStage.eval_append_last]
  cases hx : x 0 <;> norm_num [hx]

example : (inputGates paddingStage).card = 1 := by
  rw [paddingStage, ScalarStage.card_inputGates_append, empty_readers]
  norm_num [funext_iff]

-- A zero direct vector, in contrast, adds no reader regardless of the helper bank.
example : (inputGates (ScalarStage.append (Program.empty : Program signature 2 0)
    (Fin.elim0 : Fin 0 → Fin 0) (fun (_ : Fin 1) (_ : Fin 0) => false)
      (fun _ => 0) (fun _ => -1) 3)).card = 0 := by
  have hz : (fun _ : Fin 2 => (0 : ℝ)) = 0 := funext (fun _ => rfl)
  refine (ScalarStage.card_inputGates_append (Program.empty : Program signature 2 0)
    (Fin.elim0 : Fin 0 → Fin 0) (fun (_ : Fin 1) (_ : Fin 0) => false)
    (fun _ : Fin 2 => (0 : ℝ)) (fun _ : Fin 1 => (-1 : ℝ)) 3).trans ?_
  rw [empty_readers, ite_eq_left hz]

private noncomputable def fractionalWeight (i : Fin 2) : ℝ :=
  if i = 0 then -1 else 1 / 2

-- A fractional threshold is attained exactly; negative coefficients are allowed.
example : (ScalarStage.append (Program.empty : Program signature 2 0)
    (Fin.elim0 : Fin 0 → Fin 0) (fun (_ : Fin 1) (_ : Fin 0) => false)
      fractionalWeight (fun _ => 1 / 2) 3).eval interpretation
        (fun i => decide (i = 1)) (Fin.last 1) = true := by
  rw [ScalarStage.eval_append_of_match (Program.empty : Program signature 2 0)
    (Fin.elim0 : Fin 0 → Fin 0) (fun (_ : Fin 1) (_ : Fin 0) => false)
    fractionalWeight (fun _ : Fin 1 => (1 / 2 : ℝ)) 3
    (fun i : Fin 2 => decide (i = 1)) (0 : Fin 1)
    (fun _ _ _ => Subsingleton.elim _ _) (Subsingleton.elim _ _)];
    norm_num [fractionalWeight, Fin.sum_univ_two]

-- Without distinct patterns, two matching flags blend their adjustments: score 1 passes
-- although either individual threshold is 2. The selector theorem requires injectivity.
example : (ScalarStage.append (Program.empty : Program signature 1 0)
    (Fin.elim0 : Fin 0 → Fin 0) (fun (_ : Fin 2) (_ : Fin 0) => false)
      (fun _ => 1) (fun _ => 2) 3).eval interpretation
        (fun _ => true) (Fin.last 2) = true := by
  rw [ScalarStage.eval_append_last]; norm_num [Fin.sum_univ_two, funext_iff]
