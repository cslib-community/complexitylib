/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Cyclic
import Complexity.Computability.Circuit.Simulation

/-!
# Feedback around a straight-line circuit program

A native program may read external inputs and proposed state values. Connecting the latter
to selected internal gates produces a cyclic circuit without adding or duplicating operations.
The selected gates are its outputs; they may be shared and other gates may be unused.

For monotone interpretations, the cyclic output is the least state satisfying the program's
feedback equations. Thus clients can build one ordinary straight-line update program, prove
its functional behavior, and close the loop using the existing least-fixed-point semantics.
This construction does not assert a finite iteration bound.

## Main definitions

* `Cslib.Circuits.Program.feedback`: connect state inputs to selected internal gates.
* `Cslib.Circuits.Circuit.feedback`: close a native circuit whose outputs are internal gates.

## Main results

* `Cslib.Circuits.Program.cost_feedback`: feedback preserves every operation weight.
* `Cslib.Circuits.Program.eval_feedback_fixed`: the outputs satisfy the update equations.
* `Cslib.Circuits.Program.eval_feedback_le`: leastness among pre-fixed states.
* `Cslib.Circuits.Circuit.eval_feedback_eq_lfp`: a functional update determines the least output.

## References

The construction uses CSLib's native wire mapping and program evaluation and Mathlib's
Knaster–Tarski fixed-point API.
-/

@[expose] public section

namespace Cslib.Circuits.Program

universe u v

variable {σ : Signature.{u}} {U : Type v} {n k g : ℕ}

/-- Replace state inputs by their selected feedback gates, leaving other wires unchanged. -/
def feedbackWire (feed : Fin k → Fin g) : Wire (n + k) g → Wire n g :=
  Wire.elim (Fin.addCases Wire.input (Wire.gate ∘ feed)) Wire.gate

/-- Reading a feedback wire is reading the original wire with the selected gate values as state. -/
private theorem elim_feedbackWire (feed : Fin k → Fin g) (input : Fin n → U) (state : Fin g → U)
    (wire : Wire (n + k) g) :
    Wire.elim input state (feedbackWire feed wire) =
      Wire.elim (Fin.append input (state ∘ feed)) state wire := by
  cases wire with
  | input i =>
    induction i using Fin.addCases <;>
      simp [feedbackWire]
  | gate i => rfl

/-- Close the last inputs of a program through selected gates, retaining all operation costs. -/
def feedback (p : Program σ (n + k) g) (feed : Fin k → Fin g) : CyclicCircuit σ n k where
  lines i := (p.lines i).mapWires (feedbackWire feed)
  outputs := Wire.gate ∘ feed

/-- Feedback does not add, remove or duplicate any weighted gate. -/
@[simp] theorem cost_feedback (p : Program σ (n + k) g) (feed : Fin k → Fin g)
    (weight : σ.Op → ℕ) : (p.feedback feed).cost weight = p.cost weight :=
  (p.cost_eq_sum weight).symm

variable [CompleteLattice U] (p : Program σ (n + k) g) (feed : Fin k → Fin g)
  (I : Interpretation σ U) (hI : ∀ op, Monotone (I op)) (input : Fin n → U)

/-- The solved internal gates are the ordinary evaluation at the solved feedback inputs. -/
theorem evalGates_feedback : (p.feedback feed).evalGates I hI input =
    p.eval I (Fin.append input ((p.feedback feed).eval I hI input)) := by
  apply p.eq_eval_of_forall_lines_eval
  intro i
  have h := (p.feedback feed).evalGates_fixed I hI input i
  change ((p.lines i).mapWires (feedbackWire feed)).eval I input _ = _ at h
  exact ((p.lines i).eval_mapWires (feedbackWire feed) I _ input _ _
    (elim_feedbackWire feed input ((p.feedback feed).evalGates I hI input))).symm.trans h

/-- Feedback outputs satisfy the program's state-update equations. -/
theorem eval_feedback_fixed :
    p.eval I (Fin.append input ((p.feedback feed).eval I hI input)) ∘ feed =
      (p.feedback feed).eval I hI input := by
  rw [← evalGates_feedback]
  rfl

/-- Every pre-fixed state bounds the solved feedback outputs. -/
theorem eval_feedback_le {state : Fin k → U}
    (hstate : p.eval I (Fin.append input state) ∘ feed ≤ state) :
    (p.feedback feed).eval I hI input ≤ state := by
  have hgate : (p.feedback feed).evalGates I hI input ≤
      p.eval I (Fin.append input state) := by
    apply (p.feedback feed).evalGates_le
    intro i
    rw [← p.lines_eval I (Fin.append input state) i]
    apply hI _
    intro a
    change Wire.elim input _ (feedbackWire feed ((p.lines i).wires a)) ≤
      p.trace I (Fin.append input state) ((p.lines i).wires a)
    rw [elim_feedbackWire]
    cases (p.lines i).wires a with
    | input j =>
      induction j using Fin.addCases with
      | left j => simp only [trace, Wire.elim_input, Fin.append_left, le_refl]
      | right j => simpa only [trace, Wire.elim_input, Fin.append_right] using hstate j
    | gate j => exact le_rfl
  exact fun i => (hgate (feed i)).trans (hstate i)

/-- A proved functional update identifies the feedback output with its least fixed point. -/
theorem eval_feedback_eq_lfp (step : (Fin k → U) →o (Fin k → U))
    (hstep : ∀ state, p.eval I (Fin.append input state) ∘ feed = step state) :
    (p.feedback feed).eval I hI input = step.lfp := by
  apply le_antisymm
  · apply p.eval_feedback_le feed I hI input
    rw [hstep, step.map_lfp]
  · apply step.lfp_le
    rw [← hstep, p.eval_feedback_fixed feed I hI input]

end Cslib.Circuits.Program

namespace Cslib.Circuits.Circuit

universe u v

variable {σ : Signature.{u}} {U : Type v} {n k : ℕ}

/-- Extract a circuit's internal output gate, using its structural witness only in proofs. -/
def feedbackGate (c : Circuit σ (n + k) k)
    (h : ∀ i, ∃ j, c.outputs i = .gate j) (i : Fin k) : Fin c.size :=
  match heq : c.outputs i with
  | .gate j => j
  | .input _ => False.elim ((h i).elim fun _ hj => nomatch heq.symm.trans hj)

private theorem outputs_feedbackGate (c : Circuit σ (n + k) k)
    (h : ∀ i, ∃ j, c.outputs i = .gate j) (i : Fin k) :
    c.outputs i = .gate (feedbackGate c h i) := by
  unfold feedbackGate
  split
  · assumption
  · rename_i j hj
    obtain ⟨l, hl⟩ := h i
    rw [hj] at hl
    cases hl

/-- Feed the outputs of a native circuit back into its final input block. Outputs must be
internal gates; this excludes direct aliases between state inputs without an operation. -/
def feedback (c : Circuit σ (n + k) k) (h : ∀ i, ∃ j, c.outputs i = .gate j) :
    CyclicCircuit σ n k := c.program.feedback (feedbackGate c h)

/-- Closing the feedback block leaves every operation cost unchanged. -/
@[simp] theorem cost_feedback (c : Circuit σ (n + k) k)
    (h : ∀ i, ∃ j, c.outputs i = .gate j) (weight : σ.Op → ℕ) :
    (c.feedback h).cost weight = c.program.cost weight :=
  c.program.cost_feedback _ weight

private theorem eval_feedbackGate (c : Circuit σ (n + k) k)
    (h : ∀ i, ∃ j, c.outputs i = .gate j) (I : Interpretation σ U)
    (input : Fin (n + k) → U) :
    c.program.eval I input ∘ feedbackGate c h = c.eval I input := by
  funext i
  change _ = c.program.trace I input (c.outputs i)
  rw [outputs_feedbackGate c h i]
  rfl

variable [CompleteLattice U] (c : Circuit σ (n + k) k)
  (h : ∀ i, ∃ j, c.outputs i = .gate j)
  (I : Interpretation σ U) (hI : ∀ op, Monotone (I op)) (input : Fin n → U)

/-- The feedback outputs satisfy the ordinary circuit's update equations. -/
theorem eval_feedback_fixed :
    c.eval I (Fin.append input ((c.feedback h).eval I hI input)) =
      (c.feedback h).eval I hI input := by
  rw [← eval_feedbackGate c h I]
  exact c.program.eval_feedback_fixed _ I hI input

/-- Every pre-fixed state bounds the circuit's feedback outputs. -/
theorem eval_feedback_le {state : Fin k → U}
    (hstate : c.eval I (Fin.append input state) ≤ state) :
    (c.feedback h).eval I hI input ≤ state :=
  c.program.eval_feedback_le _ I hI input ((eval_feedbackGate c h I _).trans_le hstate)

/-- A functional description of the circuit update identifies its least feedback solution. -/
theorem eval_feedback_eq_lfp (step : (Fin k → U) →o (Fin k → U))
    (hstep : ∀ state, c.eval I (Fin.append input state) = step state) :
    (c.feedback h).eval I hI input = step.lfp :=
  c.program.eval_feedback_eq_lfp _ I hI input step
    (fun state => (eval_feedbackGate c h I _).trans (hstep state))

end Cslib.Circuits.Circuit
