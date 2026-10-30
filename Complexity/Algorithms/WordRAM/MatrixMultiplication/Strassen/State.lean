/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Initialize
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Bounds

/-!
# Internal explicit-stack Strassen invariants

The program takes ordinary pointers, depth and coefficient length. These structures describe
its actual intermediate state for the execution induction. They contain no run, result or
time oracle. Root readiness follows from the native setup theorem; child readiness will be
derived from the actual operand writes and frame push. The final caller interface must
compose those derivations from original input data, rather than require these invariants.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM

/-- Numerical separation maintained by the actual Strassen buffers and frame stack. -/
structure NodeLayout (p k a b out scratch frames frame : ℕ) : Prop where
  /-- Scalar cyclic ring length is positive. -/
  modulus_pos : 0 < p
  /-- The complete first input is protected below current scratch. -/
  left_before : a + 4 ^ k * p ≤ scratch
  /-- The complete second input is protected below current scratch. -/
  right_before : b + 4 ^ k * p ≤ scratch
  /-- The output also ends before current scratch. -/
  output_before : out + 4 ^ k * p ≤ scratch
  /-- Recursive coefficient buffers end before the actual stack base. -/
  scratch_before : scratch + 4 ^ k * p ≤ frames
  /-- Older frames precede the current frame. -/
  frames_before : frames ≤ frame
  /-- The output is disjoint from the first input. -/
  left_disjoint : a + 4 ^ k * p ≤ out ∨ out + 4 ^ k * p ≤ a
  /-- The output is disjoint from the second input. -/
  right_disjoint : b + 4 ^ k * p ≤ out ∨ out + 4 ^ k * p ≤ b

/-- Actual current fields and frame words at a newly entered root or pushed child. -/
structure NodeReady (p k a b out scratch frames frame : ℕ) (x : Data 64) : Prop where
  /-- First input pointer. -/
  inputA_eq : x.regs Reg.inputA = a
  /-- Second input pointer. -/
  inputB_eq : x.regs Reg.inputB = b
  /-- Output pointer. -/
  output_eq : x.regs Reg.output = out
  /-- Current scratch pointer. -/
  scratch_eq : x.regs Reg.scratch = scratch
  /-- Actual runtime cyclic length. -/
  modulus_eq : x.regs Reg.modulus = p
  /-- Current depth. -/
  depth_eq : x.regs Reg.depth = k
  /-- Actual computed coefficient-array length. -/
  size_eq : x.regs Reg.size = 4 ^ k * p
  /-- First real frame address. -/
  frames_eq : x.regs Reg.frames = frames
  /-- Current real frame address. -/
  frame_eq : x.regs Reg.frame = frame
  /-- Entry dispatch phase. -/
  phase_eq : x.regs Reg.phase = 0
  /-- Current traversal is active. -/
  active_eq : x.regs Reg.active = 1
  /-- Raw/canonical zero constant. -/
  zero_eq : x.regs Reg.zero = 0
  /-- Counter constant. -/
  one_eq : x.regs Reg.one = 1
  /-- Quadrant radix. -/
  four_eq : x.regs Reg.four = 4
  /-- Real frame width. -/
  frameWidth_eq : x.regs Reg.frameWidth = 7
  /-- Words actually written by native root setup or child push. -/
  frame_words : ∀ j : Fin 7, x.mem (frame + j.val) = x.regs (field j)

/-- Only current output, recursive coefficient scratch and current/descendant frames may
change during this node. Older parent frames are protected. -/
@[expose] def NodeWrites (p k out scratch frames frame a : ℕ) : Prop :=
  (out ≤ a ∧ a < out + 4 ^ k * p) ∨ (scratch ≤ a ∧ a < frames) ∨
    (frame ≤ a ∧ a < frame + 7 * (k + 1))

/-- Semantic/memory result of a node return, independent of an execution or time claim. -/
structure NodeResult (p k out scratch frames frame : ℕ)
    (u v : ℕ → ℤ) (x y : Data 64) : Prop where
  /-- Every actual result coefficient agrees with the existing finite product. -/
  values : ∀ i < 4 ^ k * p, y.mem (out + i) =
    Signed.encode (Cslib.Algorithms.MatrixMultiplication.Strassen.multiply p k u v i)
  /-- Actual preserved caller/parent memory. -/
  outside : ∀ a, ¬NodeWrites p k out scratch frames frame a → y.mem a = x.mem a
  /-- The current output pointer is the returned native address. -/
  output_eq : y.regs Reg.output = out
  /-- The cyclic length is preserved. -/
  modulus_eq : y.regs Reg.modulus = p
  /-- Root stack address is preserved. -/
  frames_eq : y.regs Reg.frames = frames
  /-- The actual return is a parent pop or the unchanged root pointer. -/
  frame_eq : y.regs Reg.frame = if frames < frame then frame - 7 else frame
  /-- Only root return clears the actual traversal flag. -/
  active_eq : y.regs Reg.active = if frames < frame then 1 else 0
  /-- Raw/canonical zero survives all low-bank helper calls. -/
  zero_eq : y.regs Reg.zero = 0
  /-- Counter constant survives. -/
  one_eq : y.regs Reg.one = 1
  /-- Quadrant radix survives. -/
  four_eq : y.regs Reg.four = 4
  /-- Frame width survives. -/
  frameWidth_eq : y.regs Reg.frameWidth = 7

/-- Native proof budget, to be established by controller composition. Defining this function
does not assert an execution or inherit the source Light machine's instruction constants. -/
@[expose] def traceBudget (p : ℕ) : ℕ → ℕ
  | 0 => 42 * p * p + 9 * p + 28
  | k + 1 => 7 * traceBudget p k + 616 * (4 ^ k * p) + 847

/-- The actual native setup constructs root readiness, rather than taking it as a premise. -/
theorem exec_setup_ready {w : ℕ} (x : Data 64)
    (hw : Fits w (x.regs Reg.scratch + x.regs Reg.modulus * 4 ^ x.regs Reg.depth +
      4 ^ x.regs Reg.depth + x.regs Reg.depth + 16)) :
    ∃ y, ExecWithin w setup x y (4 * x.regs Reg.depth + 30) ∧
      NodeReady (x.regs Reg.modulus) (x.regs Reg.depth) (x.regs Reg.inputA)
        (x.regs Reg.inputB) (x.regs Reg.output) (x.regs Reg.scratch)
        (x.regs Reg.scratch + 4 ^ x.regs Reg.depth * x.regs Reg.modulus)
        (x.regs Reg.scratch + 4 ^ x.regs Reg.depth * x.regs Reg.modulus) y ∧
      ∀ a, a < y.regs Reg.frame ∨ y.regs Reg.frame + 7 ≤ a → y.mem a = x.mem a := by
  obtain ⟨y, hy, hsize, hframes, hframe, hphase, hactive, hzero, hone, hfour, hwidth,
    hparams, hfields, hmem⟩ := exec_setup x hw
  have hf : y.regs Reg.frame =
      x.regs Reg.scratch + 4 ^ x.regs Reg.depth * x.regs Reg.modulus := by
    simpa only [Nat.mul_comm] using hframe.trans hframes
  refine ⟨y, hy, ⟨hparams _ (by decide), hparams _ (by decide), hparams _ (by decide),
    hparams _ (by decide), hparams _ (by decide), hparams _ (by decide), ?_, ?_, hf,
    hphase, hactive, hzero, hone, hfour, hwidth, ?_⟩, hmem⟩
  · simpa only [Nat.mul_comm] using hsize
  · simpa only [Nat.mul_comm] using hframes
  · simpa only [hf] using hfields

end Cslib.Algorithms.WordRAM.Strassen
