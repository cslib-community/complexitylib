/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Strassen.Phases
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.CyclicConvolution.Coefficient

/-!
# Original-parameter bounds for native Strassen composition

The magnitude envelope covers native scalar convolution, operand forms, recursive children
and partial output additions. The pointer envelope covers current/descendant frames and
coefficient buffers. These arithmetic lemmas derive intermediate admission facts; they are
not an execution, multiplication or time certificate supplied to the program.

The factor two above the actual scalar-kernel envelope deliberately leaves room to bound
an accumulated quarter and its next child separately. The resulting `16^k` growth is
polynomial in the padded matrix side, as required for later logarithmic-width admission.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

/-- An input-derived envelope for every signed arithmetic operand in a depth-k node. -/
@[expose] def magnitudeBound (p A B k : ℕ) : ℕ :=
  2 * CyclicConvolution.magnitudeBound p A B * 16 ^ k

/-- A uniform address envelope for the current node and all its actual descendant frames.
`frames` is the first stack address; coefficient scratch ends before it. -/
@[expose] def addressBound (frames frame k : ℕ) : ℕ := frames + frame + 7 * (k + 1) + 16

/-- There is always positive signed slack, even for zero original coefficient arrays. -/
theorem magnitudeBound_pos (p A B k : ℕ) : 0 < magnitudeBound p A B k := by
  unfold magnitudeBound CyclicConvolution.magnitudeBound
  positivity

private theorem scalar_bound_left (p A B : ℕ) : A ≤ CyclicConvolution.magnitudeBound p A B := by
  unfold CyclicConvolution.magnitudeBound
  omega

private theorem scalar_bound_right (p A B : ℕ) : B ≤ CyclicConvolution.magnitudeBound p A B := by
  unfold CyclicConvolution.magnitudeBound
  omega

/-- Original coefficient operands fit the node envelope at every depth. -/
theorem inputs_le_magnitudeBound (p A B k : ℕ) :
    A ≤ magnitudeBound p A B k ∧ B ≤ magnitudeBound p A B k := by
  have hp : 1 ≤ 16 ^ k := by
    have h : 0 < 16 ^ k := by positivity
    omega
  have hm := Nat.mul_le_mul_left (2 * CyclicConvolution.magnitudeBound p A B) hp
  simp only [Nat.mul_one] at hm
  exact ⟨(scalar_bound_left p A B).trans (by unfold magnitudeBound; omega),
    (scalar_bound_right p A B).trans (by unfold magnitudeBound; omega)⟩

/-- Both native operand-form sums have enough signed range. -/
theorem forms_le_magnitudeBound (p A B k : ℕ) :
    A + A ≤ magnitudeBound p A B k ∧ B + B ≤ magnitudeBound p A B k := by
  have hp : 1 ≤ 16 ^ k := by
    have h : 0 < 16 ^ k := by positivity
    omega
  have hm := Nat.mul_le_mul_left (2 * CyclicConvolution.magnitudeBound p A B) hp
  simp only [Nat.mul_one] at hm
  have ha := scalar_bound_left p A B
  have hb := scalar_bound_right p A B
  constructor <;> unfold magnitudeBound <;> omega

/-- At scalar leaves the original cyclic kernel admission follows from the node admission. -/
theorem scalar_le_magnitudeBound (p A B : ℕ) :
    CyclicConvolution.magnitudeBound p A B ≤ magnitudeBound p A B 0 := by
  simp only [magnitudeBound, pow_zero, Nat.mul_one]
  omega

/-- Every child's envelope follows from the original parent's, including doubled input forms. -/
theorem child_magnitudeBound_le (p A B k : ℕ) :
    magnitudeBound p (2 * A) (2 * B) k ≤ magnitudeBound p A B (k + 1) := by
  have hscalar : CyclicConvolution.magnitudeBound p (2 * A) (2 * B) ≤
      4 * CyclicConvolution.magnitudeBound p A B := by
    unfold CyclicConvolution.magnitudeBound
    nlinarith [Nat.zero_le ((p + 1) * (A * B))]
  have hm := Nat.mul_le_mul_right (16 ^ k)
    (show 2 * CyclicConvolution.magnitudeBound p (2 * A) (2 * B) ≤
        32 * CyclicConvolution.magnitudeBound p A B from by omega)
  convert hm using 1
  · rfl
  · unfold magnitudeBound
    rw [pow_succ]
    ring

/-- Four previous child contributions and one next contribution fit without relying on
an unproved cancellation or sparsity bound. -/
theorem accumulation_le_magnitudeBound (p A B k : ℕ) :
    5 * (p * ((2 * A) * (2 * B)) * 16 ^ k) ≤ magnitudeBound p A B (k + 1) := by
  have hscalar : p * (A * B) ≤ CyclicConvolution.magnitudeBound p A B := by
    unfold CyclicConvolution.magnitudeBound
    nlinarith [Nat.zero_le (A * B)]
  have hm := Nat.mul_le_mul_right (16 ^ k)
    (show 20 * (p * (A * B)) ≤ 32 * CyclicConvolution.magnitudeBound p A B from by omega)
  convert hm using 1
  · ring
  · unfold magnitudeBound
    rw [pow_succ]
    ring

/-- The actual child-buffer advancement and its child size exactly fill the parent scratch span. -/
theorem child_scratch_end (scratch p k : ℕ) :
    scratch + 3 * (4 ^ k * p) + 4 ^ k * p = scratch + 4 ^ (k + 1) * p := by
  rw [pow_succ]
  ring

/-- An actual seven-word push leaves the numerical descendant address envelope unchanged. -/
theorem addressBound_child (frames frame k : ℕ) :
    addressBound frames (frame + 7) k = addressBound frames frame (k + 1) := by
  unfold addressBound
  ring

end Cslib.Algorithms.WordRAM.Strassen
