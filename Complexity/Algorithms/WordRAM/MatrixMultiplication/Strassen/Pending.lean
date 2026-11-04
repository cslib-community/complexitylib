/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Entry
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Restore

/-!
# Actual pending-child invariant for native Strassen

The first child invariant follows from the actual complete positive-depth iteration. Later
children use the same invariant after actual return, accumulation, operand production and
push. It records only mathematical meanings of current memory/registers, not executions,
time bounds or data supplied to the program. The controller induction must derive every
instance from its actual preceding execution.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Current native child and protected parent data, after both form loops and frame push. -/
structure PendingChild (p k a b out scratch frames frame : ℕ) (phase : Fin 7)
    (u v : ℕ → ℤ) (parent child : Data 64) : Prop where
  /-- Entire child frame really exists and is ready for the controller. -/
  ready : NodeReady p k scratch (scratch + 4 ^ k * p) (scratch + 2 * (4 ^ k * p))
    (scratch + 3 * (4 ^ k * p)) frames (frame + 7) child
  /-- Actual first formed operand. -/
  left : ∀ j < 4 ^ k * p, child.mem (scratch + j) = encode
    (Cslib.Algorithms.MatrixMultiplication.Strassen.leftOperand p k u phase j)
  /-- Actual second formed operand. -/
  right : ∀ j < 4 ^ k * p, child.mem (scratch + 4 ^ k * p + j) = encode
    (Cslib.Algorithms.MatrixMultiplication.Strassen.rightOperand p k v phase j)
  /-- Original parent first input remains readable. -/
  original_left : ∀ j < 4 ^ (k + 1) * p, child.mem (a + j) = encode (u j)
  /-- Original parent second input remains readable. -/
  original_right : ∀ j < 4 ^ (k + 1) * p, child.mem (b + j) = encode (v j)
  /-- Earlier returned children have already contributed to the real parent output. -/
  partial_words : ∀ s j, j < 4 ^ k * p → child.mem (out + s.val * (4 ^ k * p) + j) = encode
    (Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue p k phase.val u v s j)
  /-- Parent fields are protected and its phase word was actually updated by the push. -/
  saved : ∀ j : Fin 7, child.mem (frame + j.val) =
    if j.val = 6 then phase.val + 1 else parent.regs (field j)

/-- Every descendant write is within the parent's complete output/scratch/frame footprint. -/
theorem NodeWrites.child_subset {p k a b out scratch frames frame d : ℕ}
    (hl : NodeLayout p (k + 1) a b out scratch frames frame)
    (h : NodeWrites p k (scratch + 2 * (4 ^ k * p)) (scratch + 3 * (4 ^ k * p))
      frames (frame + 7) d) : NodeWrites p (k + 1) out scratch frames frame d := by
  have hs := hl.scratch_before
  have hsize : 4 ^ (k + 1) * p = 4 * (4 ^ k * p) := by rw [pow_succ]; ring
  rw [hsize] at hs
  unfold NodeWrites at h ⊢
  omega

/-- The three concrete stage-write envelopes all lie inside the parent footprint. -/
theorem NodeLayout.outside_stage {p k a b out scratch frames frame d : ℕ}
    (hl : NodeLayout p (k + 1) a b out scratch frames frame)
    (h : ¬NodeWrites p (k + 1) out scratch frames frame d) :
    (d < out ∨ out + 4 ^ (k + 1) * p ≤ d) ∧
      (d < scratch ∨ scratch + 2 * (4 ^ k * p) ≤ d) ∧
      (d < frame + 6 ∨ frame + 14 ≤ d) := by
  have hs := hl.scratch_before
  have hsize : 4 ^ (k + 1) * p = 4 * (4 ^ k * p) := by rw [pow_succ]; ring
  rw [hsize] at hs
  unfold NodeWrites at h
  omega

/-- A completed child preserves the original parent arrays and its earlier partial sum.
Its own returned values are exactly the current finite child product. -/
theorem PendingChild.after_result {p k a b out scratch frames frame : ℕ}
    {phase : Fin 7} {u v : ℕ → ℤ} {parent child returned : Data 64}
    (h : PendingChild p k a b out scratch frames frame phase u v parent child)
    (hl : NodeLayout p (k + 1) a b out scratch frames frame)
    (hr : NodeResult p k (scratch + 2 * (4 ^ k * p)) (scratch + 3 * (4 ^ k * p))
      frames (frame + 7)
      (Cslib.Algorithms.MatrixMultiplication.Strassen.leftOperand p k u phase)
      (Cslib.Algorithms.MatrixMultiplication.Strassen.rightOperand p k v phase) child returned) :
    (∀ j < 4 ^ (k + 1) * p, returned.mem (a + j) = encode (u j)) ∧
      (∀ j < 4 ^ (k + 1) * p, returned.mem (b + j) = encode (v j)) ∧
      (∀ s j, j < 4 ^ k * p → returned.mem (out + s.val * (4 ^ k * p) + j) = encode
        (Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue p k phase.val u v s j)) ∧
      (∀ j < 4 ^ k * p, returned.mem (scratch + 2 * (4 ^ k * p) + j) = encode
        (Cslib.Algorithms.MatrixMultiplication.Strassen.childProduct p k u v phase j)) := by
  have ha := hl.left_before
  have hb := hl.right_before
  have ho := hl.output_before
  have hs := hl.scratch_before
  have hf := hl.frames_before
  have hsize : 4 ^ (k + 1) * p = 4 * (4 ^ k * p) := by rw [pow_succ]; ring
  have hbelow (d : ℕ) (hd : d < scratch) : returned.mem d = child.mem d := by
    apply hr.outside
    unfold NodeWrites
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [hbelow _ (by omega)]
    exact h.original_left j hj
  · intro j hj
    rw [hbelow _ (by omega)]
    exact h.original_right j hj
  · intro t j hj
    have ht := Nat.mul_le_mul_right (4 ^ k * p) (Nat.succ_le_of_lt t.isLt)
    rw [Nat.succ_mul, ← hsize] at ht
    rw [hbelow _ (by omega)]
    exact h.partial_words t j hj
  · exact hr.values

/-- The actual first controller iteration establishes the first pending child from original
parent coefficient arrays and its actual freshly written frame, even with dirty output. -/
theorem exec_first_pending {w p k A B a b out scratch frames frame : ℕ}
    (x : Data 64) (u v : ℕ → ℤ)
    (hx : NodeReady p (k + 1) a b out scratch frames frame x)
    (hl : NodeLayout p (k + 1) a b out scratch frames frame)
    (hu : ∀ i < 4 ^ (k + 1) * p, (u i).natAbs ≤ A)
    (hv : ∀ i < 4 ^ (k + 1) * p, (v i).natAbs ≤ B)
    (hleft : ∀ i < 4 ^ (k + 1) * p, x.mem (a + i) = encode (u i))
    (hright : ∀ i < 4 ^ (k + 1) * p, x.mem (b + i) = encode (v i))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound p A B (k + 1) : ℤ))
    (haddr : Fits (w + 2) (addressBound frames frame (k + 1))) :
    ∃ y, ExecWithin (w + 2) step x y (68 * (4 ^ k * p) + 77) ∧
      PendingChild p k a b out scratch frames frame 0 u v x y ∧
      (∀ d, ¬NodeWrites p (k + 1) out scratch frames frame d → y.mem d = x.mem d) := by
  have ha := hl.left_before
  have hb := hl.right_before
  have ho := hl.output_before
  have hs := hl.scratch_before
  have hf := hl.frames_before
  have hsize : 4 ^ (k + 1) * p = 4 * (4 ^ k * p) := by rw [pow_succ]; ring
  obtain ⟨y, he, ready, leftValues, rightValues, zeros, parentPhase, memory⟩ :=
    exec_step_entry x u v hx hl hu hv hleft hright hmag haddr
  refine ⟨y, he, ⟨ready, leftValues, rightValues, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j hj
    rw [memory _ ?_ (Or.inl (by omega)) (Or.inl (by omega))]
    · exact hleft j hj
    · rcases hl.left_disjoint with h | h <;> omega
  · intro j hj
    rw [memory _ ?_ (Or.inl (by omega)) (Or.inl (by omega))]
    · exact hright j hj
    · rcases hl.right_disjoint with h | h <;> omega
  · intro t j hj
    have ht := Nat.mul_le_mul_right (4 ^ k * p) (Nat.succ_le_of_lt t.isLt)
    rw [Nat.succ_mul] at ht
    rw [Nat.add_assoc, zeros _ (by rw [hsize]; omega)]
    change 0 = encode (Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue p k 0 u v t j)
    rw [Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue_zero]
    rfl
  · intro j
    by_cases heq : j.val = 6
    · have hj : j = 6 := Fin.ext heq
      subst j
      simpa using parentPhase
    · rw [ite_eq_right heq, memory _ (Or.inr (by omega)) (Or.inr (by rw [hsize] at hs; omega))
        (Or.inl (by omega))]
      exact hx.frame_words j
  · intro d hd
    obtain ⟨ho', hs', hf'⟩ := hl.outside_stage hd
    exact memory d ho' hs' hf'

end Cslib.Algorithms.WordRAM.Strassen
