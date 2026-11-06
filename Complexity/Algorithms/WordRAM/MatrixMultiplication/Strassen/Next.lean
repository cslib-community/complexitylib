/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Receive
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Prepare

/-!
# Native Strassen transition to the next child

The actual return stage first accumulates the current child's real product, then constructs
both next operands and pushes the complete next frame. Original inputs, earlier frames and
the new partial output survive by composing the real footprints of those operations.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Each of the first six actual return stages advances the output partial sum and computes
the next real recursive child. The seventh child returns through a separate final-pop case. -/
theorem exec_stage_next {w p k A B a b out scratch frames frame : ℕ}
    (phase : Fin 6) (x : Data 64) (u v : ℕ → ℤ)
    (hx : NodeHeader p (k + 1) a b out scratch frames frame x)
    (hc : ChildBuffers p k scratch x)
    (hl : NodeLayout p (k + 1) a b out scratch frames frame)
    (hu : ∀ i < 4 ^ (k + 1) * p, (u i).natAbs ≤ A)
    (hv : ∀ i < 4 ^ (k + 1) * p, (v i).natAbs ≤ B)
    (hleft : ∀ i < 4 ^ (k + 1) * p, x.mem (a + i) = encode (u i))
    (hright : ∀ i < 4 ^ (k + 1) * p, x.mem (b + i) = encode (v i))
    (hout : ∀ s j, j < 4 ^ k * p → x.mem (out + s.val * (4 ^ k * p) + j) = encode
      (Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue p k phase.val u v s j))
    (hprod : ∀ j < 4 ^ k * p, x.mem (scratch + 2 * (4 ^ k * p) + j) = encode
      (Cslib.Algorithms.MatrixMultiplication.Strassen.childProduct
        p k u v ⟨phase.val, by omega⟩ j))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound p A B (k + 1) : ℤ))
    (haddr : Fits (w + 2) (addressBound frames frame (k + 1))) :
    ∃ y, ExecWithin (w + 2) (stage ⟨phase.val + 1, by omega⟩) x y
        (receiveBudget ⟨phase.val, by omega⟩ (4 ^ k * p) + 52 * (4 ^ k * p) + 50) ∧
      NodeReady p k scratch (scratch + 4 ^ k * p) (scratch + 2 * (4 ^ k * p))
        (scratch + 3 * (4 ^ k * p)) frames (frame + 7) y ∧
      (∀ j < 4 ^ k * p, y.mem (scratch + j) = encode
        (Cslib.Algorithms.MatrixMultiplication.Strassen.leftOperand
          p k u ⟨phase.val + 1, by omega⟩ j)) ∧
      (∀ j < 4 ^ k * p, y.mem (scratch + 4 ^ k * p + j) = encode
        (Cslib.Algorithms.MatrixMultiplication.Strassen.rightOperand
          p k v ⟨phase.val + 1, by omega⟩ j)) ∧
      (∀ s j, j < 4 ^ k * p → y.mem (out + s.val * (4 ^ k * p) + j) = encode
        (Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue
          p k (phase.val + 1) u v s j)) ∧
      y.mem (frame + 6) = phase.val + 2 ∧
      ∀ d, (d < out ∨ out + 4 ^ (k + 1) * p ≤ d) →
        (d < scratch ∨ scratch + 2 * (4 ^ k * p) ≤ d) →
        (d < frame + 6 ∨ frame + 14 ≤ d) → y.mem d = x.mem d := by
  let current : Fin 7 := ⟨phase.val, by omega⟩
  let next : Fin 7 := ⟨phase.val + 1, by omega⟩
  have hsize : 4 ^ (k + 1) * p = 4 * (4 ^ k * p) := by rw [pow_succ]; ring
  have ho := hl.output_before
  have hs := hl.scratch_before
  have hf := hl.frames_before
  obtain ⟨s, he, sh, sc, outputValues, productValues, outputFrame⟩ :=
    exec_returnedUpdates current x u v hx hc hl hu hv hout hprod hmag haddr
  obtain ⟨y, hy, ready, leftValues, rightValues, parentPhase, memory⟩ := exec_prepareChild next
    s u v sh sc hl hu hv
    (by
      intro i hi
      rw [outputFrame _ ?_]
      · exact hleft i hi
      · rcases hl.left_disjoint with h | h <;> omega)
    (by
      intro i hi
      rw [outputFrame _ ?_]
      · exact hright i hi
      · rcases hl.right_disjoint with h | h <;> omega)
    hmag haddr
  have hafter : afterReturn current = prepareChild next := by
    fin_cases phase <;> rfl
  have hstage := exec_stage_return current he (hafter.symm ▸ hy)
  refine ⟨y, hstage.mono (by dsimp only [current]; omega), ready,
    leftValues, rightValues, ?_, ?_, ?_⟩
  · intro t j hj
    have ht := Nat.mul_le_mul_right (4 ^ k * p) (Nat.succ_le_of_lt t.isLt)
    rw [Nat.succ_mul] at ht
    rw [hsize] at ho
    rw [memory _ (Or.inl (by omega)) (Or.inl (by omega)), outputValues t j hj]
  · simpa only [next, Nat.add_assoc] using parentPhase
  · intro d hd hds hdf
    exact (memory d hds hdf).trans (outputFrame d hd)

end Cslib.Algorithms.WordRAM.Strassen
