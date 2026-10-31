/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandCount

/-!
# Native integer square root for the band block size

## Main results

* `BandPreparation.exec_root`: reuse `NatSqrt.exec_rename` and one final multiplication to
  compute the ordinary natural square root and its square within `5 * Nat.sqrt k + 8`
  native instructions.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM

/-- The six-register square-root assignment is injective. -/
theorem rootRegisters_injective : Function.Injective rootRegisters := by decide

private theorem rootRegisters_preserves (i : Fin 96)
    (hr : i ≠ root) (hs : i ≠ square) (ht : i ≠ temporary) (hl : i ≠ limit) (hone : i ≠ one) :
    (NatSqrt.program.rename rootRegisters).Preserves i := by
  simp [NatSqrt.program, NatSqrt.body, Code.rename, Code.Preserves, Op.rename, Op.dest, Op.bin,
    rootRegisters, NatSqrt.arg, NatSqrt.root, NatSqrt.next, NatSqrt.square, NatSqrt.one,
    NatSqrt.bound, Ne.symm hr, Ne.symm hs, Ne.symm ht, Ne.symm hl, Ne.symm hone]

/-- Compute the floor square root and its square by renaming `NatSqrt.program` and charging one
final multiplication. The only intermediate bound is `4*k+4`, which covers `(sqrt k + 1)²`. -/
theorem exec_root {w : ℕ} (k : ℕ) (x : Data 96)
    (hk : x.regs count = k) (ho : x.regs one = 1) (hfit : Fits w (4 * k + 4)) :
    ∃ y, ExecWithin w rootCode x y (5 * Nat.sqrt k + 8) ∧
      y.regs root = Nat.sqrt k ∧ y.regs square = Nat.sqrt k * Nat.sqrt k ∧ y.mem = x.mem ∧
      (∀ i, i ≠ root → i ≠ square → i ≠ temporary → i ≠ limit → y.regs i = x.regs i) := by
  obtain ⟨z, hz, hzroot, _, hzmem, hzone⟩ :=
    NatSqrt.exec_rename rootRegisters rootRegisters_injective x
      (by simpa only [rootRegisters, NatSqrt.arg, Matrix.cons_val_zero, hk] using hfit)
  simp only [rootRegisters, NatSqrt.arg, NatSqrt.root, NatSqrt.one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hz hzroot hzone
  rw [hk] at hz hzroot
  have hfinal_fit : Fits w (z.regs root * z.regs root) := by
    rw [hzroot]
    have hle := Nat.sqrt_le k
    exact hfit.of_le (by omega)
  have hfinal : ExecWithin w (ram[ square ← root * root ]) z
      (z.set square (Nat.sqrt k * Nat.sqrt k)) 1 := by
    have hmul : Fits w (Nat.sqrt k * Nat.sqrt k) := by simpa only [hzroot] using hfinal_fit
    ram_eval [hzroot, hmul]
  have hwhole : ExecWithin w rootCode x (z.set square (Nat.sqrt k * Nat.sqrt k))
      (5 * Nat.sqrt k + 8) :=
    (hz.seq hfinal).mono (by omega)
  refine ⟨z.set square (Nat.sqrt k * Nat.sqrt k), hwhole, ?_, ?_, hzmem, ?_⟩
  · simpa +decide [Data.set, square, root] using hzroot
  · simp [Data.set]
  · intro i hr hs ht hl
    have his : (z.set square (Nat.sqrt k * Nat.sqrt k)).regs i = z.regs i := by
      simp [Data.set, hs]
    rw [his]
    by_cases hone : i = one
    · subst hone; exact hzone.trans ho.symm
    · exact hz.regs_eq (rootRegisters_preserves i hr hs ht hl hone)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
