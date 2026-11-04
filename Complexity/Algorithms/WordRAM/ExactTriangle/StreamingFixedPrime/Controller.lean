/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Program
public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.Controller

/-!
# Charged one-slot controller setup and reclamation

The logical limit is read from the producer's total register before any pair is produced.
The slot is reclaimed by one native copy after verification; no memory is cleared.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime

open Cslib.WordRAM
open FixedPrime (recordBank)

-- The finite setup writes only the five existing controller registers.
set_option maxRecDepth 4096 in
private theorem setup_preserves : ∀ i : Fin 416, i.val < 400 → setup.Preserves i := by
  decide

/-- Read the total logical count and charge all five controller initialization instructions. -/
theorem exec_setup {w : ℕ} (x : Data 416) (h1 : Fits w 1) :
    ∃ y, ExecWithin w setup x y 5 ∧ y.mem = x.mem ∧
      y.regs FixedPrime.Reg.index = 0 ∧
      y.regs FixedPrime.Reg.limit = x.regs (producerBank Instances.total) ∧
      y.regs FixedPrime.Reg.found = 0 ∧ y.regs FixedPrime.Reg.scans = 0 ∧
      y.regs FixedPrime.Reg.one = 1 ∧
      ∀ j : Fin 416, j.val < 400 → y.regs j = x.regs j := by
  let M := x.regs (producerBank Instances.total)
  let y := x.set FixedPrime.Reg.index 0 |>.set FixedPrime.Reg.limit M
    |>.set FixedPrime.Reg.found 0 |>.set FixedPrime.Reg.scans 0
    |>.set FixedPrime.Reg.one 1
  have he : ExecWithin w setup x y 5 := by
    ram_eval [setup, y, M, h1, FixedPrime.Reg.index, FixedPrime.Reg.limit,
      FixedPrime.Reg.found, FixedPrime.Reg.scans, FixedPrime.Reg.one, producerBank,
      recordBank, RecordWitness.productBank, RecordProduct.producerBank,
      Instances.total, Fin.castLE]
  refine ⟨y, he, rfl, ?_, ?_, ?_, ?_, ?_, fun j hj =>
    he.regs_eq (setup_preserves j hj)⟩
  all_goals simp +decide [y, M, FixedPrime.Reg.index, FixedPrime.Reg.limit,
    FixedPrime.Reg.found, FixedPrime.Reg.scans, FixedPrime.Reg.one]

/-- Reclaim the slot by an actual charged heap copy, retaining every word and other register. -/
theorem exec_reset {w : ℕ} (x : Data 416) :
    ExecWithin w reset x
      (x.set (producerBank Instances.heap) (x.regs (producerBank Instances.output))) 1 :=
  ExecWithin.copy

end Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime
