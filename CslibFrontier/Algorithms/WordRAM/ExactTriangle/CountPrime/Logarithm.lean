/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.CanonicalCall
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CountPrime.Program

/-!
# Computed native CountPrime depth

The actual runtime original side is copied into the existing native ceiling-logarithm
routine. Four constants, the call, and copying its result into the counter metadata are
charged. No depth/logarithm certificate or precomputed padding parameter is supplied.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

/-- Compute the real ceiling binary logarithm and establish the four native constants.
All original counter argument registers and memory are preserved. -/
theorem exec_logarithm {w : ℕ} (x : Data 128)
    (hw : Fits w (x.regs Reg.side + Nat.clog 2 (x.regs Reg.side) + 8)) :
    ∃ y, ExecWithin w logarithm x y (5 * Nat.clog 2 (x.regs Reg.side) + 11) ∧
      y.regs Reg.depth = Nat.clog 2 (x.regs Reg.side) ∧
      y.regs Reg.zero = 0 ∧ y.regs Reg.one = 1 ∧ y.regs Reg.two = 2 ∧ y.regs Reg.four = 4 ∧
      y.mem = x.mem ∧
      ∀ i, 4 ≤ i.val → i ≠ Reg.depth → i ≠ Reg.zero → i ≠ Reg.one →
        i ≠ Reg.two → i ≠ Reg.four → y.regs i = x.regs i := by
  unfold logarithm
  have fit (v : ℕ) (hv : v ≤ 8) : Fits w v := hw.of_le (by omega)
  wram_exec [fit]
  wram_call (NatClog.exec _ (hw.of_le (by omega))
    (by wram_simp [NatClog.arg]; exact hw.of_le (by omega))
    (by wram_simp [NatClog.arg]; exact hw.of_le (by omega))) canonical
    (Fin.castLE_injective _) with t ⟨result, memory, _, _⟩
  wram_exec [NatClog.result, result]
  wram_simp [NatClog.arg, memory, result]
  intro i hi hd h0 h1 h2 h4
  rw [Data.set_regs_of_ne hd, Data.extend_castLE_regs_of_le _ _ i hi]
  simp only [Data.set_regs, Function.update_of_ne (show i ≠ Reg.low0 by
    intro h; subst i; contradiction), Function.update_of_ne h0,
    Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h4]

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
