/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding

/-!
# Copying the final encoding to its fixed output block

## Main results

* `Encoding.exec_copyOut`: reuse the native array copy, including equal blocks and both
  possible disjoint address orders, with its charged `7n+4` bound.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding

open Cslib.WordRAM

/-- The final copy uses seven instructions per output word plus four instructions of setup
and loop termination. Equal source/output blocks are permitted, so odd and even depths use
the same fixed program. All other registers retain their values. -/
theorem exec_copyOut {w : ℕ} (x : Data 32) (h1 : Fits w 1)
    (hs : Fits w (x.regs src + x.regs capacity))
    (hd : Fits w (x.regs output + x.regs capacity))
    (hdisj : x.regs src + x.regs capacity ≤ x.regs output ∨
      x.regs output + x.regs capacity ≤ x.regs src ∨ x.regs src = x.regs output) :
    ∃ y, ExecWithin w copyOut x y (7 * x.regs capacity + 4) ∧
      y.mem = ArrayCopy.copyPrefix x.mem (x.regs src) (x.regs output) (x.regs capacity) ∧
      (∀ i, i ≠ cell → i ≠ address → i ≠ accumulator → i ≠ one → y.regs i = x.regs i) := by
  obtain ⟨z, hz, hm, _, _, _⟩ := ArrayCopy.exec_of_separated_or_eq (x.comap copyRegisters)
    h1 hs hd hdisj
  have he := hz.rename copyRegisters_injective
  refine ⟨z.extend copyRegisters x, he, hm, ?_⟩
  intro i hc ha hv ho
  apply he.regs_eq
  have hp : ∀ i : Fin 32, i ≠ cell → i ≠ address → i ≠ accumulator → i ≠ one →
      copyOut.Preserves i := by decide
  exact hp i hc ha hv ho

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding
