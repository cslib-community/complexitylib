/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import Complexity.Computability.WordRAM.Call
public import Complexity.Computability.WordRAM.Power

/-!
# Exponentiation in an embedded native register bank

The existing power program executes on any injectively renamed five-register bank, retaining
its memory frame, input-register readback and every register outside that bank. This avoids
repeating the comap/extend execution bridge for concrete callers with multiple power calls.
-/

public section

namespace Cslib.WordRAM.Power

/-- Execute the real power loop in any injective caller register bank. -/
theorem exec_rename {r w : ℕ} (f : Fin 5 → Fin r) (hf : Function.Injective f)
    (b n : ℕ) (hb : 1 ≤ b) (x : Data r)
    (hx : x.regs (f base) = b) (hn : x.regs (f exponent) = n)
    (hfit : Fits w (b ^ n + n + 2)) :
    ∃ y, ExecWithin w (program.rename f) x y (4 * n + 5) ∧
      y.regs (f value) = b ^ n ∧ y.regs (f counter) = n ∧ y.regs (f one) = 1 ∧
      y.mem = x.mem ∧ y.regs (f base) = b ∧ y.regs (f exponent) = n ∧
      ∀ i, (∀ j, f j ≠ i) → y.regs i = x.regs i := by
  obtain ⟨y, hy, ⟨hv, hc, ho, hm, hb', hn'⟩, hframe⟩ :=
    ExecWithin.rename_post hf (exec b n hb (x.comap f) hx hn hfit)
  exact ⟨y, hy, hv, hc, ho, hm, hb', hn', hframe⟩

end Cslib.WordRAM.Power
