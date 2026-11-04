/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import Complexity.Computability.WordRAM.Call
public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Properties
public import Complexity.Algorithms.WordRAM.ExactTriangle.DyadicParameters.Exec

/-!
# Actual parameter computation in the assembled solver bank

The existing logarithm/two-power program moves as one bank. Its real executed values supply
all later deliveries and the small/fast dispatch. The original dimension is the only parameter
input; neither geometry nor a precomputed exponent/flag is supplied to this execution rule.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle

/-- Execute all actual parameter instructions above the selector, preserving original arguments. -/
theorem exec_parameters {W n : ℕ} (x : Data 640)
    (hn : x.regs (parameterBank DyadicParameters.Reg.side) = n)
    (hfit : Fits W (DyadicParameters.wordBudget n)) :
    ∃ y, ExecWithin W parameters x y (DyadicParameters.timeBound n) ∧
      y.regs (parameterBank DyadicParameters.Reg.side) = n ∧
      y.regs (parameterBank DyadicParameters.Reg.blocks) = ParameterChoice.blocks n ∧
      y.regs (parameterBank DyadicParameters.Reg.level) = ParameterChoice.level n ∧
      y.regs (parameterBank DyadicParameters.Reg.window) = ParameterChoice.window n ∧
      y.regs (parameterBank DyadicParameters.Reg.groups) = ParameterChoice.groups n ∧
      y.regs (parameterBank DyadicParameters.Reg.tensorDepth) = ParameterChoice.tensorDepth n ∧
      y.regs (parameterBank DyadicParameters.Reg.fast) =
        (if 0 < ParameterChoice.blocks n then 1 else 0) ∧
      y.mem = x.mem ∧
      ∀ j : Fin 640, j.val < 144 ∨ 160 ≤ j.val → y.regs j = x.regs j := by
  obtain ⟨y, hy, ⟨yn, yb, yl, yd, yg, yL, yf, ym⟩, -⟩ :=
    ExecWithin.rename_post parameterBank_injective
      (DyadicParameters.exec (x.comap parameterBank) hn hfit)
  exact ⟨y, hy, yn, yb, yl, yd, yg, yL, yf, ym,
    fun j hj => hy.regs_eq (parameters_preserves j hj)⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
